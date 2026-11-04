/-
Copyright (c) 2026 Malhar A. Patel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Malhar A. Patel
-/
import MechInterp.Architecture.Pattern
import MechInterp.Math.Normalizers
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Sigmoid
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Topology.Algebra.Order.Field

/-!
# Softmax, hardmax, and raw weight rules

This file defines the rules that turn a row of attention scores into weights.

## Main definitions

* `softmax s`: softmax over a whole index type, `softmax s i = exp (s i) / ∑ j, exp (s j)`.
* `maskedSoftmax M β s`: masked softmax at inverse temperature `β`,

    `A_ij = exp (β s_ij) / Z_i` if `M` allows `(i, j)`, and `0` otherwise,

  with normalizer `Z_i = maskedDenom M β s i = ∑_{j allowed} exp (β s_ij)`.
* `softmaxRule β hM`: masked softmax packaged as a `PatternRule`. The hypothesis
  `hM : M.WellFormed` certifies `Z_i > 0`, so every row really sums to one. (Lean's division by
  zero returns zero, so without it an empty row would silently produce a row summing to zero.)
* `argSet M s i`: the allowed maximizers of row `i`.
* `hardmax M s`: averaging hard attention, uniform over the allowed maximizers of each row;
  `hardmaxRule hM` is the corresponding pattern rule.
* `linearWeights M`, `sigmoidWeights M β`: raw weight rules for linear and sigmoid attention.

## Main results

* `softmax_pos`, `softmax_sum_one`, `softmax_add_const`: softmax weights are positive, sum to one,
  and ignore a constant shift of the logits.
* `maskedSoftmax_eq_softmax_subtype`: masked softmax is softmax over the allowed sources.
* `softmaxRule_rowShiftInvariant`, `softmaxRule_rowLocal` and the hardmax analogues.
* `maskedSoftmax_mono_logit`: for `β ≥ 0`, raising one allowed logit raises its weight.
* `tendsto_maskedSoftmax_hardmax` (**temperature limit**): masked softmax converges to hardmax as
  `β → ∞`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

namespace MechInterp

open Finset Filter Topology

/-! ### Softmax over a whole index type -/

section Softmax

variable {ι : Type*} [Fintype ι]

/-- The softmax normalizer `∑ i, exp (s i)`. -/
noncomputable def softmaxDenom (s : ι → ℝ) : ℝ := ∑ i, Real.exp (s i)

/-- Softmax weights over a whole index type: `softmax s i = exp (s i) / ∑ j, exp (s j)`. -/
noncomputable def softmax (s : ι → ℝ) : ι → ℝ :=
  fun i => Real.exp (s i) / softmaxDenom s

/-- The softmax normalizer is positive over a nonempty type. -/
theorem softmaxDenom_pos [Nonempty ι] (s : ι → ℝ) : 0 < softmaxDenom s :=
  positiveNormalizer_pos (fun i => Real.exp (s i)) fun _ => Real.exp_pos _

/-- Every softmax weight is positive. -/
theorem softmax_pos [Nonempty ι] (s : ι → ℝ) (i : ι) : 0 < softmax s i :=
  div_pos (Real.exp_pos _) (softmaxDenom_pos s)

/-- Every softmax weight is nonnegative. -/
theorem softmax_nonneg [Nonempty ι] (s : ι → ℝ) (i : ι) : 0 ≤ softmax s i :=
  (softmax_pos s i).le

/-- Softmax weights sum to one. -/
theorem softmax_sum_one [Nonempty ι] (s : ι → ℝ) : ∑ i, softmax s i = 1 := by
  simp only [softmax, softmaxDenom, ← Finset.sum_div]
  exact div_self (softmaxDenom_pos s).ne'

/-- Softmax is invariant under adding the same constant to every logit: the factor `exp c`
cancels between numerator and normalizer. -/
theorem softmax_add_const (s : ι → ℝ) (c : ℝ) : softmax (fun i => s i + c) = softmax s := by
  funext i
  simp only [softmax, softmaxDenom, Real.exp_add, ← Finset.sum_mul]
  exact mul_div_mul_right _ _ (Real.exp_pos c).ne'

end Softmax

/-! ### Masked softmax -/

section MaskedDefs

variable {Pdst Psrc : Type*} [Fintype Psrc] (M : Mask Pdst Psrc)

/-- The masked softmax normalizer of row `i` at inverse temperature `β`:
`Z_i = ∑_{j allowed} exp (β s_ij)`. -/
noncomputable def maskedDenom (β : ℝ) (s : Pdst → Psrc → ℝ) (i : Pdst) : ℝ :=
  ∑ j ∈ M.allowedSet i, Real.exp (β * s i j)

/-- Masked softmax weights at inverse temperature `β`: `exp (β s_ij) / Z_i` on allowed entries and
`0` on disallowed ones. -/
noncomputable def maskedSoftmax (β : ℝ) (s : Pdst → Psrc → ℝ) (i : Pdst) (j : Psrc) : ℝ :=
  if M.allowed i j then Real.exp (β * s i j) / maskedDenom M β s i else 0

end MaskedDefs

section Masked

variable {Pdst Psrc : Type*} [Fintype Psrc] {M : Mask Pdst Psrc}

/-- In a well-formed mask, every row has an allowed source. -/
theorem allowedSet_nonempty (hM : M.WellFormed) (i : Pdst) : (M.allowedSet i).Nonempty := by
  obtain ⟨j, hj⟩ := hM i
  exact ⟨j, (Mask.mem_allowedSet M i j).mpr hj⟩

/-- In a well-formed mask, every masked softmax normalizer is positive. -/
theorem maskedDenom_pos (hM : M.WellFormed) (β : ℝ) (s : Pdst → Psrc → ℝ) (i : Pdst) :
    0 < maskedDenom M β s i :=
  positiveNormalizer_pos_of_nonempty (allowedSet_nonempty hM i) _ fun _ _ => Real.exp_pos _

/-- The masked softmax weight of an allowed entry. -/
theorem maskedSoftmax_of_allowed {β : ℝ} {s : Pdst → Psrc → ℝ} {i : Pdst} {j : Psrc}
    (h : M.allowed i j) :
    maskedSoftmax M β s i j = Real.exp (β * s i j) / maskedDenom M β s i := if_pos h

/-- A disallowed entry has masked softmax weight zero. -/
theorem maskedSoftmax_of_not_allowed {β : ℝ} {s : Pdst → Psrc → ℝ} {i : Pdst} {j : Psrc}
    (h : ¬ M.allowed i j) : maskedSoftmax M β s i j = 0 := if_neg h

/-- In a well-formed mask, every allowed entry has positive masked softmax weight. -/
theorem maskedSoftmax_pos (hM : M.WellFormed) {β : ℝ} {s : Pdst → Psrc → ℝ} {i : Pdst}
    {j : Psrc} (h : M.allowed i j) : 0 < maskedSoftmax M β s i j := by
  rw [maskedSoftmax_of_allowed h]
  exact div_pos (Real.exp_pos _) (maskedDenom_pos hM β s i)

/-- The masked softmax pattern rule at inverse temperature `β`. The well-formedness certificate
`hM` makes every normalizer positive, so the rows sum to one. -/
noncomputable def softmaxRule (β : ℝ) (hM : M.WellFormed) : PatternRule Pdst Psrc M where
  toPattern s :=
    { A := maskedSoftmax M β s
      nonneg := fun i j => by
        unfold maskedSoftmax
        split_ifs
        · exact div_nonneg (Real.exp_pos _).le
            (Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le)
        · exact le_refl 0
      row_sum := fun i => by
        -- The row sum is `Z_i / Z_i`, and `Z_i > 0` because the row has an allowed source.
        have hne : (M.allowedSet i).Nonempty := by
          obtain ⟨j, hj⟩ := hM i
          exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩⟩
        have hpos : 0 < maskedDenom M β s i :=
          positiveNormalizer_pos_of_nonempty hne _ fun _ _ => Real.exp_pos _
        unfold maskedSoftmax
        rw [← Finset.sum_filter, ← Finset.sum_div]
        exact div_self hpos.ne' }
  supported s i j h := by
    change maskedSoftmax M β s i j = 0
    simp [maskedSoftmax, h]

@[simp] theorem softmaxRule_A (β : ℝ) (hM : M.WellFormed) (s : Pdst → Psrc → ℝ) :
    ((softmaxRule β hM).toPattern s).A = maskedSoftmax M β s := rfl

/-- With the full mask and `β = 1`, masked softmax is softmax over the whole source type. -/
theorem maskedSoftmax_full (s : Psrc → ℝ) (i : Pdst) (j : Psrc) :
    maskedSoftmax (Mask.full : Mask Pdst Psrc) 1 (fun _ => s) i j = softmax s j := by
  simp [maskedSoftmax, maskedDenom, Mask.allowedSet, Mask.full, softmax, softmaxDenom]

/-- Masked softmax is softmax over the subtype of allowed sources, applied to the scaled logits
`β s_ik`. -/
theorem maskedSoftmax_eq_softmax_subtype {β : ℝ} {s : Pdst → Psrc → ℝ} {i : Pdst} {j : Psrc}
    (h : M.allowed i j) :
    maskedSoftmax M β s i j = softmax (fun k : {k // M.allowed i k} => β * s i k) ⟨j, h⟩ := by
  rw [maskedSoftmax_of_allowed h, softmax, softmaxDenom, maskedDenom]
  congr 1
  exact Finset.sum_subtype (M.allowedSet i) (fun k => Mask.mem_allowedSet M i k)
    (fun k => Real.exp (β * s i k))

/-- **Row-shift invariance.** Adding a constant `c i` to every score in row `i` leaves masked
softmax unchanged: the factor `exp (β c_i)` cancels. -/
theorem maskedSoftmax_add_row (β : ℝ) (s : Pdst → Psrc → ℝ) (c : Pdst → ℝ) :
    maskedSoftmax M β (fun i j => s i j + c i) = maskedSoftmax M β s := by
  funext i j
  unfold maskedSoftmax maskedDenom
  split_ifs
  · simp only [mul_add, Real.exp_add, ← Finset.sum_mul]
    exact mul_div_mul_right _ _ (Real.exp_pos _).ne'
  · rfl

/-- The softmax rule is row-shift invariant. -/
theorem softmaxRule_rowShiftInvariant (β : ℝ) (hM : M.WellFormed) :
    (softmaxRule β hM).RowShiftInvariant :=
  fun s c => AttnPattern.ext (maskedSoftmax_add_row β s c)

/-- The normalizer of row `i` depends only on the allowed scores of row `i`. -/
theorem maskedDenom_congr {β : ℝ} {s s' : Pdst → Psrc → ℝ} {i : Pdst}
    (h : ∀ j, M.allowed i j → s i j = s' i j) : maskedDenom M β s i = maskedDenom M β s' i :=
  Finset.sum_congr rfl fun j hj => by rw [h j ((Mask.mem_allowedSet M i j).mp hj)]

/-- **Row locality.** Row `i` of masked softmax depends only on the allowed scores of row `i`. -/
theorem maskedSoftmax_congr {β : ℝ} {s s' : Pdst → Psrc → ℝ} {i : Pdst}
    (h : ∀ j, M.allowed i j → s i j = s' i j) (j : Psrc) :
    maskedSoftmax M β s i j = maskedSoftmax M β s' i j := by
  unfold maskedSoftmax
  split_ifs with hj
  · rw [h j hj, maskedDenom_congr h]
  · rfl

/-- The softmax rule is row-local. -/
theorem softmaxRule_rowLocal (β : ℝ) (hM : M.WellFormed) : (softmaxRule β hM).RowLocal :=
  fun _ _ _ h j => maskedSoftmax_congr h j

/-- **Monotonicity in a logit.** For `β ≥ 0`, raising one allowed logit `s_ij` while keeping the
other logits of row `i` fixed raises the weight `A_ij`.

*Proof.* Write `Z_i = e_j + R` with `e_j = exp (β s_ij)` and `R ≥ 0` the sum over the other allowed
sources. Raising `s_ij` raises `e_j` to `e'_j` and leaves `R` fixed, and
`e_j / (e_j + R) ≤ e'_j / (e'_j + R)` is equivalent to `e_j R ≤ e'_j R`. -/
theorem maskedSoftmax_mono_logit {β : ℝ} (hβ : 0 ≤ β)
    {s s' : Pdst → Psrc → ℝ} {i : Pdst} {j : Psrc} (hj : M.allowed i j)
    (hle : s i j ≤ s' i j) (hother : ∀ k, k ≠ j → s i k = s' i k) :
    maskedSoftmax M β s i j ≤ maskedSoftmax M β s' i j := by
  classical
  have hjmem : j ∈ M.allowedSet i := (Mask.mem_allowedSet M i j).mpr hj
  -- The sum `R` over the other allowed sources is the same for `s` and `s'`.
  have hR : ∑ k ∈ (M.allowedSet i).erase j, Real.exp (β * s i k) =
      ∑ k ∈ (M.allowedSet i).erase j, Real.exp (β * s' i k) :=
    Finset.sum_congr rfl fun k hk => by rw [hother k (Finset.ne_of_mem_erase hk)]
  have hZ : ∀ t : Pdst → Psrc → ℝ, maskedDenom M β t i =
      Real.exp (β * t i j) + ∑ k ∈ (M.allowedSet i).erase j, Real.exp (β * t i k) :=
    fun t => (Finset.add_sum_erase _ (fun k => Real.exp (β * t i k)) hjmem).symm
  rw [maskedSoftmax_of_allowed hj, maskedSoftmax_of_allowed hj, hZ s, hZ s', ← hR]
  set R := ∑ k ∈ (M.allowedSet i).erase j, Real.exp (β * s i k)
  have hRnn : 0 ≤ R := Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le
  have he : Real.exp (β * s i j) ≤ Real.exp (β * s' i j) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hle hβ)
  have h1 := Real.exp_pos (β * s i j)
  have h2 := Real.exp_pos (β * s' i j)
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

end Masked

/-! ### Hardmax -/

section HardmaxDefs

variable {Pdst Psrc : Type*} [Fintype Psrc] (M : Mask Pdst Psrc)

/-- The allowed maximizers of row `i`: the allowed sources whose score is at least every other
allowed score. -/
noncomputable def argSet (s : Pdst → Psrc → ℝ) (i : Pdst) : Finset Psrc :=
  univ.filter fun j => M.allowed i j ∧ ∀ j', M.allowed i j' → s i j' ≤ s i j

/-- Hardmax weights (averaging hard attention): `1 / |argSet|` on the allowed maximizers of each
row and `0` elsewhere. -/
noncomputable def hardmax [DecidableEq Psrc] (s : Pdst → Psrc → ℝ) (i : Pdst) (j : Psrc) : ℝ :=
  if j ∈ argSet M s i then 1 / ((argSet M s i).card : ℝ) else 0

end HardmaxDefs

section Hardmax

variable {Pdst Psrc : Type*} [Fintype Psrc] [DecidableEq Psrc] {M : Mask Pdst Psrc}

theorem mem_argSet {s : Pdst → Psrc → ℝ} {i : Pdst} {j : Psrc} :
    j ∈ argSet M s i ↔ M.allowed i j ∧ ∀ j', M.allowed i j' → s i j' ≤ s i j := by
  simp [argSet]

/-- In a well-formed mask the argmax set is nonempty: a nonempty finite row has a maximum. -/
theorem argSet_nonempty (hM : M.WellFormed) (s : Pdst → Psrc → ℝ) (i : Pdst) :
    (argSet M s i).Nonempty := by
  obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image (M.allowedSet i) (s i)
    (allowedSet_nonempty hM i)
  exact ⟨j, mem_argSet.mpr ⟨(Mask.mem_allowedSet M i j).mp hj,
    fun j' hj' => hmax j' ((Mask.mem_allowedSet M i j').mpr hj')⟩⟩

/-- Every maximizer is an allowed source. -/
theorem argSet_subset_allowedSet (s : Pdst → Psrc → ℝ) (i : Pdst) :
    argSet M s i ⊆ M.allowedSet i :=
  fun j hj => (Mask.mem_allowedSet M i j).mpr (mem_argSet.mp hj).1

/-- The hardmax pattern rule. Well-formedness makes every argmax set nonempty, so the rows sum to
one. -/
noncomputable def hardmaxRule (hM : M.WellFormed) : PatternRule Pdst Psrc M where
  toPattern s :=
    { A := hardmax M s
      nonneg := fun i j => by
        unfold hardmax
        split_ifs
        · exact div_nonneg zero_le_one (Nat.cast_nonneg _)
        · exact le_refl 0
      row_sum := fun i => by
        -- The row sum is `|argSet| · (1 / |argSet|)`, and the argmax set is nonempty.
        have hne : (argSet M s i).Nonempty := by
          obtain ⟨j₀, hj₀⟩ := hM i
          have hrow : (M.allowedSet i).Nonempty :=
            ⟨j₀, Finset.mem_filter.mpr ⟨Finset.mem_univ j₀, hj₀⟩⟩
          obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image (M.allowedSet i) (s i) hrow
          refine ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j,
            (Finset.mem_filter.mp hj).2, fun j' hj' => hmax j' ?_⟩⟩
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ j', hj'⟩
        unfold hardmax
        rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter,
          Finset.sum_const, nsmul_eq_mul]
        have : ((argSet M s i).card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hne.card_pos.ne'
        field_simp }
  supported s i j h := by
    change hardmax M s i j = 0
    have : j ∉ argSet M s i := fun hj => h (Finset.mem_filter.mp hj).2.1
    simp [hardmax, this]

@[simp] theorem hardmaxRule_A (hM : M.WellFormed) (s : Pdst → Psrc → ℝ) :
    ((hardmaxRule hM).toPattern s).A = hardmax M s := rfl

/-- Adding a row constant to the scores does not change the maximizers. -/
theorem argSet_add_row (s : Pdst → Psrc → ℝ) (c : Pdst → ℝ) (i : Pdst) :
    argSet M (fun i j => s i j + c i) i = argSet M s i := by
  ext j
  simp only [mem_argSet, add_le_add_iff_right]

/-- Adding a row constant to the scores does not change hardmax. -/
theorem hardmax_add_row (s : Pdst → Psrc → ℝ) (c : Pdst → ℝ) :
    hardmax M (fun i j => s i j + c i) = hardmax M s := by
  funext i j
  simp only [hardmax, argSet_add_row]

/-- The hardmax rule is row-shift invariant. -/
theorem hardmaxRule_rowShiftInvariant (hM : M.WellFormed) : (hardmaxRule hM).RowShiftInvariant :=
  fun s c => AttnPattern.ext (hardmax_add_row s c)

/-- The maximizers of row `i` depend only on the allowed scores of row `i`. -/
theorem argSet_congr {s s' : Pdst → Psrc → ℝ} {i : Pdst}
    (h : ∀ j, M.allowed i j → s i j = s' i j) : argSet M s i = argSet M s' i := by
  ext j
  simp only [mem_argSet]
  constructor
  · rintro ⟨hj, hmax⟩
    exact ⟨hj, fun j' hj' => by rw [← h j' hj', ← h j hj]; exact hmax j' hj'⟩
  · rintro ⟨hj, hmax⟩
    exact ⟨hj, fun j' hj' => by rw [h j' hj', h j hj]; exact hmax j' hj'⟩

/-- The hardmax rule is row-local. -/
theorem hardmaxRule_rowLocal (hM : M.WellFormed) : (hardmaxRule hM).RowLocal :=
  fun _ _ _ h j => by
    change hardmax M _ _ j = hardmax M _ _ j
    simp only [hardmax, argSet_congr h]

/-- **Temperature limit.** For a well-formed mask, masked softmax converges to hardmax as the
inverse temperature `β` tends to infinity.

*Proof.* Let `m` be the largest allowed score of row `i` and divide numerator and normalizer by
`exp (β m)`. Each term `exp (β (s_ik - m))` is `1` when `k` attains the maximum and tends to `0`
when `s_ik < m`. So the numerator tends to `[j ∈ argSet]` and the normalizer to `|argSet| > 0`,
and their ratio tends to the hardmax weight. -/
theorem tendsto_maskedSoftmax_hardmax (hM : M.WellFormed) (s : Pdst → Psrc → ℝ) (i : Pdst)
    (j : Psrc) :
    Tendsto (fun β => maskedSoftmax M β s i j) atTop (𝓝 (hardmax M s i j)) := by
  -- `m` is the maximum allowed score of row `i`, attained at `j₀`.
  obtain ⟨j₀, hj₀⟩ := argSet_nonempty hM s i
  set m := s i j₀ with hm
  have hle : ∀ k, M.allowed i k → s i k ≤ m := (mem_argSet.mp hj₀).2
  have hmem : ∀ k, k ∈ argSet M s i ↔ M.allowed i k ∧ s i k = m := by
    intro k
    rw [mem_argSet]
    constructor
    · rintro ⟨hk, hmax⟩
      exact ⟨hk, le_antisymm (hle k hk) (hmax j₀ (mem_argSet.mp hj₀).1)⟩
    · rintro ⟨hk, heq⟩
      exact ⟨hk, fun j' hj' => heq ▸ hle j' hj'⟩
  -- The rescaled terms `g β k = exp (β (s_ik - m))` and their limits.
  set g : ℝ → Psrc → ℝ := fun β k => Real.exp (β * (s i k - m)) with hg_def
  have hg : ∀ k, M.allowed i k →
      Tendsto (fun β => g β k) atTop (𝓝 (if k ∈ argSet M s i then 1 else 0)) := by
    intro k hk
    by_cases hkm : s i k = m
    · rw [if_pos ((hmem k).mpr ⟨hk, hkm⟩)]
      simp only [hg_def, hkm, sub_self, mul_zero, Real.exp_zero]
      exact tendsto_const_nhds
    · rw [if_neg fun h => hkm ((hmem k).mp h).2]
      have hneg : s i k - m < 0 := sub_neg.mpr (lt_of_le_of_ne (hle k hk) hkm)
      exact Real.tendsto_exp_atBot.comp (tendsto_id.atTop_mul_const_of_neg hneg)
  -- Rewrite masked softmax in terms of `g`.
  have heq : ∀ β, maskedSoftmax M β s i j =
      (if M.allowed i j then g β j else 0) / ∑ k ∈ M.allowedSet i, g β k := by
    intro β
    by_cases hj : M.allowed i j
    · rw [maskedSoftmax_of_allowed hj, if_pos hj, maskedDenom]
      simp only [hg_def, mul_sub, Real.exp_sub, ← Finset.sum_div]
      rw [div_div_div_cancel_right₀ (Real.exp_pos _).ne']
    · rw [maskedSoftmax_of_not_allowed hj, if_neg hj, zero_div]
  -- The normalizer tends to `|argSet|` and the numerator to `[j ∈ argSet]`.
  have hden : Tendsto (fun β => ∑ k ∈ M.allowedSet i, g β k) atTop
      (𝓝 ((argSet M s i).card : ℝ)) := by
    have h := tendsto_finsetSum (M.allowedSet i)
      fun k hk => hg k ((Mask.mem_allowedSet M i k).mp hk)
    rwa [Finset.sum_boole, Finset.filter_mem_eq_inter,
      Finset.inter_eq_right.mpr (argSet_subset_allowedSet s i)] at h
  have hnum : Tendsto (fun β => if M.allowed i j then g β j else 0) atTop
      (𝓝 (if j ∈ argSet M s i then 1 else 0)) := by
    by_cases hj : M.allowed i j
    · simp only [if_pos hj]; exact hg j hj
    · simp only [if_neg hj, if_neg fun h => hj (mem_argSet.mp h).1]
      exact tendsto_const_nhds
  have hcard : ((argSet M s i).card : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (argSet_nonempty hM s i).card_pos.ne'
  have hlim := hnum.div hden hcard
  have hval : hardmax M s i j =
      (if j ∈ argSet M s i then 1 else 0) / ((argSet M s i).card : ℝ) := by
    unfold hardmax
    split_ifs <;> simp
  rw [hval, funext heq]
  exact hlim

end Hardmax

/-! ### Raw weight rules -/

section Weights

variable {Pdst Psrc : Type*} (M : Mask Pdst Psrc)

/-- Linear attention: the masked raw scores are the weights. -/
def linearWeights : WeightRule Pdst Psrc where
  toWeights s i j := if M.allowed i j then s i j else 0

/-- Sigmoid attention at inverse temperature `β`: each allowed entry gets weight
`sigmoid (β s_ij)`, independently of the rest of its row. -/
noncomputable def sigmoidWeights (β : ℝ) : WeightRule Pdst Psrc where
  toWeights s i j := if M.allowed i j then Real.sigmoid (β * s i j) else 0

end Weights

end MechInterp

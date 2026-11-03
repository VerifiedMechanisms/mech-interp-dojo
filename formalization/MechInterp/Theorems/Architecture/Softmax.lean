import MechInterp.Definitions.Architecture.Softmax
import MechInterp.Theorems.Architecture.Mask
import MechInterp.Theorems.Architecture.Pattern
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Order.Filter.AtTopBot.Field

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

/-!
# Softmax and hardmax theorems

* Legacy softmax: positivity, row sums.
* Masked softmax: positivity on allowed entries, agreement with legacy softmax on full masks,
  agreement with softmax on the allowed subtype, row-shift invariance, row locality, and
  monotonicity in a logit.
* Hardmax: row-shift invariance and row locality.
* **Temperature limit**: `softmax_β → hardmax` as `β → ∞`.
-/

namespace MechInterp

open Finset Filter Topology

section Legacy

variable {ι : Type*} [Fintype ι]

theorem softmaxDenom_pos [Nonempty ι] (s : ι → ℝ) : 0 < softmaxDenom s :=
  positiveNormalizer_pos (fun i => Real.exp (s i)) fun _ => Real.exp_pos _

theorem softmax_pos [Nonempty ι] (s : ι → ℝ) (i : ι) : 0 < softmax s i :=
  div_pos (Real.exp_pos _) (softmaxDenom_pos s)

theorem softmax_nonneg [Nonempty ι] (s : ι → ℝ) (i : ι) : 0 ≤ softmax s i :=
  (softmax_pos s i).le

theorem softmax_sum_one [Nonempty ι] (s : ι → ℝ) : ∑ i, softmax s i = 1 := by
  simp only [softmax, softmaxDenom, ← Finset.sum_div]
  exact div_self (softmaxDenom_pos s).ne'

/-- Legacy softmax is invariant under adding a constant to every logit. -/
theorem softmax_add_const (s : ι → ℝ) (c : ℝ) : softmax (fun i => s i + c) = softmax s := by
  funext i
  simp only [softmax, softmaxDenom, Real.exp_add, ← Finset.sum_mul]
  exact mul_div_mul_right _ _ (Real.exp_pos c).ne'

end Legacy

section Masked

variable {Pdst Psrc : Type*} [Fintype Psrc] {M : Mask Pdst Psrc}

theorem allowedSet_nonempty (hM : M.WellFormed) (i : Pdst) : (M.allowedSet i).Nonempty := by
  obtain ⟨j, hj⟩ := hM i
  exact ⟨j, (Mask.mem_allowedSet M i j).mpr hj⟩

theorem maskedDenom_pos (hM : M.WellFormed) (β : ℝ) (s : Pdst → Psrc → ℝ) (i : Pdst) :
    0 < maskedDenom M β s i :=
  positiveNormalizer_pos_of_nonempty (allowedSet_nonempty hM i) _ fun _ _ => Real.exp_pos _

theorem maskedSoftmax_of_allowed {β : ℝ} {s : Pdst → Psrc → ℝ} {i : Pdst} {j : Psrc}
    (h : M.allowed i j) :
    maskedSoftmax M β s i j = Real.exp (β * s i j) / maskedDenom M β s i := if_pos h

theorem maskedSoftmax_of_not_allowed {β : ℝ} {s : Pdst → Psrc → ℝ} {i : Pdst} {j : Psrc}
    (h : ¬ M.allowed i j) : maskedSoftmax M β s i j = 0 := if_neg h

theorem maskedSoftmax_pos (hM : M.WellFormed) {β : ℝ} {s : Pdst → Psrc → ℝ} {i : Pdst}
    {j : Psrc} (h : M.allowed i j) : 0 < maskedSoftmax M β s i j := by
  rw [maskedSoftmax_of_allowed h]
  exact div_pos (Real.exp_pos _) (maskedDenom_pos hM β s i)

@[simp] theorem softmaxRule_A (β : ℝ) (hM : M.WellFormed) (s : Pdst → Psrc → ℝ) :
    ((softmaxRule β hM).toPattern s).A = maskedSoftmax M β s := rfl

@[simp] theorem hardmaxRule_A [DecidableEq Psrc] (hM : M.WellFormed) (s : Pdst → Psrc → ℝ) :
    ((hardmaxRule hM).toPattern s).A = hardmax M s := rfl

/-- On a full mask at temperature one, masked softmax is legacy softmax. -/
theorem maskedSoftmax_full (s : Psrc → ℝ) (i : Pdst) (j : Psrc) :
    maskedSoftmax (Mask.full : Mask Pdst Psrc) 1 (fun _ => s) i j = softmax s j := by
  simp [maskedSoftmax, maskedDenom, Mask.allowedSet, Mask.full, softmax, softmaxDenom]

/-- Masked softmax is softmax over the allowed sources. -/
theorem maskedSoftmax_eq_softmax_subtype {β : ℝ} {s : Pdst → Psrc → ℝ} {i : Pdst} {j : Psrc}
    (h : M.allowed i j) :
    maskedSoftmax M β s i j = softmax (fun k : {k // M.allowed i k} => β * s i k) ⟨j, h⟩ := by
  rw [maskedSoftmax_of_allowed h, softmax, softmaxDenom, maskedDenom]
  congr 1
  exact Finset.sum_subtype (M.allowedSet i) (fun k => Mask.mem_allowedSet M i k)
    (fun k => Real.exp (β * s i k))

/-- Adding a row constant to the scores leaves masked softmax unchanged. -/
theorem maskedSoftmax_add_row (β : ℝ) (s : Pdst → Psrc → ℝ) (c : Pdst → ℝ) :
    maskedSoftmax M β (fun i j => s i j + c i) = maskedSoftmax M β s := by
  funext i j
  unfold maskedSoftmax maskedDenom
  split_ifs
  · simp only [mul_add, Real.exp_add, ← Finset.sum_mul]
    exact mul_div_mul_right _ _ (Real.exp_pos _).ne'
  · rfl

theorem softmaxRule_rowShiftInvariant (β : ℝ) (hM : M.WellFormed) :
    (softmaxRule β hM).RowShiftInvariant :=
  fun s c => AttnPattern.ext (maskedSoftmax_add_row β s c)

theorem maskedDenom_congr {β : ℝ} {s s' : Pdst → Psrc → ℝ} {i : Pdst}
    (h : ∀ j, M.allowed i j → s i j = s' i j) : maskedDenom M β s i = maskedDenom M β s' i :=
  Finset.sum_congr rfl fun j hj => by rw [h j ((Mask.mem_allowedSet M i j).mp hj)]

theorem maskedSoftmax_congr {β : ℝ} {s s' : Pdst → Psrc → ℝ} {i : Pdst}
    (h : ∀ j, M.allowed i j → s i j = s' i j) (j : Psrc) :
    maskedSoftmax M β s i j = maskedSoftmax M β s' i j := by
  unfold maskedSoftmax
  split_ifs with hj
  · rw [h j hj, maskedDenom_congr h]
  · rfl

theorem softmaxRule_rowLocal (β : ℝ) (hM : M.WellFormed) : (softmaxRule β hM).RowLocal :=
  fun _ _ _ h j => maskedSoftmax_congr h j

/-- Raising one allowed logit (and keeping the others) raises its softmax weight. -/
theorem maskedSoftmax_mono_logit {β : ℝ} (hβ : 0 ≤ β)
    {s s' : Pdst → Psrc → ℝ} {i : Pdst} {j : Psrc} (hj : M.allowed i j)
    (hle : s i j ≤ s' i j) (hother : ∀ k, k ≠ j → s i k = s' i k) :
    maskedSoftmax M β s i j ≤ maskedSoftmax M β s' i j := by
  classical
  have hjmem : j ∈ M.allowedSet i := (Mask.mem_allowedSet M i j).mpr hj
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

section Hardmax

variable {Pdst Psrc : Type*} [Fintype Psrc] [DecidableEq Psrc] {M : Mask Pdst Psrc}

theorem mem_argSet {s : Pdst → Psrc → ℝ} {i : Pdst} {j : Psrc} :
    j ∈ argSet M s i ↔ M.allowed i j ∧ ∀ j', M.allowed i j' → s i j' ≤ s i j := by
  simp [argSet]

theorem argSet_nonempty (hM : M.WellFormed) (s : Pdst → Psrc → ℝ) (i : Pdst) :
    (argSet M s i).Nonempty := by
  obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image (M.allowedSet i) (s i)
    (allowedSet_nonempty hM i)
  exact ⟨j, mem_argSet.mpr ⟨(Mask.mem_allowedSet M i j).mp hj,
    fun j' hj' => hmax j' ((Mask.mem_allowedSet M i j').mpr hj')⟩⟩

theorem argSet_subset_allowedSet (s : Pdst → Psrc → ℝ) (i : Pdst) :
    argSet M s i ⊆ M.allowedSet i :=
  fun j hj => (Mask.mem_allowedSet M i j).mpr (mem_argSet.mp hj).1

theorem argSet_add_row (s : Pdst → Psrc → ℝ) (c : Pdst → ℝ) (i : Pdst) :
    argSet M (fun i j => s i j + c i) i = argSet M s i := by
  ext j
  simp only [mem_argSet, add_le_add_iff_right]

theorem hardmax_add_row (s : Pdst → Psrc → ℝ) (c : Pdst → ℝ) :
    hardmax M (fun i j => s i j + c i) = hardmax M s := by
  funext i j
  simp only [hardmax, argSet_add_row]

theorem hardmaxRule_rowShiftInvariant (hM : M.WellFormed) : (hardmaxRule hM).RowShiftInvariant :=
  fun s c => AttnPattern.ext (hardmax_add_row s c)

theorem argSet_congr {s s' : Pdst → Psrc → ℝ} {i : Pdst}
    (h : ∀ j, M.allowed i j → s i j = s' i j) : argSet M s i = argSet M s' i := by
  ext j
  simp only [mem_argSet]
  constructor
  · rintro ⟨hj, hmax⟩
    exact ⟨hj, fun j' hj' => by rw [← h j' hj', ← h j hj]; exact hmax j' hj'⟩
  · rintro ⟨hj, hmax⟩
    exact ⟨hj, fun j' hj' => by rw [h j' hj', h j hj]; exact hmax j' hj'⟩

theorem hardmaxRule_rowLocal (hM : M.WellFormed) : (hardmaxRule hM).RowLocal :=
  fun _ _ _ h j => by
    change hardmax M _ _ j = hardmax M _ _ j
    simp only [hardmax, argSet_congr h]

/-- **Temperature limit.** As the inverse temperature grows, masked softmax converges to
hardmax (uniform attention over the allowed maximizers). -/
theorem tendsto_maskedSoftmax_hardmax (hM : M.WellFormed) (s : Pdst → Psrc → ℝ) (i : Pdst)
    (j : Psrc) :
    Tendsto (fun β => maskedSoftmax M β s i j) atTop (𝓝 (hardmax M s i j)) := by
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
  have heq : ∀ β, maskedSoftmax M β s i j =
      (if M.allowed i j then g β j else 0) / ∑ k ∈ M.allowedSet i, g β k := by
    intro β
    by_cases hj : M.allowed i j
    · rw [maskedSoftmax_of_allowed hj, if_pos hj, maskedDenom]
      simp only [hg_def, mul_sub, Real.exp_sub, ← Finset.sum_div]
      rw [div_div_div_cancel_right₀ (Real.exp_pos _).ne']
    · rw [maskedSoftmax_of_not_allowed hj, if_neg hj, zero_div]
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

end MechInterp

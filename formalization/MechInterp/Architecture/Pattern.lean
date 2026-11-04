/-
Copyright (c) 2026 Malhar A. Patel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Malhar A. Patel
-/
import MechInterp.Architecture.Mask
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Convex.Combination
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp

/-!
# Attention patterns and value mixing

After scoring, an attention head turns each row of scores into weights over source positions and
averages the values with those weights. This file defines the weights and the averaging step.

## Main definitions

* `AttnPattern Pdst Psrc`: a row-stochastic matrix `A` (nonnegative entries, rows summing to one).
  The row sums are a field of the structure, so a pattern cannot be built without proving them.
* `mix A v`: value mixing `(mix A v)_i = ∑ j, A i j • v j`, for arbitrary weights `A`.
* `AttnPattern.SupportedOn A M`: `A` vanishes outside the mask `M`.
* `AttnPattern.comp`, `AttnPattern.point`, `AttnPattern.uniform`: composition (matrix product),
  attending to one chosen source, and uniform attention.
* `PatternRule Pdst Psrc M`: a rule that turns any score matrix into a pattern supported on `M`.
  Softmax and hardmax (`MechInterp.Architecture.Softmax`) are pattern rules.
* `PatternRule.RowShiftInvariant`, `PatternRule.RowLocal`: adding a constant to a row of scores
  does not change the pattern; row `i` of the pattern depends only on the allowed scores of row
  `i`.
* `WeightRule`: a rule producing raw, not necessarily normalized, weights (linear or sigmoid
  attention).

## Main results

* `mix_add`, `mix_smul`, `map_mix`: mixing is linear in the values and commutes with linear maps.
* `mix_const`: a row-stochastic pattern preserves constants.
* `mix_comp`: mixing with a composed pattern is iterated mixing.
* `mix_mem_convexHull`: if `A` is supported on `M`, then `(mix A v)_i` lies in the convex hull
  of the values `v j` that `i` may attend to. An attention head can only average what it sees.
-/

namespace MechInterp

/-! ### Attention patterns -/

/-- A row-stochastic attention pattern: each row is a probability distribution over sources. -/
structure AttnPattern (Pdst Psrc : Type*) [Fintype Psrc] where
  /-- The weight `A i j` that destination `i` puts on source `j`. -/
  A : Pdst → Psrc → ℝ
  /-- Every weight is nonnegative. -/
  nonneg : ∀ i j, 0 ≤ A i j
  /-- Every row sums to one. -/
  row_sum : ∀ i, ∑ j, A i j = 1

/-- Value mixing `(mix A v)_i = ∑ j, A i j • v j`. The weights `A` need not be stochastic. -/
def mix {Pdst Psrc U : Type*} [Fintype Psrc] [AddCommMonoid U] [Module ℝ U]
    (A : Pdst → Psrc → ℝ) (v : Psrc → U) : Pdst → U :=
  fun i => ∑ j, A i j • v j

namespace AttnPattern

variable {Pdst Psrc Pmid : Type*} [Fintype Psrc]

/-- The pattern vanishes outside the mask: `A i j = 0` whenever `j` is not allowed for `i`. -/
def SupportedOn (A : AttnPattern Pdst Psrc) (M : Mask Pdst Psrc) : Prop :=
  ∀ i j, ¬ M.allowed i j → A.A i j = 0

/-- The composition of two patterns, their matrix product `(A B)_ik = ∑ j, A_ij B_jk`. It is
again row-stochastic, and describes two attention steps in a row. -/
def comp [Fintype Pmid] (A : AttnPattern Pdst Pmid) (B : AttnPattern Pmid Psrc) :
    AttnPattern Pdst Psrc where
  A i k := ∑ j, A.A i j * B.A j k
  nonneg i k := Finset.sum_nonneg fun j _ => mul_nonneg (A.nonneg i j) (B.nonneg j k)
  row_sum i := by
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, B.row_sum, mul_one, A.row_sum]

/-- The pattern in which each destination `i` attends only to the source `f i`. -/
def point [DecidableEq Psrc] (f : Pdst → Psrc) : AttnPattern Pdst Psrc where
  A i j := if j = f i then 1 else 0
  nonneg i j := by split_ifs <;> norm_num
  row_sum i := by simp

/-- The uniform pattern, which spreads weight `1 / |Psrc|` over all sources. -/
noncomputable def uniform [Nonempty Psrc] : AttnPattern Pdst Psrc where
  A _ _ := 1 / (Fintype.card Psrc : ℝ)
  nonneg _ _ := div_nonneg zero_le_one (Nat.cast_nonneg _)
  row_sum _ := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have : (Fintype.card Psrc : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    field_simp

/-- Two patterns are equal when their weight matrices are. -/
theorem ext {A B : AttnPattern Pdst Psrc} (h : A.A = B.A) : A = B := by
  cases A; cases B; cases h; rfl

theorem comp_A [Fintype Pmid] (A : AttnPattern Pdst Pmid) (B : AttnPattern Pmid Psrc) (i : Pdst)
    (k : Psrc) : (A.comp B).A i k = ∑ j, A.A i j * B.A j k := rfl

theorem point_A [DecidableEq Psrc] (f : Pdst → Psrc) (i : Pdst) (j : Psrc) :
    (point f).A i j = if j = f i then 1 else 0 := rfl

/-- Every attention weight is at most one, since it is one term of a row summing to one. -/
theorem le_one (A : AttnPattern Pdst Psrc) (i : Pdst) (j : Psrc) : A.A i j ≤ 1 := by
  rw [← A.row_sum i]
  exact Finset.single_le_sum (fun k _ => A.nonneg i k) (Finset.mem_univ j)

end AttnPattern

/-! ### Value mixing -/

section Mix

variable {Pdst Psrc Pmid U W : Type*} [Fintype Psrc] [AddCommGroup U] [Module ℝ U]
  [AddCommGroup W] [Module ℝ W]

theorem mix_apply (A : Pdst → Psrc → ℝ) (v : Psrc → U) (i : Pdst) :
    mix A v i = ∑ j, A i j • v j := rfl

/-- Mixing is additive in the values. -/
theorem mix_add (A : Pdst → Psrc → ℝ) (v v' : Psrc → U) :
    mix A (v + v') = mix A v + mix A v' := by
  funext i
  simp [mix, smul_add, Finset.sum_add_distrib]

/-- Mixing is homogeneous in the values. -/
theorem mix_smul (A : Pdst → Psrc → ℝ) (c : ℝ) (v : Psrc → U) :
    mix A (c • v) = c • mix A v := by
  funext i
  simp [mix, Finset.smul_sum, smul_comm c]

/-- Mixing zero values gives zero. -/
theorem mix_zero (A : Pdst → Psrc → ℝ) : mix A (0 : Psrc → U) = 0 := by
  funext i; simp [mix]

/-- Linear maps commute with mixing: `L (∑ j, A i j • v j) = ∑ j, A i j • L (v j)`. -/
theorem map_mix (L : U →ₗ[ℝ] W) (A : Pdst → Psrc → ℝ) (v : Psrc → U) (i : Pdst) :
    L (mix A v i) = mix A (fun j => L (v j)) i := by
  simp [mix, map_sum]

/-- Mixing a constant with a row-stochastic pattern returns that constant. -/
theorem mix_const (A : AttnPattern Pdst Psrc) (c : U) (i : Pdst) :
    mix A.A (fun _ => c) i = c := by
  rw [mix, ← Finset.sum_smul, A.row_sum, one_smul]

/-- Mixing with a composed pattern is iterated mixing:
`mix (A.comp B) v = mix A (mix B v)`. -/
theorem mix_comp [Fintype Pmid] (A : AttnPattern Pdst Pmid) (B : AttnPattern Pmid Psrc)
    (v : Psrc → U) : mix (A.comp B).A v = mix A.A (mix B.A v) := by
  funext i
  simp only [mix, AttnPattern.comp_A, Finset.sum_smul, Finset.smul_sum, smul_smul]
  exact Finset.sum_comm

/-- **Convex-hull bound.** If `A` is supported on `M`, the mixed value at `i` is a convex
combination of the values `v j` that `i` may attend to: the disallowed terms vanish and the
allowed weights are nonnegative and sum to one. -/
theorem mix_mem_convexHull (A : AttnPattern Pdst Psrc) {M : Mask Pdst Psrc}
    (hA : A.SupportedOn M) (v : Psrc → U) (i : Pdst) :
    mix A.A v i ∈ convexHull ℝ (v '' {j | M.allowed i j}) := by
  -- Restrict the sum to the allowed sources.
  have hsum : ∀ (f : Psrc → U), ∑ j, A.A i j • f j = ∑ j ∈ M.allowedSet i, A.A i j • f j :=
    fun f => (Finset.sum_subset (Finset.subset_univ _) fun j _ hj => by
      rw [hA i j (by simpa [Mask.allowedSet] using hj), zero_smul]).symm
  -- The allowed weights still sum to one.
  have hw : ∑ j ∈ M.allowedSet i, A.A i j = 1 := by
    rw [← A.row_sum i]
    exact Finset.sum_subset (Finset.subset_univ _) fun j _ hj => hA i j
      (by simpa [Mask.allowedSet] using hj)
  rw [mix, hsum]
  exact (convex_convexHull ℝ _).sum_mem (fun j _ => A.nonneg i j) hw fun j hj =>
    subset_convexHull ℝ _ ⟨j, by simpa [Mask.allowedSet] using hj, rfl⟩

/-- Without a mask: the mixed value lies in the convex hull of all the values. -/
theorem mix_mem_convexHull_range (A : AttnPattern Pdst Psrc) (v : Psrc → U) (i : Pdst) :
    mix A.A v i ∈ convexHull ℝ (Set.range v) :=
  (convex_convexHull ℝ _).sum_mem (fun j _ => A.nonneg i j) (A.row_sum i) fun j _ =>
    subset_convexHull ℝ _ ⟨j, rfl⟩

end Mix

/-! ### Pattern rules and weight rules -/

/-- A pattern rule for the mask `M`: it turns any score matrix into an attention pattern
supported on `M`. -/
structure PatternRule (Pdst Psrc : Type*) [Fintype Psrc] (M : Mask Pdst Psrc) where
  /-- The pattern produced from a score matrix. -/
  toPattern : (Pdst → Psrc → ℝ) → AttnPattern Pdst Psrc
  /-- The pattern never puts weight on a disallowed source. -/
  supported : ∀ s, (toPattern s).SupportedOn M

namespace PatternRule

variable {Pdst Psrc : Type*} [Fintype Psrc] {M : Mask Pdst Psrc}

/-- A rule is **row-shift invariant** when adding a constant `c i` to every score in row `i`
leaves the pattern unchanged. Softmax and hardmax have this property. -/
def RowShiftInvariant (ρ : PatternRule Pdst Psrc M) : Prop :=
  ∀ s (c : Pdst → ℝ), ρ.toPattern (fun i j => s i j + c i) = ρ.toPattern s

/-- A rule is **row-local** when row `i` of the pattern depends only on the scores `s i j` of the
sources `j` that `i` may attend to. -/
def RowLocal (ρ : PatternRule Pdst Psrc M) : Prop :=
  ∀ s s' i, (∀ j, M.allowed i j → s i j = s' i j) →
    ∀ j, (ρ.toPattern s).A i j = (ρ.toPattern s').A i j

end PatternRule

/-- A weight rule produces raw attention weights from scores, without requiring rows to sum to
one (as in linear or sigmoid attention). -/
structure WeightRule (Pdst Psrc : Type*) where
  /-- The weights produced from a score matrix. -/
  toWeights : (Pdst → Psrc → ℝ) → Pdst → Psrc → ℝ

end MechInterp

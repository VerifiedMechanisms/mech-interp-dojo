import MechInterp.Definitions.Architecture.Pattern
import Mathlib.Analysis.Convex.Combination

set_option linter.style.header false

/-!
# Attention-pattern identities

* Extensionality of patterns.
* `mix` is linear in the values, commutes with linear maps, and preserves constants.
* Mixing with a pattern supported on a mask lies in the convex hull of the allowed values.
* Pattern composition corresponds to iterated mixing.
-/

namespace MechInterp

namespace AttnPattern

variable {Pdst Psrc Pmid U : Type*} [Fintype Psrc]

theorem ext {A B : AttnPattern Pdst Psrc} (h : A.A = B.A) : A = B := by
  cases A; cases B; cases h; rfl

theorem comp_A [Fintype Pmid] (A : AttnPattern Pdst Pmid) (B : AttnPattern Pmid Psrc) (i : Pdst)
    (k : Psrc) : (A.comp B).A i k = ∑ j, A.A i j * B.A j k := rfl

theorem point_A [DecidableEq Psrc] (f : Pdst → Psrc) (i : Pdst) (j : Psrc) :
    (point f).A i j = if j = f i then 1 else 0 := rfl

theorem le_one (A : AttnPattern Pdst Psrc) (i : Pdst) (j : Psrc) : A.A i j ≤ 1 := by
  rw [← A.row_sum i]
  exact Finset.single_le_sum (fun k _ => A.nonneg i k) (Finset.mem_univ j)

end AttnPattern

section Mix

variable {Pdst Psrc Pmid U W : Type*} [Fintype Psrc] [AddCommGroup U] [Module ℝ U]
  [AddCommGroup W] [Module ℝ W]

theorem mix_apply (A : Pdst → Psrc → ℝ) (v : Psrc → U) (i : Pdst) :
    mix A v i = ∑ j, A i j • v j := rfl

theorem mix_add (A : Pdst → Psrc → ℝ) (v v' : Psrc → U) :
    mix A (v + v') = mix A v + mix A v' := by
  funext i
  simp [mix, smul_add, Finset.sum_add_distrib]

theorem mix_smul (A : Pdst → Psrc → ℝ) (c : ℝ) (v : Psrc → U) :
    mix A (c • v) = c • mix A v := by
  funext i
  simp [mix, Finset.smul_sum, smul_comm c]

theorem mix_zero (A : Pdst → Psrc → ℝ) : mix A (0 : Psrc → U) = 0 := by
  funext i; simp [mix]

/-- Linear maps commute with mixing. -/
theorem map_mix (L : U →ₗ[ℝ] W) (A : Pdst → Psrc → ℝ) (v : Psrc → U) (i : Pdst) :
    L (mix A v i) = mix A (fun j => L (v j)) i := by
  simp [mix, map_sum]

/-- Mixing a constant with a row-stochastic pattern returns the constant. -/
theorem mix_const (A : AttnPattern Pdst Psrc) (c : U) (i : Pdst) :
    mix A.A (fun _ => c) i = c := by
  rw [mix, ← Finset.sum_smul, A.row_sum, one_smul]

/-- Mixing with a composed pattern is iterated mixing. -/
theorem mix_comp [Fintype Pmid] (A : AttnPattern Pdst Pmid) (B : AttnPattern Pmid Psrc)
    (v : Psrc → U) : mix (A.comp B).A v = mix A.A (mix B.A v) := by
  funext i
  simp only [mix, AttnPattern.comp_A, Finset.sum_smul, Finset.smul_sum, smul_smul]
  exact Finset.sum_comm

/-- Mixing with a pattern supported on `M` lies in the convex hull of the allowed values. -/
theorem mix_mem_convexHull (A : AttnPattern Pdst Psrc) {M : Mask Pdst Psrc}
    (hA : A.SupportedOn M) (v : Psrc → U) (i : Pdst) :
    mix A.A v i ∈ convexHull ℝ (v '' {j | M.allowed i j}) := by
  have hsum : ∀ (f : Psrc → U), ∑ j, A.A i j • f j = ∑ j ∈ M.allowedSet i, A.A i j • f j :=
    fun f => (Finset.sum_subset (Finset.subset_univ _) fun j _ hj => by
      rw [hA i j (by simpa [Mask.allowedSet] using hj), zero_smul]).symm
  have hw : ∑ j ∈ M.allowedSet i, A.A i j = 1 := by
    rw [← A.row_sum i]
    exact Finset.sum_subset (Finset.subset_univ _) fun j _ hj => hA i j
      (by simpa [Mask.allowedSet] using hj)
  rw [mix, hsum]
  exact (convex_convexHull ℝ _).sum_mem (fun j _ => A.nonneg i j) hw fun j hj =>
    subset_convexHull ℝ _ ⟨j, by simpa [Mask.allowedSet] using hj, rfl⟩

/-- Mixing with a pattern lies in the convex hull of all values. -/
theorem mix_mem_convexHull_range (A : AttnPattern Pdst Psrc) (v : Psrc → U) (i : Pdst) :
    mix A.A v i ∈ convexHull ℝ (Set.range v) :=
  (convex_convexHull ℝ _).sum_mem (fun j _ => A.nonneg i j) (A.row_sum i) fun j _ =>
    subset_convexHull ℝ _ ⟨j, rfl⟩

end Mix

end MechInterp

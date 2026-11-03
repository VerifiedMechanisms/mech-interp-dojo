import Mathlib.Analysis.Convex.Segment
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Module.FiniteDimension
import MechInterp.Definitions.Math.ConvexSeparation

set_option linter.style.header false

/-!
# Convex separation

* `segment_cross_not_separable`: two crossing segments cannot be separated by a linear
  threshold (weak on one side, strict on the other).
* `linThresholdSeparable_iff_disjoint_convexHull`: finite sets are linear-threshold
  separable exactly when their convex hulls are disjoint.
-/

namespace MechInterp

open scoped InnerProductSpace

/-- A convex combination of two reals, both at most `τ`, is at most `τ`. -/
theorem convex_combo_le {a b τ x y : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (hx : x ≤ τ) (hy : y ≤ τ) : a * x + b * y ≤ τ := by
  have hτ : a * τ + b * τ = τ := by rw [← add_mul, hab, one_mul]
  nlinarith [mul_le_mul_of_nonneg_left hx ha, mul_le_mul_of_nonneg_left hy hb]

/-- A convex combination of two reals, both strictly above `τ`, is strictly above `τ`. -/
theorem lt_convex_combo {a b τ x y : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (hx : τ < x) (hy : τ < y) : τ < a * x + b * y := by
  rcases eq_or_lt_of_le ha with h | h
  · subst h; simp only [zero_add] at hab; subst hab; linarith
  · have hτ : a * τ + b * τ = τ := by rw [← add_mul, hab, one_mul]
    nlinarith [mul_lt_mul_of_pos_left hx h, mul_le_mul_of_nonneg_left hy.le hb]

/-- **Segment-crossing obstruction.** If a point lies on both segments `[p, q]` and
`[r, s]`, no linear functional places `p, q` weakly below `τ` and `r, s` strictly above. -/
theorem segment_cross_not_separable
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    {p q r s : V} (L : V →ₗ[ℝ] ℝ) {τ : ℝ}
    (hp : L p ≤ τ) (hq : L q ≤ τ) (hr : τ < L r) (hs : τ < L s)
    {P : V} (hPpq : P ∈ segment ℝ p q) (hPrs : P ∈ segment ℝ r s) : False := by
  obtain ⟨a, b, ha, hb, hab, hP1⟩ := hPpq
  obtain ⟨c, e, hc, he, hce, hP2⟩ := hPrs
  have hLP_le : L P ≤ τ := by
    rw [← hP1, map_add, L.map_smul, L.map_smul, smul_eq_mul, smul_eq_mul]
    exact convex_combo_le ha hb hab hp hq
  have hLP_gt : τ < L P := by
    rw [← hP2, map_add, L.map_smul, L.map_smul, smul_eq_mul, smul_eq_mul]
    exact lt_convex_combo hc he hce hr hs
  exact not_le.mpr hLP_gt hLP_le

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Separation of the generating sets extends to their convex hulls. -/
theorem LinThresholdSeparable.hulls {Spos Sneg : Set V}
    (h : LinThresholdSeparable Spos Sneg) :
    LinThresholdSeparable (convexHull ℝ Spos) (convexHull ℝ Sneg) := by
  obtain ⟨w, τ, hpos, hneg⟩ := h
  refine ⟨w, τ, ?_, ?_⟩
  · have hconv : Convex ℝ {x : V | τ < ⟪w, x⟫_ℝ} :=
      convex_halfSpace_gt (innerₛₗ ℝ w).isLinear τ
    exact fun x hx => convexHull_min (fun s hs => hpos s hs) hconv hx
  · have hconv : Convex ℝ {x : V | ⟪w, x⟫_ℝ ≤ τ} :=
      convex_halfSpace_le (innerₛₗ ℝ w).isLinear τ
    exact fun x hx => convexHull_min (fun s hs => hneg s hs) hconv hx

/-- Separable sets have disjoint convex hulls. -/
theorem LinThresholdSeparable.disjoint_convexHull {Spos Sneg : Set V}
    (h : LinThresholdSeparable Spos Sneg) :
    Disjoint (convexHull ℝ Spos) (convexHull ℝ Sneg) := by
  obtain ⟨w, τ, hpos, hneg⟩ := h.hulls
  rw [Set.disjoint_left]
  intro x hxp hxn
  exact absurd (hpos x hxp) (not_lt.mpr (hneg x hxn))

/-- **Finite linear-threshold separability.** Finite sets in a finite-dimensional real
inner product space are separable by a linear threshold exactly when their convex hulls
are disjoint. -/
theorem linThresholdSeparable_iff_disjoint_convexHull [FiniteDimensional ℝ V]
    {Spos Sneg : Set V} (hpos : Spos.Finite) (hneg : Sneg.Finite) :
    LinThresholdSeparable Spos Sneg ↔ Disjoint (convexHull ℝ Spos) (convexHull ℝ Sneg) := by
  refine ⟨LinThresholdSeparable.disjoint_convexHull, fun hdisj => ?_⟩
  obtain ⟨f, u, v, hfu, huv, hvf⟩ :=
    geometric_hahn_banach_compact_closed (convex_convexHull ℝ Sneg)
      (hneg.isCompact_convexHull (𝕜 := ℝ)) (convex_convexHull ℝ Spos)
      ((hpos.isCompact_convexHull (𝕜 := ℝ)).isClosed) hdisj.symm
  refine ⟨(InnerProductSpace.toDual ℝ V).symm f, u, fun s hs => ?_, fun s hs => ?_⟩
  · rw [InnerProductSpace.toDual_symm_apply]
    exact huv.trans (hvf s (subset_convexHull ℝ Spos hs))
  · rw [InnerProductSpace.toDual_symm_apply]
    exact (hfu s (subset_convexHull ℝ Sneg hs)).le

end MechInterp

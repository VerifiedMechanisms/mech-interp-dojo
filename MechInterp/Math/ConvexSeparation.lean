/-
Copyright (c) 2026 Malhar A. Patel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Malhar A. Patel
-/
import Mathlib.Analysis.Convex.Segment
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Linear-threshold separability and convex hulls

A linear-threshold classifier on a real inner product space `V` labels a point `s` positive when
its score `⟪w, s⟫` is strictly above a threshold `τ`, and negative otherwise. This file asks when
two sets of points can be labelled correctly by one such classifier.

## Main definitions

* `LinThresholdSeparable Spos Sneg`: some `w` and `τ` put every point of `Spos` strictly above
  `τ` and every point of `Sneg` at or below `τ`.

## Main results

* `segment_cross_not_separable`: if the segments `[p, q]` and `[r, s]` share a point, no linear
  functional puts `p, q` weakly below a threshold and `r, s` strictly above it. This is the
  geometric reason a single attention head cannot compute XOR.
* `LinThresholdSeparable.disjoint_convexHull`: separable sets have disjoint convex hulls.
* `linThresholdSeparable_iff_disjoint_convexHull`: for *finite* sets in a finite-dimensional
  space the converse also holds (by the Hahn–Banach separation theorem).

## Conventions

The inequality is strict on the positive side and weak on the negative side. A score of exactly
`τ` is therefore classified as negative, matching the convention `f x = true ↔ 0 < S x` used for
Boolean classifiers elsewhere in the project.
-/

namespace MechInterp

open scoped InnerProductSpace

/-! ### Convex combinations of reals -/

/-- If two reals are at most `τ`, so is any convex combination of them. -/
theorem convex_combo_le {a b τ x y : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (hx : x ≤ τ) (hy : y ≤ τ) : a * x + b * y ≤ τ := by
  -- `τ` is itself the convex combination `a * τ + b * τ`; compare termwise.
  have hτ : a * τ + b * τ = τ := by rw [← add_mul, hab, one_mul]
  nlinarith [mul_le_mul_of_nonneg_left hx ha, mul_le_mul_of_nonneg_left hy hb]

/-- If two reals are strictly above `τ`, so is any convex combination of them. -/
theorem lt_convex_combo {a b τ x y : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (hx : τ < x) (hy : τ < y) : τ < a * x + b * y := by
  rcases eq_or_lt_of_le ha with h | h
  · -- `a = 0`, so `b = 1` and the combination is just `y`.
    subst h; simp only [zero_add] at hab; subst hab; linarith
  · -- `a > 0`, so the `x` term contributes a strict increase over `a * τ`.
    have hτ : a * τ + b * τ = τ := by rw [← add_mul, hab, one_mul]
    nlinarith [mul_lt_mul_of_pos_left hx h, mul_le_mul_of_nonneg_left hy.le hb]

/-! ### The segment-crossing obstruction -/

/-- **Segment-crossing obstruction.** Let `L` be a linear functional with `L p, L q ≤ τ` and
`τ < L r, L s`. Then the segments `[p, q]` and `[r, s]` cannot share a point `P`: as a point of
`[p, q]` it would satisfy `L P ≤ τ`, and as a point of `[r, s]` it would satisfy `τ < L P`. -/
theorem segment_cross_not_separable
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    {p q r s : V} (L : V →ₗ[ℝ] ℝ) {τ : ℝ}
    (hp : L p ≤ τ) (hq : L q ≤ τ) (hr : τ < L r) (hs : τ < L s)
    {P : V} (hPpq : P ∈ segment ℝ p q) (hPrs : P ∈ segment ℝ r s) : False := by
  -- Write `P` as a convex combination of each pair of endpoints.
  obtain ⟨a, b, ha, hb, hab, hP1⟩ := hPpq
  obtain ⟨c, e, hc, he, hce, hP2⟩ := hPrs
  -- `L` is linear, so `L P` is the matching convex combination of the endpoint scores.
  have hLP_le : L P ≤ τ := by
    rw [← hP1, map_add, L.map_smul, L.map_smul, smul_eq_mul, smul_eq_mul]
    exact convex_combo_le ha hb hab hp hq
  have hLP_gt : τ < L P := by
    rw [← hP2, map_add, L.map_smul, L.map_smul, smul_eq_mul, smul_eq_mul]
    exact lt_convex_combo hc he hce hr hs
  exact not_le.mpr hLP_gt hLP_le

/-! ### Linear-threshold separability -/

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- `Spos` and `Sneg` are **linear-threshold separable** when some weight vector `w` and threshold
`τ` give every point of `Spos` a score `⟪w, s⟫` strictly above `τ` and every point of `Sneg` a
score at most `τ`. -/
def LinThresholdSeparable (Spos Sneg : Set V) : Prop :=
  ∃ (w : V) (τ : ℝ), (∀ s ∈ Spos, τ < ⟪w, s⟫_ℝ) ∧ (∀ s ∈ Sneg, ⟪w, s⟫_ℝ ≤ τ)

/-- A classifier that separates two sets also separates their convex hulls, because each of the
half-spaces `{x | τ < ⟪w, x⟫}` and `{x | ⟪w, x⟫ ≤ τ}` is convex. -/
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

/-- Linear-threshold separable sets have disjoint convex hulls: a common point of the hulls would
have to score both above and at most `τ`. -/
theorem LinThresholdSeparable.disjoint_convexHull {Spos Sneg : Set V}
    (h : LinThresholdSeparable Spos Sneg) :
    Disjoint (convexHull ℝ Spos) (convexHull ℝ Sneg) := by
  obtain ⟨w, τ, hpos, hneg⟩ := h.hulls
  rw [Set.disjoint_left]
  intro x hxp hxn
  exact absurd (hpos x hxp) (not_lt.mpr (hneg x hxn))

/-- **Finite linear-threshold separability.** In a finite-dimensional real inner product space,
two finite sets are linear-threshold separable if and only if their convex hulls are disjoint.

The hard direction uses Mathlib's geometric Hahn–Banach theorem: the hull of `Sneg` is compact
and the hull of `Spos` is closed, so a continuous functional strictly separates them; the Riesz
representation `InnerProductSpace.toDual` turns that functional into a weight vector `w`. -/
theorem linThresholdSeparable_iff_disjoint_convexHull [FiniteDimensional ℝ V]
    {Spos Sneg : Set V} (hpos : Spos.Finite) (hneg : Sneg.Finite) :
    LinThresholdSeparable Spos Sneg ↔ Disjoint (convexHull ℝ Spos) (convexHull ℝ Sneg) := by
  refine ⟨LinThresholdSeparable.disjoint_convexHull, fun hdisj => ?_⟩
  -- Hahn–Banach: `f < u` on `hull Sneg` and `v < f` on `hull Spos`, with `u < v`.
  obtain ⟨f, u, v, hfu, huv, hvf⟩ :=
    geometric_hahn_banach_compact_closed (convex_convexHull ℝ Sneg)
      (hneg.isCompact_convexHull (𝕜 := ℝ)) (convex_convexHull ℝ Spos)
      ((hpos.isCompact_convexHull (𝕜 := ℝ)).isClosed) hdisj.symm
  -- Represent `f` as `⟪w, ·⟫` and use `τ = u`.
  refine ⟨(InnerProductSpace.toDual ℝ V).symm f, u, fun s hs => ?_, fun s hs => ?_⟩
  · rw [InnerProductSpace.toDual_symm_apply]
    exact huv.trans (hvf s (subset_convexHull ℝ Spos hs))
  · rw [InnerProductSpace.toDual_symm_apply]
    exact (hfu s (subset_convexHull ℝ Sneg hs)).le

end MechInterp

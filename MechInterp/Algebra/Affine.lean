/-
Copyright (c) 2026 Malhar A. Patel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Malhar A. Patel
-/
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineMap

/-!
# Affine maps and biases

The learned projections of a real transformer have biases, so they are affine maps
`f x = L x + b` rather than linear maps. This file uses Mathlib's affine maps `V →ᵃ[ℝ] W`, whose
linear part is `f.linear`, and names the pieces interpretability arguments refer to.

## Main definitions

* `affineOf L b`: the affine map `x ↦ L x + b`.
* `bias f`: the bias `f 0` of an affine map.
* `IsBiasFree f`: `f 0 = 0`, so `f` is just its linear part.

## Main results

* `affine_apply_eq_linear_add_bias`: every affine map is its linear part plus its bias.
* `affineOf_linear_bias`: an affine map is recovered from its linear part and bias.
* `affine_map_combo`: affine maps preserve affine combinations `a • x + (1 - a) • y`.
-/

namespace MechInterp

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

/-! ### Definitions -/

/-- The affine map `x ↦ L x + b` with linear part `L` and bias `b`. -/
def affineOf (L : V →ₗ[ℝ] W) (b : W) : V →ᵃ[ℝ] W where
  toFun x := L x + b
  linear := L
  map_vadd' p v := by
    simp only [vadd_eq_add, map_add]
    abel

/-- An affine map is bias-free when it sends `0` to `0`. -/
def IsBiasFree (f : V →ᵃ[ℝ] W) : Prop := f 0 = 0

/-- The bias of an affine map, its value `f 0` at the origin. -/
def bias (f : V →ᵃ[ℝ] W) : W := f 0

/-! ### Decomposition into linear part and bias -/

@[simp] theorem affineOf_apply (L : V →ₗ[ℝ] W) (b : W) (x : V) : affineOf L b x = L x + b := rfl

@[simp] theorem affineOf_linear (L : V →ₗ[ℝ] W) (b : W) : (affineOf L b).linear = L := rfl

/-- Every affine map is its linear part plus its bias: `f x = f.linear x + f 0`. This is the
defining property `f (x +ᵥ 0) = f.linear x +ᵥ f 0` of an affine map. -/
theorem affine_apply_eq_linear_add_bias (f : V →ᵃ[ℝ] W) (x : V) : f x = f.linear x + bias f := by
  have h := f.map_vadd 0 x
  simpa [vadd_eq_add, bias] using h

/-- An affine map is rebuilt from its linear part and its bias. -/
theorem affineOf_linear_bias (f : V →ᵃ[ℝ] W) : affineOf f.linear (bias f) = f := by
  ext x
  rw [affineOf_apply, ← affine_apply_eq_linear_add_bias]

/-- A bias-free affine map agrees with its linear part. -/
theorem IsBiasFree.apply_eq {f : V →ᵃ[ℝ] W} (hf : IsBiasFree f) (x : V) : f x = f.linear x := by
  rw [affine_apply_eq_linear_add_bias, bias, hf, add_zero]

/-- An affine map built with zero bias is bias-free. -/
theorem isBiasFree_affineOf_zero (L : V →ₗ[ℝ] W) : IsBiasFree (affineOf L 0) := by
  simp [IsBiasFree]

/-- A linear map, viewed as an affine map, is bias-free. -/
theorem isBiasFree_toAffineMap (L : V →ₗ[ℝ] W) : IsBiasFree L.toAffineMap := by
  simp [IsBiasFree]

/-- Affine maps preserve affine combinations: `f (a • x + (1 - a) • y) = a • f x + (1 - a) • f y`.
The bias survives because the weights `a` and `1 - a` sum to one. -/
theorem affine_map_combo (f : V →ᵃ[ℝ] W) (a : ℝ) (x y : V) :
    f (a • x + (1 - a) • y) = a • f x + (1 - a) • f y := by
  simp only [affine_apply_eq_linear_add_bias f, map_add, map_smul, smul_add]
  have h : bias f = a • bias f + (1 - a) • bias f := by rw [← add_smul]; simp
  conv_lhs => rw [h]
  abel

end MechInterp

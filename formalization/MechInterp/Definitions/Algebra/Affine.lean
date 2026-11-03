import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Mathlib.Data.Real.Basic

set_option linter.style.header false

/-!
# Affine maps

Learned projections are affine maps `V →ᵃ[ℝ] W`, written `x ↦ L x + b`. Linear maps are the
bias-free case.
-/

namespace MechInterp

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

/-- The affine map `x ↦ L x + b`. -/
def affineOf (L : V →ₗ[ℝ] W) (b : W) : V →ᵃ[ℝ] W where
  toFun x := L x + b
  linear := L
  map_vadd' p v := by
    simp only [vadd_eq_add, map_add]
    abel

/-- An affine map is bias-free when it sends `0` to `0`. -/
def IsBiasFree (f : V →ᵃ[ℝ] W) : Prop := f 0 = 0

/-- The bias `f 0` of an affine map. -/
def bias (f : V →ᵃ[ℝ] W) : W := f 0

end MechInterp

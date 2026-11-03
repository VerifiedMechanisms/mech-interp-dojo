import MechInterp.Definitions.Algebra.Affine

set_option linter.style.header false

/-!
# Affine-map decompositions
-/

namespace MechInterp

variable {V W U : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
  [AddCommGroup U] [Module ℝ U]

@[simp] theorem affineOf_apply (L : V →ₗ[ℝ] W) (b : W) (x : V) : affineOf L b x = L x + b := rfl

@[simp] theorem affineOf_linear (L : V →ₗ[ℝ] W) (b : W) : (affineOf L b).linear = L := rfl

/-- Every affine map is its linear part plus its bias. -/
theorem affine_apply_eq_linear_add_bias (f : V →ᵃ[ℝ] W) (x : V) : f x = f.linear x + bias f := by
  have h := f.map_vadd 0 x
  simpa [vadd_eq_add, bias] using h

theorem affineOf_linear_bias (f : V →ᵃ[ℝ] W) : affineOf f.linear (bias f) = f := by
  ext x
  rw [affineOf_apply, ← affine_apply_eq_linear_add_bias]

theorem IsBiasFree.apply_eq {f : V →ᵃ[ℝ] W} (hf : IsBiasFree f) (x : V) : f x = f.linear x := by
  rw [affine_apply_eq_linear_add_bias, bias, hf, add_zero]

theorem isBiasFree_affineOf_zero (L : V →ₗ[ℝ] W) : IsBiasFree (affineOf L 0) := by
  simp [IsBiasFree]

theorem isBiasFree_toAffineMap (L : V →ₗ[ℝ] W) : IsBiasFree L.toAffineMap := by
  simp [IsBiasFree]

/-- Affine maps send affine combinations to affine combinations. -/
theorem affine_map_combo (f : V →ᵃ[ℝ] W) (a : ℝ) (x y : V) :
    f (a • x + (1 - a) • y) = a • f x + (1 - a) • f y := by
  simp only [affine_apply_eq_linear_add_bias f, map_add, map_smul, smul_add]
  have h : bias f = a • bias f + (1 - a) • bias f := by rw [← add_smul]; simp
  conv_lhs => rw [h]
  abel

end MechInterp

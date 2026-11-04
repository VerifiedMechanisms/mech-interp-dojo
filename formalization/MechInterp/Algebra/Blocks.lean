/-
Copyright (c) 2026 Malhar A. Patel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Malhar A. Patel
-/
import MechInterp.Algebra.Spaces

/-!
# Block decompositions of coordinate spaces

Concatenated spaces appear throughout a transformer: multi-head outputs are concatenations of
per-head vectors, and residual streams are split into subspaces. Here a concatenated space is a
coordinate space whose index type is a sum, product, or sigma type. A *block map* is then
restriction or extension along the injective index map that picks out one block, so no index
arithmetic is ever needed.

## Main definitions

All in the namespace `Block`.

* `restrict e` and `extend e he`: restriction along `e`, and extension by zero along an injective
  `e`, packaged as a linear isometry.
* Heterogeneous blocks `RVec (Σ h, ι h)`, where block `h` has its own index type `ι h` (heads of
  different widths): `inj h`, `proj h`, `concat v`.
* Uniform blocks `RVec (H × κ)`, where every block has index type `κ`: `injProd h`,
  `projProd h`, `concatProd v`.
* Zero padding `RVec ι → RVec (ι ⊕ κ)`: `pad ι κ` and its left inverse `unpad ι κ`.

## Main results

For each kind of block:

* `proj h ∘ inj h = id`, and `proj h' ∘ inj h = 0` for `h' ≠ h` (`proj_inj`, `proj_inj_of_ne`);
* injection is adjoint to projection and preserves inner products (`inner_inj_left`,
  `inner_inj`);
* concatenation followed by projection returns each block, and a concatenation is the sum of
  its injected blocks (`proj_concat`, `concat_eq_sum`).

The product-block and padding versions carry the suffix `Prod` or the name `pad`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

namespace MechInterp

namespace Block

open RVec
open scoped InnerProductSpace

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

/-! ### Restriction and extension along an index map -/

/-- Restriction along `e : κ → ι`, reading the coordinates `w (e k)`. -/
def restrict (e : κ → ι) : RVec ι →ₗ[ℝ] RVec κ := restrictAlong e

/-- Extension by zero along an injective `e : κ → ι`, as a linear isometry. Its isometry
certificate is `RVec.inner_extendAlong`. -/
noncomputable def extend (e : κ → ι) (he : Function.Injective e) : RVec κ →ₗᵢ[ℝ] RVec ι :=
  (extendAlong e).isometryOfInner fun v w => inner_extendAlong he v w

@[simp] theorem restrict_apply (e : κ → ι) (w : RVec ι) (k : κ) : restrict e w k = w (e k) :=
  rfl

theorem extend_apply (e : κ → ι) (he : Function.Injective e) (v : RVec κ) :
    extend e he v = extendAlong e v := rfl

/-- Coordinate `e k` of an extension is `v k`. -/
@[simp] theorem extend_apply_self (e : κ → ι) (he : Function.Injective e) (v : RVec κ)
    (k : κ) : extend e he v (e k) = v k :=
  extendAlong_apply_self he v k

/-- Coordinates outside the range of `e` are zero in an extension. -/
theorem extend_apply_of_forall_ne (e : κ → ι) (he : Function.Injective e) (v : RVec κ)
    {i : ι} (hi : ∀ k, e k ≠ i) : extend e he v i = 0 :=
  extendAlong_apply_of_forall_ne v hi

/-- Restriction is a left inverse of extension. -/
@[simp] theorem restrict_extend (e : κ → ι) (he : Function.Injective e) (v : RVec κ) :
    restrict e (extend e he v) = v :=
  restrictAlong_extendAlong he v

/-- Extension is adjoint to restriction: `⟪extend e v, w⟫ = ⟪v, restrict e w⟫`. -/
theorem inner_extend_left (e : κ → ι) (he : Function.Injective e) (v : RVec κ) (w : RVec ι) :
    ⟪extend e he v, w⟫_ℝ = ⟪v, restrict e w⟫_ℝ :=
  inner_extendAlong_left e v w

/-- The mirror form of `inner_extend_left`: `⟪w, extend e v⟫ = ⟪restrict e w, v⟫`. -/
theorem inner_extend_right (e : κ → ι) (he : Function.Injective e) (v : RVec κ) (w : RVec ι) :
    ⟪w, extend e he v⟫_ℝ = ⟪restrict e w, v⟫_ℝ := by
  rw [real_inner_comm, inner_extend_left, real_inner_comm]

/-- Extension preserves inner products. -/
theorem inner_extend (e : κ → ι) (he : Function.Injective e) (v w : RVec κ) :
    ⟪extend e he v, extend e he w⟫_ℝ = ⟪v, w⟫_ℝ :=
  (extend e he).inner_map_map v w

/-- Restricting along `e'` an extension along `e` gives zero when `e` and `e'` have disjoint
ranges: the two blocks do not overlap. -/
theorem restrict_extend_of_disjoint {κ' : Type*} (e : κ → ι) (he : Function.Injective e)
    (e' : κ' → ι) (hdisj : ∀ k k', e k ≠ e' k') (v : RVec κ) :
    restrict e' (extend e he v) = 0 := by
  ext k'
  simp only [restrict_apply, PiLp.zero_apply]
  exact extend_apply_of_forall_ne e he v fun k => hdisj k k'

/-! ### Heterogeneous blocks `RVec (Σ h, ι h)` -/

section Sigma

variable {H : Type*} [Fintype H] [DecidableEq H] {ι : H → Type*} [∀ h, Fintype (ι h)]
  [∀ h, DecidableEq (ι h)]

/-- Inject a vector into block `h` of a sigma-indexed space, padding the other blocks with
zeros. -/
noncomputable def inj (h : H) : RVec (ι h) →ₗᵢ[ℝ] RVec (Σ h, ι h) :=
  extend (Sigma.mk h) sigma_mk_injective

/-- Project block `h` out of a sigma-indexed space. -/
def proj (h : H) : RVec (Σ h, ι h) →ₗ[ℝ] RVec (ι h) := restrict (Sigma.mk h)

/-- Concatenate one vector per block: coordinate `⟨h, j⟩` of `concat v` is `v h j`. -/
def concat (v : (h : H) → RVec (ι h)) : RVec (Σ h, ι h) := ofFun fun k => v k.1 k.2

@[simp] theorem proj_apply (h : H) (w : RVec (Σ h, ι h)) (j : ι h) : proj h w j = w ⟨h, j⟩ :=
  rfl

@[simp] theorem inj_apply_same (h : H) (v : RVec (ι h)) (j : ι h) : inj h v ⟨h, j⟩ = v j :=
  extend_apply_self (Sigma.mk h) sigma_mk_injective v j

/-- Projecting an injected block gives it back. -/
@[simp] theorem proj_inj (h : H) (v : RVec (ι h)) : proj h (inj h v) = v :=
  restrict_extend _ _ v

/-- Projecting onto a different block gives zero. -/
theorem proj_inj_of_ne {h h' : H} (hne : h' ≠ h) (v : RVec (ι h)) : proj h' (inj h v) = 0 :=
  restrict_extend_of_disjoint _ _ _ (fun _ _ heq => hne (congrArg Sigma.fst heq).symm) v

/-- Injection is adjoint to projection: `⟪inj h v, w⟫ = ⟪v, proj h w⟫`. -/
theorem inner_inj_left (h : H) (v : RVec (ι h)) (w : RVec (Σ h, ι h)) :
    ⟪inj h v, w⟫_ℝ = ⟪v, proj h w⟫_ℝ :=
  inner_extend_left _ _ v w

/-- Injection into a block preserves inner products. -/
theorem inner_inj (h : H) (v w : RVec (ι h)) : ⟪inj h v, inj h w⟫_ℝ = ⟪v, w⟫_ℝ :=
  inner_extend _ _ v w

@[simp] theorem concat_apply (v : (h : H) → RVec (ι h)) (k : Σ h, ι h) :
    concat v k = v k.1 k.2 := rfl

/-- Projecting a concatenation onto block `h` returns `v h`. -/
@[simp] theorem proj_concat (v : (h : H) → RVec (ι h)) (h : H) : proj h (concat v) = v h := by
  ext j; rfl

/-- Pairing a concatenation with an injected vector only sees the matching block. -/
theorem inner_concat_inj (v : (h : H) → RVec (ι h)) (h : H) (x : RVec (ι h)) :
    ⟪concat v, inj h x⟫_ℝ = ⟪v h, x⟫_ℝ := by
  rw [real_inner_comm, inner_inj_left, proj_concat, real_inner_comm]

/-- A concatenation is the sum of its injected blocks: `concat v = ∑ h, inj h (v h)`. -/
theorem concat_eq_sum (v : (h : H) → RVec (ι h)) : concat v = ∑ h, inj h (v h) := by
  ext ⟨h, j⟩
  rw [WithLp.ofLp_sum, Finset.sum_apply, Finset.sum_eq_single h]
  · simp
  · intro h' _ hne
    exact extend_apply_of_forall_ne _ _ _ fun k heq => hne (congrArg Sigma.fst heq)
  · simp

end Sigma

/-! ### Uniform blocks `RVec (H × κ)` -/

section Prod

variable {H : Type*} [Fintype H] [DecidableEq H] [DecidableEq κ]

/-- Inject a vector into block `h` of a uniform product space `RVec (H × κ)`. -/
noncomputable def injProd (h : H) : RVec κ →ₗᵢ[ℝ] RVec (H × κ) :=
  extend (Prod.mk h) (Prod.mk_right_injective h)

/-- Project block `h` out of a uniform product space. -/
def projProd (h : H) : RVec (H × κ) →ₗ[ℝ] RVec κ := restrict (Prod.mk h)

/-- Concatenate one vector per block: coordinate `(h, j)` of `concatProd v` is `v h j`. -/
def concatProd (v : H → RVec κ) : RVec (H × κ) := ofFun fun k => v k.1 k.2

@[simp] theorem projProd_apply (h : H) (w : RVec (H × κ)) (j : κ) :
    projProd h w j = w (h, j) := rfl

@[simp] theorem injProd_apply_same (h : H) (v : RVec κ) (j : κ) : injProd h v (h, j) = v j :=
  extend_apply_self (Prod.mk h) (Prod.mk_right_injective h) v j

/-- Projecting an injected block gives it back. -/
@[simp] theorem projProd_injProd (h : H) (v : RVec κ) : projProd h (injProd h v) = v :=
  restrict_extend _ _ v

/-- Projecting onto a different block gives zero. -/
theorem projProd_injProd_of_ne {h h' : H} (hne : h' ≠ h) (v : RVec κ) :
    projProd h' (injProd h v) = 0 :=
  restrict_extend_of_disjoint _ _ _ (fun _ _ heq => hne (congrArg Prod.fst heq).symm) v

/-- Injection is adjoint to projection. -/
theorem inner_injProd_left (h : H) (v : RVec κ) (w : RVec (H × κ)) :
    ⟪injProd h v, w⟫_ℝ = ⟪v, projProd h w⟫_ℝ :=
  inner_extend_left _ _ v w

/-- Injection into a block preserves inner products. -/
theorem inner_injProd (h : H) (v w : RVec κ) : ⟪injProd h v, injProd h w⟫_ℝ = ⟪v, w⟫_ℝ :=
  inner_extend _ _ v w

@[simp] theorem concatProd_apply (v : H → RVec κ) (k : H × κ) : concatProd v k = v k.1 k.2 :=
  rfl

/-- Projecting a concatenation onto block `h` returns `v h`. -/
@[simp] theorem projProd_concatProd (v : H → RVec κ) (h : H) :
    projProd h (concatProd v) = v h := by
  ext j; rfl

/-- Pairing a concatenation with an injected vector only sees the matching block. -/
theorem inner_concatProd_injProd (v : H → RVec κ) (h : H) (x : RVec κ) :
    ⟪concatProd v, injProd h x⟫_ℝ = ⟪v h, x⟫_ℝ := by
  rw [real_inner_comm, inner_injProd_left, projProd_concatProd, real_inner_comm]

end Prod

/-! ### Zero padding `RVec ι → RVec (ι ⊕ κ)` -/

section PadDefs

variable (ι κ) [DecidableEq κ]

/-- Pad a vector with zero coordinates indexed by `κ`. -/
noncomputable def pad : RVec ι →ₗᵢ[ℝ] RVec (ι ⊕ κ) := extend Sum.inl Sum.inl_injective

/-- Forget the padding coordinates. -/
def unpad : RVec (ι ⊕ κ) →ₗ[ℝ] RVec ι := restrict Sum.inl

end PadDefs

section Pad

variable [DecidableEq κ]

/-- Removing the padding recovers the original vector. -/
@[simp] theorem unpad_pad (v : RVec ι) : unpad ι κ (pad ι κ v) = v :=
  restrict_extend _ _ v

/-- Padding is adjoint to unpadding. -/
theorem inner_pad_left (v : RVec ι) (w : RVec (ι ⊕ κ)) :
    ⟪pad ι κ v, w⟫_ℝ = ⟪v, unpad ι κ w⟫_ℝ :=
  inner_extend_left _ _ v w

/-- Padding preserves inner products. -/
theorem inner_pad (v w : RVec ι) : ⟪pad ι κ v, pad ι κ w⟫_ℝ = ⟪v, w⟫_ℝ :=
  inner_extend _ _ v w

@[simp] theorem pad_apply_inl (v : RVec ι) (i : ι) : pad ι κ v (Sum.inl i) = v i :=
  extend_apply_self _ _ v i

/-- The padding coordinates are zero. -/
@[simp] theorem pad_apply_inr (v : RVec ι) (k : κ) : pad ι κ v (Sum.inr k) = 0 :=
  extend_apply_of_forall_ne _ _ v fun _ => Sum.inl_ne_inr

end Pad

end Block

end MechInterp

import MechInterp.Definitions.Algebra.Blocks

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Block-coordinate identities

`proj ∘ inj = id`, cross-block vanishing, inner-product preservation, adjointness of
injection and projection, and the concatenation identities, for sigma blocks, uniform
product blocks, and padding.
-/

namespace MechInterp

namespace Block

open RVec
open scoped InnerProductSpace

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

@[simp] theorem restrict_apply (e : κ → ι) (w : RVec ι) (k : κ) : restrict e w k = w (e k) :=
  rfl

theorem extend_apply (e : κ → ι) (he : Function.Injective e) (v : RVec κ) :
    extend e he v = extendAlong e v := rfl

@[simp] theorem extend_apply_self (e : κ → ι) (he : Function.Injective e) (v : RVec κ)
    (k : κ) : extend e he v (e k) = v k :=
  extendAlong_apply_self he v k

theorem extend_apply_of_forall_ne (e : κ → ι) (he : Function.Injective e) (v : RVec κ)
    {i : ι} (hi : ∀ k, e k ≠ i) : extend e he v i = 0 :=
  extendAlong_apply_of_forall_ne v hi

@[simp] theorem restrict_extend (e : κ → ι) (he : Function.Injective e) (v : RVec κ) :
    restrict e (extend e he v) = v :=
  restrictAlong_extendAlong he v

/-- Extension is adjoint to restriction. -/
theorem inner_extend_left (e : κ → ι) (he : Function.Injective e) (v : RVec κ) (w : RVec ι) :
    ⟪extend e he v, w⟫_ℝ = ⟪v, restrict e w⟫_ℝ :=
  inner_extendAlong_left e v w

theorem inner_extend_right (e : κ → ι) (he : Function.Injective e) (v : RVec κ) (w : RVec ι) :
    ⟪w, extend e he v⟫_ℝ = ⟪restrict e w, v⟫_ℝ := by
  rw [real_inner_comm, inner_extend_left, real_inner_comm]

/-- Extension preserves inner products. -/
theorem inner_extend (e : κ → ι) (he : Function.Injective e) (v w : RVec κ) :
    ⟪extend e he v, extend e he w⟫_ℝ = ⟪v, w⟫_ℝ :=
  (extend e he).inner_map_map v w

/-- Restricting along `e'` an extension along `e` with disjoint ranges gives zero. -/
theorem restrict_extend_of_disjoint {κ' : Type*} (e : κ → ι) (he : Function.Injective e)
    (e' : κ' → ι) (hdisj : ∀ k k', e k ≠ e' k') (v : RVec κ) :
    restrict e' (extend e he v) = 0 := by
  ext k'
  simp only [restrict_apply, PiLp.zero_apply]
  exact extend_apply_of_forall_ne e he v fun k => hdisj k k'

section Sigma

variable {H : Type*} [Fintype H] [DecidableEq H] {ι : H → Type*} [∀ h, Fintype (ι h)]
  [∀ h, DecidableEq (ι h)]

@[simp] theorem proj_apply (h : H) (w : RVec (Σ h, ι h)) (j : ι h) : proj h w j = w ⟨h, j⟩ :=
  rfl

@[simp] theorem inj_apply_same (h : H) (v : RVec (ι h)) (j : ι h) : inj h v ⟨h, j⟩ = v j :=
  extend_apply_self (Sigma.mk h) sigma_mk_injective v j

@[simp] theorem proj_inj (h : H) (v : RVec (ι h)) : proj h (inj h v) = v :=
  restrict_extend _ _ v

theorem proj_inj_of_ne {h h' : H} (hne : h' ≠ h) (v : RVec (ι h)) : proj h' (inj h v) = 0 :=
  restrict_extend_of_disjoint _ _ _ (fun _ _ heq => hne (congrArg Sigma.fst heq).symm) v

theorem inner_inj_left (h : H) (v : RVec (ι h)) (w : RVec (Σ h, ι h)) :
    ⟪inj h v, w⟫_ℝ = ⟪v, proj h w⟫_ℝ :=
  inner_extend_left _ _ v w

theorem inner_inj (h : H) (v w : RVec (ι h)) : ⟪inj h v, inj h w⟫_ℝ = ⟪v, w⟫_ℝ :=
  inner_extend _ _ v w

@[simp] theorem concat_apply (v : (h : H) → RVec (ι h)) (k : Σ h, ι h) :
    concat v k = v k.1 k.2 := rfl

@[simp] theorem proj_concat (v : (h : H) → RVec (ι h)) (h : H) : proj h (concat v) = v h := by
  ext j; rfl

theorem inner_concat_inj (v : (h : H) → RVec (ι h)) (h : H) (x : RVec (ι h)) :
    ⟪concat v, inj h x⟫_ℝ = ⟪v h, x⟫_ℝ := by
  rw [real_inner_comm, inner_inj_left, proj_concat, real_inner_comm]

theorem concat_eq_sum (v : (h : H) → RVec (ι h)) : concat v = ∑ h, inj h (v h) := by
  ext ⟨h, j⟩
  rw [WithLp.ofLp_sum, Finset.sum_apply, Finset.sum_eq_single h]
  · simp
  · intro h' _ hne
    exact extend_apply_of_forall_ne _ _ _ fun k heq => hne (congrArg Sigma.fst heq)
  · simp

end Sigma

section Prod

variable {H : Type*} [Fintype H] [DecidableEq H] [DecidableEq κ]

@[simp] theorem projProd_apply (h : H) (w : RVec (H × κ)) (j : κ) :
    projProd h w j = w (h, j) := rfl

@[simp] theorem injProd_apply_same (h : H) (v : RVec κ) (j : κ) : injProd h v (h, j) = v j :=
  extend_apply_self (Prod.mk h) (Prod.mk_right_injective h) v j

@[simp] theorem projProd_injProd (h : H) (v : RVec κ) : projProd h (injProd h v) = v :=
  restrict_extend _ _ v

theorem projProd_injProd_of_ne {h h' : H} (hne : h' ≠ h) (v : RVec κ) :
    projProd h' (injProd h v) = 0 :=
  restrict_extend_of_disjoint _ _ _ (fun _ _ heq => hne (congrArg Prod.fst heq).symm) v

theorem inner_injProd_left (h : H) (v : RVec κ) (w : RVec (H × κ)) :
    ⟪injProd h v, w⟫_ℝ = ⟪v, projProd h w⟫_ℝ :=
  inner_extend_left _ _ v w

theorem inner_injProd (h : H) (v w : RVec κ) : ⟪injProd h v, injProd h w⟫_ℝ = ⟪v, w⟫_ℝ :=
  inner_extend _ _ v w

@[simp] theorem concatProd_apply (v : H → RVec κ) (k : H × κ) : concatProd v k = v k.1 k.2 :=
  rfl

@[simp] theorem projProd_concatProd (v : H → RVec κ) (h : H) :
    projProd h (concatProd v) = v h := by
  ext j; rfl

theorem inner_concatProd_injProd (v : H → RVec κ) (h : H) (x : RVec κ) :
    ⟪concatProd v, injProd h x⟫_ℝ = ⟪v h, x⟫_ℝ := by
  rw [real_inner_comm, inner_injProd_left, projProd_concatProd, real_inner_comm]

end Prod

section Pad

variable [DecidableEq κ]

@[simp] theorem unpad_pad (v : RVec ι) : unpad ι κ (pad ι κ v) = v :=
  restrict_extend _ _ v

theorem inner_pad_left (v : RVec ι) (w : RVec (ι ⊕ κ)) :
    ⟪pad ι κ v, w⟫_ℝ = ⟪v, unpad ι κ w⟫_ℝ :=
  inner_extend_left _ _ v w

theorem inner_pad (v w : RVec ι) : ⟪pad ι κ v, pad ι κ w⟫_ℝ = ⟪v, w⟫_ℝ :=
  inner_extend _ _ v w

@[simp] theorem pad_apply_inl (v : RVec ι) (i : ι) : pad ι κ v (Sum.inl i) = v i :=
  extend_apply_self _ _ v i

@[simp] theorem pad_apply_inr (v : RVec ι) (k : κ) : pad ι κ v (Sum.inr k) = 0 :=
  extend_apply_of_forall_ne _ _ v fun _ => Sum.inl_ne_inr

end Pad

end Block

end MechInterp

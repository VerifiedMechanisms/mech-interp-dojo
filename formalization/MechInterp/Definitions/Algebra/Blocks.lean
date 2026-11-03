import MechInterp.Theorems.Algebra.Spaces

set_option linter.style.header false

/-!
# Block-coordinate maps

Concatenated spaces are indexed by sum, product, and sigma types, so block maps are
coordinate restriction and extension along an injective index map. No index arithmetic is
needed.

* Sigma blocks `RVec (Σ h, ι h)`: `inj`, `proj`, `concat` (heterogeneous head widths).
* Product blocks `RVec (H × κ)`: `injProd`, `projProd`, `concatProd` (uniform widths).
* Padding `RVec ι → RVec (ι ⊕ κ)`: `pad`, `unpad`.
-/

namespace MechInterp

namespace Block

open RVec

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

/-- Restriction along `e`. -/
def restrict (e : κ → ι) : RVec ι →ₗ[ℝ] RVec κ := restrictAlong e

/-- Extension by zero along an injective `e`, as a linear isometry. -/
noncomputable def extend (e : κ → ι) (he : Function.Injective e) : RVec κ →ₗᵢ[ℝ] RVec ι :=
  (extendAlong e).isometryOfInner fun v w => inner_extendAlong he v w

section Sigma

variable {H : Type*} [Fintype H] [DecidableEq H] {ι : H → Type*} [∀ h, Fintype (ι h)]
  [∀ h, DecidableEq (ι h)]

/-- Inject a vector into block `h` of a sigma-indexed space. -/
noncomputable def inj (h : H) : RVec (ι h) →ₗᵢ[ℝ] RVec (Σ h, ι h) :=
  extend (Sigma.mk h) sigma_mk_injective

/-- Project block `h` out of a sigma-indexed space. -/
def proj (h : H) : RVec (Σ h, ι h) →ₗ[ℝ] RVec (ι h) := restrict (Sigma.mk h)

/-- Concatenate one vector per block. -/
def concat (v : (h : H) → RVec (ι h)) : RVec (Σ h, ι h) := ofFun fun k => v k.1 k.2

end Sigma

section Prod

variable {H : Type*} [Fintype H] [DecidableEq H] [DecidableEq κ]

/-- Inject a vector into block `h` of a uniform product space `RVec (H × κ)`. -/
noncomputable def injProd (h : H) : RVec κ →ₗᵢ[ℝ] RVec (H × κ) :=
  extend (Prod.mk h) (Prod.mk_right_injective h)

/-- Project block `h` out of a uniform product space. -/
def projProd (h : H) : RVec (H × κ) →ₗ[ℝ] RVec κ := restrict (Prod.mk h)

/-- Concatenate one vector per block in a uniform product space. -/
def concatProd (v : H → RVec κ) : RVec (H × κ) := ofFun fun k => v k.1 k.2

end Prod

section Pad

variable (ι κ) [DecidableEq κ]

/-- Pad by zero coordinates. -/
noncomputable def pad : RVec ι →ₗᵢ[ℝ] RVec (ι ⊕ κ) := extend Sum.inl Sum.inl_injective

/-- Forget the padding coordinates. -/
def unpad : RVec (ι ⊕ κ) →ₗ[ℝ] RVec ι := restrict Sum.inl

end Pad

end Block

end MechInterp

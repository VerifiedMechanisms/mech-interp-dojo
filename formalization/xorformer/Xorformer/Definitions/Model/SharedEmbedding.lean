import Xorformer.Definitions.Prelude
import Xorformer.Definitions.Model.Head

set_option linter.style.header false

/-!
# Shared-embedding and head-local attention models

This module holds the definitions of this part of the development. Their proofs are in
`Xorformer.Theorems.Model.SharedEmbedding`.

`HeadFamily` permits each head to carry its own token and positional embeddings.
The prose model instead uses one token embedding and one positional embedding,
followed by head-specific attention maps. `SharedHeadFamily` encodes that model
literally.

This file proves that the two parameterizations have the same head-count
expressivity when width is unrestricted. A head-local family of width `d` is
sent to a shared-embedding family of width `H * d`. The shared embedding is the
concatenation of the `H` local embedding blocks. Head `h` projects to block `h`,
applies its original maps, and writes its result back into block `h`.
-/

namespace Xorformer

open MechInterp
open scoped BigOperators InnerProductSpace

/-! ## Block-coordinate maps -/

/-- Project block `h` from a vector whose `H` blocks each have width `d`. -/
noncomputable def headBlockProject {H d : ℕ} (h : Fin H) :
    Vec (H * d) →ₗ[ℝ] Vec d where
  toFun v := WithLp.toLp 2 (fun j => v (finProdFinEquiv (h, j)))
  map_add' x y := by
    ext j
    rfl
  map_smul' c x := by
    ext j
    rfl

/-- Inject a width-`d` vector into block `h` of an `H * d` vector. -/
noncomputable def headBlockInject {H d : ℕ} (h : Fin H) :
    Vec d →ₗ[ℝ] Vec (H * d) where
  toFun v := WithLp.toLp 2 (fun k =>
    if (finProdFinEquiv.symm k).1 = h then v (finProdFinEquiv.symm k).2 else 0)
  map_add' x y := by
    ext k
    by_cases hk : k.divNat = h <;> simp [hk]
  map_smul' c x := by
    ext k
    by_cases hk : k.divNat = h <;> simp [hk]

/-- Concatenate `H` width-`d` vectors into one width-`H * d` vector. -/
noncomputable def headBlockConcat {H d : ℕ} (v : Fin H → Vec d) : Vec (H * d) :=
  WithLp.toLp 2 (fun k => v k.divNat k.modNat)

/-! ## The literal shared-embedding model -/

/-- An `H`-head family with one token embedding and one positional embedding
shared by every head. Only the query, key, and value maps depend on the head. -/
structure SharedHeadFamily (n d H : ℕ) where
  tokenEmbed : Fin 3 → Vec d
  posEmbed : SeqPos n → Vec d
  WQ : Fin H → Vec d →ₗ[ℝ] Vec d
  WK : Fin H → Vec d →ₗ[ℝ] Vec d
  WV : Fin H → Vec d →ₗ[ℝ] Vec d

namespace SharedHeadFamily

/-- View one member of a shared family as an ordinary `Head`. -/
noncomputable def head (M : SharedHeadFamily n d H) (h : Fin H) : Head n d where
  tokenEmbed := M.tokenEmbed
  posEmbed := M.posEmbed
  WQ := M.WQ h
  WK := M.WK h
  WV := M.WV h

/-- Forget that the embeddings are shared. -/
noncomputable def toHeadFamily (M : SharedHeadFamily n d H) : HeadFamily n d H :=
  M.head

/-- Summed attention update of a shared-embedding head family. -/
noncomputable def attnUpdate (M : SharedHeadFamily n d H) :
    (Fin n → Bool) → Vec d :=
  headFamilyAttnUpdate M.toHeadFamily

end SharedHeadFamily

/-- Computability in the literal shared-embedding model from `model.md`. -/
def computableWithSharedHeadsN (n H : ℕ) (f : (Fin n → Bool) → Bool) : Prop :=
  ∃ d, ∃ M : SharedHeadFamily n d H, computesPred f M.attnUpdate

/-- Least head count in the literal shared-embedding model. -/
noncomputable def SharedHStar (n : ℕ) (f : (Fin n → Bool) → Bool) : ℕ :=
  by
    classical
    exact if h : ∃ k, computableWithSharedHeadsN n k f then Nat.find h else 0

/-! ## Concatenating a head-local family -/

/-- Lift a head-local linear map so it reads and writes only block `h`. -/
noncomputable def headBlockLift {H d : ℕ} (h : Fin H) (A : Vec d →ₗ[ℝ] Vec d) :
    Vec (H * d) →ₗ[ℝ] Vec (H * d) :=
  (headBlockInject h).comp (A.comp (headBlockProject h))

/-- Concatenate every head-local parameter block into one shared embedding space.
The number of heads is unchanged and the width grows from `d` to `H * d`. -/
noncomputable def shareHeadEmbeddings {n d H : ℕ} (Hs : HeadFamily n d H) :
    SharedHeadFamily n (H * d) H where
  tokenEmbed t := headBlockConcat (fun h => (Hs h).tokenEmbed t)
  posEmbed p := headBlockConcat (fun h => (Hs h).posEmbed p)
  WQ h := headBlockLift h (Hs h).WQ
  WK h := headBlockLift h (Hs h).WK
  WV h := headBlockLift h (Hs h).WV

/-! ## Head-count expressivity equivalence -/

end Xorformer

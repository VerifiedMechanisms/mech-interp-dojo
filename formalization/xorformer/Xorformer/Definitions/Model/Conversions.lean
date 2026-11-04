import Xorformer.Definitions.Model.Literal
import Xorformer.Definitions.Model.Head
import MechInterp.Algebra.Blocks

set_option linter.style.header false

/-!
# Conversions between the literal and reduced models

Both directions change width. Neither is a fixed-width statement.

**Literal to reduced** (`LiteralParams.toReduced`, width `d + dh`). The residual space
`Vec d` and the head space `Vec dh` are placed in complementary coordinate blocks of
`Vec (d + dh)`. Head `h` reads the residual block, maps queries and keys into the head block
with `ι₂ ∘ W ∘ r₁`, and writes `ι₁ W_O W_V` back into the residual block. Every reduced head
carries the same (shared) embedding.

**Reduced to literal** (`toLiteral`, width `H·d + 1`, head width `d + 1`). The head-local
embeddings are concatenated into blocks `(Fin H × Fin d)`. Head `h` reads its block with
`P_h`, applies its square maps padded into `Vec (d + 1)`, and writes back into block `h`
with `I_h`. One spare coordinate keeps both widths positive.
-/

noncomputable section

namespace Xorformer

open MechInterp
open scoped InnerProductSpace

namespace Conversion

/-- Reindex `Fin a ⊕ Fin b` coordinates as `Fin (a + b)`. -/
def sumIso (a b : ℕ) : RVec (Fin a ⊕ Fin b) ≃ₗᵢ[ℝ] Vec (a + b) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ finSumFinEquiv

/-- Isometric inclusion of `Vec a` as the first block of `Vec (a + b)`. -/
def firstIn (a b : ℕ) : Vec a →ₗ[ℝ] Vec (a + b) :=
  (sumIso a b).toLinearEquiv.toLinearMap ∘ₗ (Block.pad (Fin a) (Fin b)).toLinearMap

/-- Projection of `Vec (a + b)` onto its first block (a retraction of `firstIn`). -/
def firstOut (a b : ℕ) : Vec (a + b) →ₗ[ℝ] Vec a :=
  Block.unpad (Fin a) (Fin b) ∘ₗ (sumIso a b).symm.toLinearEquiv.toLinearMap

/-- Isometric inclusion of `Vec b` as the second block of `Vec (a + b)`. -/
def secondIn (a b : ℕ) : Vec b →ₗ[ℝ] Vec (a + b) :=
  (sumIso a b).toLinearEquiv.toLinearMap ∘ₗ
    (Block.extend (Sum.inr : Fin b → Fin a ⊕ Fin b) Sum.inr_injective).toLinearMap

/-- Index type of the widened residual space: one `Fin d` block per head plus one spare
coordinate. -/
abbrev BlockIdx (H d : ℕ) := (Fin H × Fin d) ⊕ Fin 1

/-- Reindex the widened residual space as `Vec (H * d + 1)`. -/
def blockIso (H d : ℕ) : RVec (BlockIdx H d) ≃ₗᵢ[ℝ] Vec (H * d + 1) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
    ((finProdFinEquiv.sumCongr (Equiv.refl (Fin 1))).trans finSumFinEquiv)

/-- `I_h`: write a `Vec d` vector into block `h`. -/
def blockIn {H d : ℕ} (h : Fin H) : Vec d →ₗ[ℝ] Vec (H * d + 1) :=
  (blockIso H d).toLinearEquiv.toLinearMap ∘ₗ
    (Block.pad (Fin H × Fin d) (Fin 1)).toLinearMap ∘ₗ (Block.injProd h).toLinearMap

/-- `P_h`: read block `h`. -/
def blockOut {H d : ℕ} (h : Fin H) : Vec (H * d + 1) →ₗ[ℝ] Vec d :=
  Block.projProd h ∘ₗ Block.unpad (Fin H × Fin d) (Fin 1) ∘ₗ
    (blockIso H d).symm.toLinearEquiv.toLinearMap

/-- Concatenate one `Vec d` vector per head into the widened residual space. -/
def blockConcat {H d : ℕ} (v : Fin H → Vec d) : Vec (H * d + 1) :=
  blockIso H d (Block.pad (Fin H × Fin d) (Fin 1) (Block.concatProd v))

end Conversion

open Conversion

namespace LiteralParams

variable {n H d dh : ℕ}

/-- Head `h` of a literal model as a reduced head of width `d + dh`. -/
def toReducedHead (θ : LiteralParams n H d dh) (h : Fin H) : Head n (d + dh) where
  tokenEmbed t := firstIn d dh (θ.embedding.tokenVec t)
  posEmbed p := firstIn d dh (θ.embedding.posVec p)
  WQ := secondIn d dh ∘ₗ θ.WQ h ∘ₗ firstOut d dh
  WK := secondIn d dh ∘ₗ θ.WK h ∘ₗ firstOut d dh
  WV := firstIn d dh ∘ₗ θ.WO h ∘ₗ θ.WV h ∘ₗ firstOut d dh

/-- The reduced head family of a literal model. -/
def toReduced (θ : LiteralParams n H d dh) : HeadFamily n (d + dh) H := θ.toReducedHead

/-- The reduced readout direction. -/
def reducedReadout (θ : LiteralParams n H d dh) : Vec (d + dh) := firstIn d dh θ.w

/-- The reduced threshold: the constant query residual is absorbed into it. -/
def reducedThreshold (θ : LiteralParams n H d dh) : ℝ :=
  θ.τ - ⟪θ.w, θ.embedding.tokenVec 2 + θ.embedding.posVec none⟫_ℝ

end LiteralParams

/-- The shared embedding of a widened reduced family: concatenated head-local embeddings. -/
def toLiteralEmbedding {n d H : ℕ} (Hs : HeadFamily n d H) :
    AdditiveEmbedding (Fin 3) (SeqPos n) (Vec (H * d + 1)) :=
  AdditiveEmbedding.ofFunctions (fun t => blockConcat fun h => (Hs h).tokenEmbed t)
    (fun p => blockConcat fun h => (Hs h).posEmbed p)

/-- The literal readout direction `∑ h, I_h w`. -/
def toLiteralReadout {d H : ℕ} (w : Vec d) : Vec (H * d + 1) := ∑ h : Fin H, blockIn h w

/-- A reduced head family with readout `(w, τ)` as a literal model. -/
def toLiteral {n d H : ℕ} (Hs : HeadFamily n d H) (w : Vec d) (τ : ℝ) :
    LiteralParams n H (H * d + 1) (d + 1) where
  embedding := toLiteralEmbedding Hs
  WQ h := firstIn d 1 ∘ₗ (Hs h).WQ ∘ₗ blockOut h
  WK h := firstIn d 1 ∘ₗ (Hs h).WK ∘ₗ blockOut h
  WV h := firstIn d 1 ∘ₗ (Hs h).WV ∘ₗ blockOut h
  WO h := blockIn h ∘ₗ firstOut d 1
  w := toLiteralReadout w
  τ := τ + ⟪toLiteralReadout (H := H) w,
    (toLiteralEmbedding Hs).tokenVec 2 + (toLiteralEmbedding Hs).posVec none⟫_ℝ

end Xorformer

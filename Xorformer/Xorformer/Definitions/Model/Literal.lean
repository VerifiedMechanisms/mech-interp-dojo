import Xorformer.Definitions.Model.Input
import MechInterp.Architecture.Embedding
import MechInterp.Architecture.MultiHead
import MechInterp.Architecture.Mask

set_option linter.style.header false

/-!
# The literal XORFormer

The model of `model.md`, built from `MechInterp` components.

* **Embedding.** One additive token-and-position embedding `u_p = e_{tok(p)} + p_p`
  (`MechInterp.AdditiveEmbedding`), shared by every head.
* **Heads.** `H` heads with rectangular, bias-free projections
  `W_Q, W_K, W_V : ℝ^{dModel} → ℝ^{dHead}` and `W_O : ℝ^{dHead} → ℝ^{dModel}`
  (`MechInterp.AttentionHead`).
* **Layer.** One multi-head attention layer (`MechInterp.MultiHead`). It uses the full mask,
  scores `⟪q, k⟫` (scale one, zero bias), the softmax rule at temperature one, and no output
  bias. All heads read the same embedded stream.
* **Residual.** The full residual stream `X = u + MHA(u)` at every position.
* **Readout.** The affine probe `S(x) = ⟪w, X_query⟫ - τ`. Then `f x = true` exactly when
  `S(x) > 0`, so zero scores are classified as false.

The causal variant uses `Mask.causal seqOrd`, with the query last. Its query readout agrees
with the full-mask model (`Theorems/Model/Literal`).
-/

noncomputable section

namespace Xorformer

open MechInterp
open scoped InnerProductSpace

/-- Parameters of the literal XORFormer with `H` heads, residual width `d`, and head
width `dh`. -/
structure LiteralParams (n H d dh : ℕ) where
  /-- The shared token and positional embedding. -/
  embedding : AdditiveEmbedding (Fin 3) (SeqPos n) (Vec d)
  WQ : Fin H → Vec d →ₗ[ℝ] Vec dh
  WK : Fin H → Vec d →ₗ[ℝ] Vec dh
  WV : Fin H → Vec d →ₗ[ℝ] Vec dh
  WO : Fin H → Vec dh →ₗ[ℝ] Vec d
  /-- Readout direction. -/
  w : Vec d
  /-- Readout threshold. -/
  τ : ℝ

/-- The full-attention softmax rule at temperature one. -/
def fullRule (n : ℕ) : PatternRule (SeqPos n) (SeqPos n) Mask.full :=
  softmaxRule 1 Mask.full_wellFormed

/-- The causal softmax rule at temperature one, with the query last. -/
def causalRule (n : ℕ) : PatternRule (SeqPos n) (SeqPos n) (Mask.causal seqOrd) :=
  softmaxRule 1 (Mask.causal_wellFormed seqOrd)

namespace LiteralParams

variable {n H d dh : ℕ}

/-- Head `h` as a `MechInterp` attention head with bias-free projections. -/
def head (θ : LiteralParams n H d dh) (h : Fin H) : AttentionHead (Vec d) (Vec dh) (Vec dh) :=
  ⟨(θ.WQ h).toAffineMap, (θ.WK h).toAffineMap, (θ.WV h).toAffineMap, θ.WO h⟩

/-- The attention layer for a given mask and pattern rule: score scale one, zero score bias,
and no output bias. -/
def attentionWith (θ : LiteralParams n H d dh) (M : Mask (SeqPos n) (SeqPos n))
    (ρ : PatternRule (SeqPos n) (SeqPos n) M) : MultiHead (SeqPos n) (SeqPos n) (Vec d) :=
  MultiHead.uniform (Fin H) dh dh θ.head (fun _ => ScoreRule.standard 1) M ρ 0

/-- The full-attention layer. -/
def attention (θ : LiteralParams n H d dh) : MultiHead (SeqPos n) (SeqPos n) (Vec d) :=
  θ.attentionWith Mask.full (fullRule n)

/-- The causal-attention layer. -/
def causalAttention (θ : LiteralParams n H d dh) : MultiHead (SeqPos n) (SeqPos n) (Vec d) :=
  θ.attentionWith (Mask.causal seqOrd) (causalRule n)

/-- The embedded input stream `u(x)`. -/
def input (θ : LiteralParams n H d dh) (x : Fin n → Bool) : MechInterp.Stream (SeqPos n) (Vec d) :=
  θ.embedding.embed (Head.seqTok x)

/-- The residual stream after one attention block, for a given mask and pattern rule. -/
def residualWith (θ : LiteralParams n H d dh) (M : Mask (SeqPos n) (SeqPos n))
    (ρ : PatternRule (SeqPos n) (SeqPos n) M) (x : Fin n → Bool) :
    MechInterp.Stream (SeqPos n) (Vec d) :=
  θ.input x + (θ.attentionWith M ρ).eval (θ.input x) (θ.input x)

/-- The full-attention residual stream `X = u + MHA(u)`. -/
def residual (θ : LiteralParams n H d dh) (x : Fin n → Bool) :
    MechInterp.Stream (SeqPos n) (Vec d) :=
  θ.residualWith Mask.full (fullRule n) x

/-- The causal-attention residual stream. -/
def causalResidual (θ : LiteralParams n H d dh) (x : Fin n → Bool) :
    MechInterp.Stream (SeqPos n) (Vec d) :=
  θ.residualWith (Mask.causal seqOrd) (causalRule n) x

/-- The classifier score `S(x) = ⟪w, X_query⟫ - τ`. -/
def score (θ : LiteralParams n H d dh) (x : Fin n → Bool) : ℝ :=
  ⟪θ.w, θ.residual x none⟫_ℝ - θ.τ

/-- The classifier score of the causal variant. -/
def causalScore (θ : LiteralParams n H d dh) (x : Fin n → Bool) : ℝ :=
  ⟪θ.w, θ.causalResidual x none⟫_ℝ - θ.τ

/-- The model computes `f`: `f x = true` exactly when the score is positive. -/
def Computes (θ : LiteralParams n H d dh) (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ x, 0 < θ.score x ↔ f x = true

/-- The query-row attention logit of head `h` at source `j`: `⟪W_Q u_q, W_K u_j⟫`. -/
def queryLogit (θ : LiteralParams n H d dh) (h : Fin H) (x : Fin n → Bool) (j : SeqPos n) :
    ℝ :=
  ⟪θ.WQ h (θ.input x none), θ.WK h (θ.input x j)⟫_ℝ

/-- The query-row attention weight `A^{(h)}_{qj}` of head `h`. -/
def queryWeight (θ : LiteralParams n H d dh) (h : Fin H) (x : Fin n → Bool) (j : SeqPos n) :
    ℝ :=
  Real.exp (θ.queryLogit h x j) / ∑ j', Real.exp (θ.queryLogit h x j')

/-- The softmax numerator `∑ j, exp(logit_j) W_V u_j` of head `h` (in head space). -/
def headNumerator (θ : LiteralParams n H d dh) (h : Fin H) (x : Fin n → Bool) : Vec dh :=
  ∑ j, Real.exp (θ.queryLogit h x j) • θ.WV h (θ.input x j)

/-- The softmax denominator `∑ j, exp(logit_j)` of head `h`. -/
def headDenominator (θ : LiteralParams n H d dh) (h : Fin H) (x : Fin n → Bool) : ℝ :=
  ∑ j, Real.exp (θ.queryLogit h x j)

/-- The contribution `W_O ∑ j, A_qj W_V u_j` of head `h` to the query residual. -/
def headOutput (θ : LiteralParams n H d dh) (h : Fin H) (x : Fin n → Bool) : Vec d :=
  θ.WO h (∑ j, θ.queryWeight h x j • θ.WV h (θ.input x j))

end LiteralParams

end Xorformer

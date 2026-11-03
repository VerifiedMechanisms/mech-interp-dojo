import Xorformer.Definitions.Model.Literal
import MechInterp.Theorems.Architecture.Attention
import MechInterp.Theorems.Architecture.Softmax
import MechInterp.Theorems.Architecture.Score
import MechInterp.Theorems.Architecture.Embedding
import MechInterp.Theorems.Architecture.Mask

set_option linter.style.header false

/-!
# Semantics of the literal XORFormer

* `residual_none`, `score_eq`: the query residual is the constant query embedding plus the
  head outputs `W_O ∑ j, A_qj W_V u_j`. This is the literal score of `model.md`.
* `input_none_const`: the query embedding does not depend on the input.
* `queryWeight_eq_softmax`: each head's query-row pattern is the softmax of its logits
  `⟪W_Q u_q, W_K u_j⟫`.
* `causalScore_eq_score`: with the query last, the causal mask gives the same query readout
  as the full mask. This holds for this one-layer query readout only.
-/

namespace Xorformer

open MechInterp
open scoped InnerProductSpace

/-- The full softmax rule at temperature one. -/
theorem fullRule_A {n : ℕ} (s : SeqPos n → SeqPos n → ℝ) (i j : SeqPos n) :
    ((fullRule n).toPattern s).A i j = Real.exp (s i j) / ∑ j', Real.exp (s i j') := by
  have hset : (Mask.full : Mask (SeqPos n) (SeqPos n)).allowedSet i = Finset.univ := by
    ext k; simp [Mask.allowedSet, Mask.full]
  simp only [fullRule, softmaxRule_A, maskedSoftmax, maskedDenom, hset, one_mul]
  rfl

/-- The query is last, so its causal row allows every position. -/
theorem causal_allowed_none {n : ℕ} (j : SeqPos n) : (Mask.causal seqOrd).allowed none j := by
  cases j with
  | none => exact le_refl _
  | some i => exact (Mask.causal_allowed _ _ _).mpr (le_of_lt i.isLt)

/-- At the query row, the causal and full softmax rules agree. -/
theorem causalRule_A_none {n : ℕ} (s : SeqPos n → SeqPos n → ℝ) (j : SeqPos n) :
    ((causalRule n).toPattern s).A none j = ((fullRule n).toPattern s).A none j := by
  have hset : (Mask.causal seqOrd : Mask (SeqPos n) (SeqPos n)).allowedSet none =
      Finset.univ := by
    ext k; simp only [Finset.mem_univ, iff_true, Mask.mem_allowedSet]; exact causal_allowed_none k
  rw [fullRule_A]
  simp only [causalRule, softmaxRule_A, maskedSoftmax, maskedDenom, hset, one_mul,
    if_pos (causal_allowed_none j)]

namespace LiteralParams

variable {n H d dh : ℕ} (θ : LiteralParams n H d dh)

theorem input_apply (x : Fin n → Bool) (p : SeqPos n) :
    θ.input x p = θ.embedding.tokenVec (Head.seqTok x p) + θ.embedding.posVec p := rfl

/-- The query embedding is the query token plus the query position. -/
theorem input_none (x : Fin n → Bool) :
    θ.input x none = θ.embedding.tokenVec 2 + θ.embedding.posVec none := rfl

/-- The query embedding does not depend on the input. -/
theorem input_none_const (x y : Fin n → Bool) : θ.input x none = θ.input y none := rfl

@[simp] theorem head_WV (h : Fin H) : (θ.head h).WV = (θ.WV h).toAffineMap := rfl

@[simp] theorem head_WO (h : Fin H) : (θ.head h).WO = θ.WO h := rfl

/-- Head scores are plain dot products of queries and keys. -/
theorem head_scores (h : Fin H) (X : MechInterp.Stream (SeqPos n) (Vec d)) :
    (θ.head h).scores (ScoreRule.standard 1) X X =
      fun i j => ⟪θ.WQ h (X i), θ.WK h (X j)⟫_ℝ := by
  funext i j
  simp [AttentionHead.scores, AttentionHead.queries, AttentionHead.keys, head]

/-- One head's output at destination `i`, via MechInterp's `AttentionHead.result_eq_resultWith`
and `AttentionHead.resultWith_apply`. -/
theorem head_result_apply (M : Mask (SeqPos n) (SeqPos n))
    (ρ : PatternRule (SeqPos n) (SeqPos n) M) (X : MechInterp.Stream (SeqPos n) (Vec d))
    (i : SeqPos n) (h : Fin H) :
    (θ.head h).result (ScoreRule.standard 1) ρ X X i =
      θ.WO h (∑ j, (ρ.toPattern fun i j => ⟪θ.WQ h (X i), θ.WK h (X j)⟫_ℝ).A i j •
        θ.WV h (X j)) := by
  rw [AttentionHead.result_eq_resultWith, AttentionHead.resultWith_apply, AttentionHead.pattern,
    head_scores, map_sum]
  simp only [head_WO, head_WV, LinearMap.coe_toAffineMap, map_smul]

/-- The attention layer at destination `i`, for any mask and rule, as a sum of head
outputs. -/
theorem attentionWith_eval (M : Mask (SeqPos n) (SeqPos n))
    (ρ : PatternRule (SeqPos n) (SeqPos n) M) (X : MechInterp.Stream (SeqPos n) (Vec d))
    (i : SeqPos n) :
    (θ.attentionWith M ρ).eval X X i =
      ∑ h, θ.WO h (∑ j, (ρ.toPattern fun i j => ⟪θ.WQ h (X i), θ.WK h (X j)⟫_ℝ).A i j •
        θ.WV h (X j)) := by
  simp only [MultiHead.eval, attentionWith, MultiHead.uniform, MultiHead.headResult, zero_add]
  exact Finset.sum_congr rfl fun h _ => θ.head_result_apply M ρ X i h

theorem queryWeight_eq_fullRule (h : Fin H) (x : Fin n → Bool) (j : SeqPos n) :
    θ.queryWeight h x j =
      ((fullRule n).toPattern fun i j =>
        ⟪θ.WQ h (θ.input x i), θ.WK h (θ.input x j)⟫_ℝ).A none j := by
  rw [fullRule_A]; rfl

/-- **Query residual.** The query residual is the query embedding plus the head outputs. -/
theorem residual_none (x : Fin n → Bool) :
    θ.residual x none = θ.input x none + ∑ h, θ.headOutput h x := by
  simp only [residual, residualWith, Pi.add_apply, attentionWith_eval, headOutput,
    queryWeight_eq_fullRule]

/-- **Literal score.** `S(x) = ⟪w, u_q + ∑ h, W_O^{(h)} ∑ j, A^{(h)}_{qj} W_V^{(h)} u_j⟫ - τ`. -/
theorem score_eq (x : Fin n → Bool) :
    θ.score x = ⟪θ.w, θ.input x none + ∑ h, θ.headOutput h x⟫_ℝ - θ.τ := by
  rw [score, residual_none]

theorem score_eq_sum (x : Fin n → Bool) :
    θ.score x = ⟪θ.w, θ.input x none⟫_ℝ + ∑ h, ⟪θ.w, θ.headOutput h x⟫_ℝ - θ.τ := by
  rw [score_eq, inner_add_right, inner_sum]

/-- The causal residual agrees with the full residual at the query. -/
theorem causalResidual_none (x : Fin n → Bool) :
    θ.causalResidual x none = θ.residual x none := by
  simp only [causalResidual, residual, residualWith, Pi.add_apply, attentionWith_eval,
    causalRule_A_none]

/-- **Causal and full masks agree at the query readout.** -/
theorem causalScore_eq_score (x : Fin n → Bool) : θ.causalScore x = θ.score x := by
  rw [causalScore, score, causalResidual_none]

/-- The causal variant computes exactly the same functions. -/
theorem computes_iff_causal (f : (Fin n → Bool) → Bool) :
    θ.Computes f ↔ ∀ x, 0 < θ.causalScore x ↔ f x = true := by
  simp only [Computes, causalScore_eq_score]

theorem headDenominator_pos (h : Fin H) (x : Fin n → Bool) : 0 < θ.headDenominator h x :=
  Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty

/-- The query-row weights are the softmax of the query logits. -/
theorem queryWeight_eq_softmax (h : Fin H) (x : Fin n → Bool) :
    θ.queryWeight h x = softmax (θ.queryLogit h x) := rfl

theorem queryWeight_pos (h : Fin H) (x : Fin n → Bool) (j : SeqPos n) :
    0 < θ.queryWeight h x j := by
  rw [queryWeight_eq_softmax]; exact softmax_pos _ _

theorem sum_queryWeight (h : Fin H) (x : Fin n → Bool) : ∑ j, θ.queryWeight h x j = 1 := by
  rw [queryWeight_eq_softmax]; exact softmax_sum_one _

/-- A head output is the projected softmax numerator divided by the denominator. -/
theorem headOutput_eq (h : Fin H) (x : Fin n → Bool) :
    θ.headOutput h x = (θ.headDenominator h x)⁻¹ • θ.WO h (θ.headNumerator h x) := by
  rw [headOutput, headNumerator, ← map_smul, Finset.smul_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_smul, queryWeight, headDenominator, div_eq_inv_mul]

end LiteralParams

end Xorformer

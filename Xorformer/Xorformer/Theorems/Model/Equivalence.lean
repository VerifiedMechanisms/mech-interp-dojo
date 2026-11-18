import Xorformer.Definitions.Model.Conversions
import Xorformer.Definitions.Model.Computability
import Xorformer.Theorems.Model.Literal
import Xorformer.Theorems.Model.Head
import MechInterp.Algebra.Blocks

set_option linter.style.header false

/-!
# Literal and reduced models have the same expressivity at every head count

* `Conversion.*`: the block maps are isometric, and their retractions invert them.
* `LiteralParams.computesPred_toReduced`: a literal model of widths `(d, dh)` gives a reduced
  family of width `d + dh` with the same head count. Queries and keys are padded
  isometrically; `W_O` moves through the weighted sum; the constant query residual is
  absorbed into the threshold.
* `toLiteral_computes`: a reduced family of width `d` gives a literal model with
  `dModel = H·d + 1` and `dHead = d + 1`, both positive.
* `computableWithHeads_iff_reduced`, `HStar_eq_ReducedHStar`: equivalence at every head
  count, and therefore equal minima. These results change width; they are not fixed-width
  equivalences.
-/

namespace Xorformer

open MechInterp
open scoped InnerProductSpace

namespace Conversion

theorem firstOut_firstIn (a b : ℕ) (v : Vec a) : firstOut a b (firstIn a b v) = v := by
  simp [firstOut, firstIn]

theorem inner_firstIn (a b : ℕ) (u v : Vec a) :
    ⟪firstIn a b u, firstIn a b v⟫_ℝ = ⟪u, v⟫_ℝ := by
  simp [firstIn]

theorem inner_secondIn (a b : ℕ) (u v : Vec b) :
    ⟪secondIn a b u, secondIn a b v⟫_ℝ = ⟪u, v⟫_ℝ := by
  simp [secondIn]

theorem blockOut_blockIn {H d : ℕ} (h : Fin H) (v : Vec d) : blockOut h (blockIn h v) = v := by
  simp [blockOut, blockIn]

theorem blockOut_blockIn_of_ne {H d : ℕ} {h h' : Fin H} (hne : h' ≠ h) (v : Vec d) :
    blockOut h' (blockIn h v) = 0 := by
  simp [blockOut, blockIn, Block.projProd_injProd_of_ne hne]

theorem blockOut_blockConcat {H d : ℕ} (v : Fin H → Vec d) (h : Fin H) :
    blockOut h (blockConcat v) = v h := by
  simp [blockOut, blockConcat]

theorem blockConcat_add {H d : ℕ} (v v' : Fin H → Vec d) :
    blockConcat (fun h => v h + v' h) = blockConcat v + blockConcat v' := by
  have hc : Block.concatProd (fun h => v h + v' h) =
      Block.concatProd v + Block.concatProd v' := by
    ext k; rfl
  simp [blockConcat, hc]

theorem inner_blockIn_blockIn {H d : ℕ} (h' h : Fin H) (a b : Vec d) :
    ⟪blockIn h' a, blockIn h b⟫_ℝ = if h' = h then ⟪a, b⟫_ℝ else 0 := by
  have key : ⟪blockIn h' a, blockIn h b⟫_ℝ =
      ⟪(Block.injProd h' : Vec d →ₗᵢ[ℝ] RVec (Fin H × Fin d)) a, Block.injProd h b⟫_ℝ := by
    simp [blockIn]
  rw [key, Block.inner_injProd_left]
  split_ifs with hh
  · subst hh; rw [Block.projProd_injProd]
  · rw [Block.projProd_injProd_of_ne hh, inner_zero_right]

theorem inner_toLiteralReadout_blockIn {H d : ℕ} (w a : Vec d) (h : Fin H) :
    ⟪toLiteralReadout (H := H) w, blockIn h a⟫_ℝ = ⟪w, a⟫_ℝ := by
  rw [toLiteralReadout, sum_inner, Finset.sum_eq_single h]
  · rw [inner_blockIn_blockIn, if_pos rfl]
  · intro h' _ hne; rw [inner_blockIn_blockIn, if_neg hne]
  · intro hh; exact absurd (Finset.mem_univ h) hh

end Conversion

open Conversion

/-! ## Literal to reduced -/

namespace LiteralParams

variable {n H d dh : ℕ} (θ : LiteralParams n H d dh)

theorem toReducedHead_x (h : Fin H) (bits : Fin n → Bool) (p : SeqPos n) :
    (θ.toReducedHead h).x bits p = firstIn d dh (θ.input bits p) := by
  simp only [Head.x, toReducedHead, input_apply, map_add]

theorem toReducedHead_sigma (h : Fin H) (bits : Fin n → Bool) (p : SeqPos n) :
    (θ.toReducedHead h).sigma bits p = Real.exp (θ.queryLogit h bits p) := by
  simp only [Head.sigma, toReducedHead_x]
  simp only [toReducedHead, LinearMap.comp_apply, firstOut_firstIn, inner_secondIn, queryLogit]
  rw [real_inner_comm]

theorem toReducedHead_value (h : Fin H) (bits : Fin n → Bool) (p : SeqPos n) :
    (θ.toReducedHead h).value bits p = firstIn d dh (θ.WO h (θ.WV h (θ.input bits p))) := by
  simp only [Head.value, toReducedHead_x]
  simp only [toReducedHead, LinearMap.comp_apply, firstOut_firstIn]

theorem toReducedHead_attnUpdate (h : Fin H) (bits : Fin n → Bool) :
    (θ.toReducedHead h).attnUpdate bits = firstIn d dh (θ.headOutput h bits) := by
  rw [Head.attnUpdate, Head.numerator, Head.denominator, headOutput_eq, map_smul]
  congr 1
  · simp only [toReducedHead_sigma, headDenominator]
  · simp only [toReducedHead_sigma, toReducedHead_value, headNumerator, map_sum, map_smul]

theorem toReduced_attnUpdate (bits : Fin n → Bool) :
    headFamilyAttnUpdate θ.toReduced bits = firstIn d dh (∑ h, θ.headOutput h bits) := by
  simp only [headFamilyAttnUpdate, toReduced, toReducedHead_attnUpdate, map_sum]

/-- The reduced readout equals the literal score up to the absorbed constant. -/
theorem reducedReadout_inner (bits : Fin n → Bool) :
    ⟪θ.reducedReadout, headFamilyAttnUpdate θ.toReduced bits⟫_ℝ - θ.reducedThreshold =
      θ.score bits := by
  rw [toReduced_attnUpdate, reducedReadout, inner_firstIn, reducedThreshold, score_eq,
    input_none]
  simp only [inner_add_right]
  ring

/-- **Literal to reduced.** A literal model with `H` heads gives a reduced family with `H`
heads computing the same function. -/
theorem computesPred_toReduced {f : (Fin n → Bool) → Bool} (hθ : θ.Computes f) :
    computesPred f (headFamilyAttnUpdate θ.toReduced) := by
  refine ⟨θ.reducedReadout, θ.reducedThreshold, fun bits => ?_⟩
  rw [← hθ bits, ← reducedReadout_inner, gt_iff_lt, sub_pos]

end LiteralParams

/-! ## Reduced to literal -/

section ReducedToLiteral

variable {n d H : ℕ} (Hs : HeadFamily n d H) (w : Vec d) (τ : ℝ)

@[simp] theorem toLiteral_WQ (h : Fin H) :
    (toLiteral Hs w τ).WQ h = firstIn d 1 ∘ₗ (Hs h).WQ ∘ₗ blockOut h := rfl

@[simp] theorem toLiteral_WK (h : Fin H) :
    (toLiteral Hs w τ).WK h = firstIn d 1 ∘ₗ (Hs h).WK ∘ₗ blockOut h := rfl

@[simp] theorem toLiteral_WV (h : Fin H) :
    (toLiteral Hs w τ).WV h = firstIn d 1 ∘ₗ (Hs h).WV ∘ₗ blockOut h := rfl

@[simp] theorem toLiteral_WO (h : Fin H) :
    (toLiteral Hs w τ).WO h = blockIn h ∘ₗ firstOut d 1 := rfl

theorem toLiteral_input (bits : Fin n → Bool) (p : SeqPos n) :
    (toLiteral Hs w τ).input bits p = blockConcat fun h => (Hs h).x bits p := by
  rw [LiteralParams.input_apply]
  simp only [toLiteral, toLiteralEmbedding, AdditiveEmbedding.tokenVec_ofFunctions,
    AdditiveEmbedding.posVec_ofFunctions, Head.x]
  exact (blockConcat_add _ _).symm

theorem blockOut_toLiteral_input (h : Fin H) (bits : Fin n → Bool) (p : SeqPos n) :
    blockOut h ((toLiteral Hs w τ).input bits p) = (Hs h).x bits p := by
  rw [toLiteral_input, blockOut_blockConcat]

theorem toLiteral_queryLogit (h : Fin H) (bits : Fin n → Bool) (p : SeqPos n) :
    (toLiteral Hs w τ).queryLogit h bits p =
      ⟪(Hs h).WK ((Hs h).x bits p), (Hs h).WQ ((Hs h).x bits none)⟫_ℝ := by
  simp only [LiteralParams.queryLogit, toLiteral_WQ, toLiteral_WK, LinearMap.comp_apply,
    blockOut_toLiteral_input, inner_firstIn]
  rw [real_inner_comm]

theorem toLiteral_headOutput (h : Fin H) (bits : Fin n → Bool) :
    (toLiteral Hs w τ).headOutput h bits = blockIn h ((Hs h).attnUpdate bits) := by
  rw [LiteralParams.headOutput_eq, Head.attnUpdate, map_smul]
  have hden : (toLiteral Hs w τ).headDenominator h bits = (Hs h).denominator bits := by
    simp only [LiteralParams.headDenominator, toLiteral_queryLogit, Head.denominator, Head.sigma]
  have hnum : (toLiteral Hs w τ).WO h ((toLiteral Hs w τ).headNumerator h bits) =
      blockIn h ((Hs h).numerator bits) := by
    simp only [LiteralParams.headNumerator, toLiteral_queryLogit, map_sum, map_smul,
      Head.numerator, Head.sigma, Head.value]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [toLiteral_WV, toLiteral_WO, LinearMap.comp_apply, blockOut_toLiteral_input,
      firstOut_firstIn]
  rw [hden, hnum]

/-- The score of the widened literal model is the reduced readout. -/
theorem toLiteral_score (bits : Fin n → Bool) :
    (toLiteral Hs w τ).score bits = ⟪w, headFamilyAttnUpdate Hs bits⟫_ℝ - τ := by
  rw [LiteralParams.score_eq_sum]
  simp only [toLiteral_headOutput]
  have hq : (toLiteral Hs w τ).input bits none =
      (toLiteralEmbedding Hs).tokenVec 2 + (toLiteralEmbedding Hs).posVec none := rfl
  have hw : (toLiteral Hs w τ).w = toLiteralReadout w := rfl
  simp only [hw, inner_toLiteralReadout_blockIn, hq]
  rw [headFamilyAttnUpdate, inner_sum]
  simp only [toLiteral]
  ring

/-- **Reduced to literal.** A reduced family with `H` heads and readout `(w, τ)` gives a
literal model with `H` heads computing the same function. -/
theorem toLiteral_computes {f : (Fin n → Bool) → Bool}
    (hf : ∀ bits, ⟪w, headFamilyAttnUpdate Hs bits⟫_ℝ > τ ↔ f bits = true) :
    (toLiteral Hs w τ).Computes f := by
  intro bits
  rw [toLiteral_score, sub_pos, ← gt_iff_lt]
  exact hf bits

end ReducedToLiteral

/-! ## Equivalence and equal minima -/

variable {n : ℕ}

theorem reducedComputableWithHeads_of_computableWithHeads {H : ℕ} {f : (Fin n → Bool) → Bool}
    (h : ComputableWithHeads n H f) : reducedComputableWithHeads n H f := by
  obtain ⟨d, dh, -, -, θ, hθ⟩ := h
  exact ⟨d + dh, θ.toReduced, θ.computesPred_toReduced hθ⟩

theorem computableWithHeads_of_reducedComputableWithHeads {H : ℕ}
    {f : (Fin n → Bool) → Bool} (h : reducedComputableWithHeads n H f) :
    ComputableWithHeads n H f := by
  obtain ⟨d, Hs, w, τ, hf⟩ := h
  exact ⟨H * d + 1, d + 1, Nat.succ_pos _, Nat.succ_pos _, toLiteral Hs w τ,
    toLiteral_computes Hs w τ hf⟩

/-- **Per-head-count equivalence** of the literal and reduced models (width may change). -/
theorem computableWithHeads_iff_reduced (H : ℕ) (f : (Fin n → Bool) → Bool) :
    ComputableWithHeads n H f ↔ reducedComputableWithHeads n H f :=
  ⟨reducedComputableWithHeads_of_computableWithHeads,
    computableWithHeads_of_reducedComputableWithHeads⟩

theorem exactHeadComplexity_iff_reduced (f : (Fin n → Bool) → Bool) (k : ℕ) :
    ExactHeadComplexity n f k ↔ reducedExactHeadComplexity n f k := by
  simp only [ExactHeadComplexity, reducedExactHeadComplexity, computableWithHeads_iff_reduced]

/-- **Equal minima.** The literal head complexity equals the reduced head complexity. -/
theorem HStar_eq_ReducedHStar (f : (Fin n → Bool) → Bool) : HStar n f = ReducedHStar n f := by
  classical
  have hiff : ∀ k, ComputableWithHeads n k f ↔ reducedComputableWithHeads n k f :=
    fun k => computableWithHeads_iff_reduced k f
  unfold HStar ReducedHStar
  by_cases hex : ∃ k, reducedComputableWithHeads n k f
  · have hexL : ∃ k, ComputableWithHeads n k f := hex.imp fun k => (hiff k).mpr
    rw [dif_pos hexL, dif_pos hex]
    exact le_antisymm (Nat.find_min' hexL ((hiff _).mpr (Nat.find_spec hex)))
      (Nat.find_min' hex ((hiff _).mp (Nat.find_spec hexL)))
  · have hexL : ¬ ∃ k, ComputableWithHeads n k f := fun ⟨k, hk⟩ => hex ⟨k, (hiff k).mp hk⟩
    rw [dif_neg hexL, dif_neg hex]

end Xorformer

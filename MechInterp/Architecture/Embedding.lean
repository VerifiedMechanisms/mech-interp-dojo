/-
Copyright (c) 2026 Malhar A. Patel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Malhar A. Patel
-/
import MechInterp.Algebra.Spaces

/-!
# Token encoders and additive embeddings

A transformer reads its input as a sequence of tokens, one per position, and turns that sequence
into a residual stream. This file defines both steps.

## Main definitions

* `Encoder In P T`: a map from task inputs to token sequences, `In → (P → T)`.
* `AdditiveEmbedding T P V`: a token embedding `W_E : ℝ^T → V` and a positional embedding
  `W_P : ℝ^P → V`, both *linear maps out of one-hot spaces*.
* `AdditiveEmbedding.embed E tok`: the stream `X_i = W_E δ_{tok i} + W_P δ_i`.
* `AdditiveEmbedding.ofFunctions e p` builds an embedding from token vectors `e t` and position
  vectors `p i`; `AdditiveEmbedding.tokenOnly e` has no positional part.

## Main results

* `embed_apply`: `X_i = e_{tok i} + p_i`.
* `embed_tokenOnly_comp`: without positional information, relabeling positions relabels the
  stream.

## Implementation notes

Treating embeddings as linear maps, rather than as lookup functions `T → V`, makes "full circuits"
such as `W_U ∘ W_O ∘ W_V ∘ W_E` ordinary compositions of linear maps. Attention layers take
arbitrary streams as input, so embeddings are never part of the attention parameters.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

namespace MechInterp

/-- A token encoder: for each task input, the token at each position. -/
abbrev Encoder (In P T : Type*) := In → P → T

/-- Token and positional embeddings, as linear maps out of the one-hot spaces `ℝ^T` and
`ℝ^P`. -/
structure AdditiveEmbedding (T P V : Type*) [AddCommGroup V] [Module ℝ V] where
  /-- The token embedding `W_E`. -/
  WE : RVec T →ₗ[ℝ] V
  /-- The positional embedding `W_P`. -/
  WP : RVec P →ₗ[ℝ] V

namespace AdditiveEmbedding

variable {T P V In : Type*} [AddCommGroup V] [Module ℝ V] [Fintype T] [DecidableEq T]
  [Fintype P] [DecidableEq P]

/-! ### Embedding a sequence -/

/-- The embedding vector `e_t = W_E δ_t` of a token `t`. -/
noncomputable def tokenVec (E : AdditiveEmbedding T P V) (t : T) : V := E.WE (RVec.oneHot t)

/-- The positional vector `p_i = W_P δ_i` of a position `i`. -/
noncomputable def posVec (E : AdditiveEmbedding T P V) (i : P) : V := E.WP (RVec.oneHot i)

/-- The embedded stream of a token sequence: `X_i = e_{tok i} + p_i`. -/
noncomputable def embed (E : AdditiveEmbedding T P V) (tok : P → T) : Stream P V :=
  fun i => E.tokenVec (tok i) + E.posVec i

/-- The embedded stream of an encoded input, `x ↦ embed (enc x)`. -/
noncomputable def embedInput (E : AdditiveEmbedding T P V) (enc : Encoder In P T) :
    In → Stream P V :=
  fun x => E.embed (enc x)

@[simp] theorem embed_apply (E : AdditiveEmbedding T P V) (tok : P → T) (i : P) :
    E.embed tok i = E.tokenVec (tok i) + E.posVec i := rfl

@[simp] theorem embedInput_apply (E : AdditiveEmbedding T P V) (enc : Encoder In P T) (x : In) :
    E.embedInput enc x = E.embed (enc x) := rfl

/-! ### Constructing embeddings -/

/-- The additive embedding with token vectors `e t` and position vectors `p i`. -/
noncomputable def ofFunctions (e : T → V) (p : P → V) : AdditiveEmbedding T P V :=
  ⟨RVec.linearOfFun e, RVec.linearOfFun p⟩

/-- An embedding with token vectors `e t` and no positional information (`p_i = 0`). -/
noncomputable def tokenOnly (e : T → V) : AdditiveEmbedding T P V := ofFunctions e fun _ => 0

/-- `ofFunctions e p` has token vectors `e`. -/
@[simp] theorem tokenVec_ofFunctions (e : T → V) (p : P → V) (t : T) :
    (ofFunctions e p).tokenVec t = e t := by
  simp [tokenVec, ofFunctions]

/-- `ofFunctions e p` has position vectors `p`. -/
@[simp] theorem posVec_ofFunctions (e : T → V) (p : P → V) (i : P) :
    (ofFunctions e p).posVec i = p i := by
  simp [posVec, ofFunctions]

/-- A token-only embedding has zero position vectors. -/
@[simp] theorem posVec_tokenOnly (e : T → V) (i : P) :
    (tokenOnly e : AdditiveEmbedding T P V).posVec i = 0 := by
  simp [tokenOnly]

/-- **Relabeling equivariance.** Without positional information, embedding the relabeled
sequence `tok ∘ π` gives the relabeled stream `embed tok ∘ π`. -/
theorem embed_tokenOnly_comp {P' : Type*} [Fintype P'] [DecidableEq P'] (e : T → V)
    (tok : P → T) (π : P' → P) :
    (tokenOnly e : AdditiveEmbedding T P' V).embed (tok ∘ π) =
      (tokenOnly e : AdditiveEmbedding T P V).embed tok ∘ π := by
  funext i
  simp [tokenOnly]

end AdditiveEmbedding

end MechInterp

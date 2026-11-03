import MechInterp.Theorems.Algebra.Spaces

set_option linter.style.header false

/-!
# Encoders and embeddings

An encoder maps a task input to a token at each position. Token and positional embeddings
are linear maps out of one-hot spaces, `W_E : ℝ^T → V` and `W_P : ℝ^P → V`, so full circuits
such as `W_U W_O W_V W_E` are plain compositions. The additive embedding is
`X_i = W_E δ_{tok i} + W_P δ_i`.

Attention and later modules accept arbitrary streams; embeddings are never part of attention
parameters.
-/

namespace MechInterp

/-- A token encoder: the token at each position of an input. -/
abbrev Encoder (In P T : Type*) := In → P → T

/-- Token and positional embeddings as linear maps out of one-hot spaces. -/
structure AdditiveEmbedding (T P V : Type*) [AddCommGroup V] [Module ℝ V] where
  /-- Token embedding `W_E`. -/
  WE : RVec T →ₗ[ℝ] V
  /-- Positional embedding `W_P`. -/
  WP : RVec P →ₗ[ℝ] V

namespace AdditiveEmbedding

variable {T P V In : Type*} [AddCommGroup V] [Module ℝ V] [Fintype T] [DecidableEq T]
  [Fintype P] [DecidableEq P]

/-- The embedding vector `e_t = W_E δ_t` of a token. -/
noncomputable def tokenVec (E : AdditiveEmbedding T P V) (t : T) : V := E.WE (RVec.oneHot t)

/-- The positional vector `p_i = W_P δ_i`. -/
noncomputable def posVec (E : AdditiveEmbedding T P V) (i : P) : V := E.WP (RVec.oneHot i)

/-- The embedded stream of a token sequence. -/
noncomputable def embed (E : AdditiveEmbedding T P V) (tok : P → T) : Stream P V :=
  fun i => E.tokenVec (tok i) + E.posVec i

/-- The embedded stream of an encoded input. -/
noncomputable def embedInput (E : AdditiveEmbedding T P V) (enc : Encoder In P T) :
    In → Stream P V :=
  fun x => E.embed (enc x)

/-- Build an additive embedding from token and position vectors. -/
noncomputable def ofFunctions (e : T → V) (p : P → V) : AdditiveEmbedding T P V :=
  ⟨RVec.linearOfFun e, RVec.linearOfFun p⟩

/-- An embedding without positional information. -/
noncomputable def tokenOnly (e : T → V) : AdditiveEmbedding T P V := ofFunctions e fun _ => 0

end AdditiveEmbedding

end MechInterp

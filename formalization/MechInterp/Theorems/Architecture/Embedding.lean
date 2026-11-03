import MechInterp.Definitions.Architecture.Embedding

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Embedding identities
-/

namespace MechInterp

namespace AdditiveEmbedding

variable {T P V In : Type*} [AddCommGroup V] [Module ℝ V] [Fintype T] [DecidableEq T]
  [Fintype P] [DecidableEq P]

@[simp] theorem embed_apply (E : AdditiveEmbedding T P V) (tok : P → T) (i : P) :
    E.embed tok i = E.tokenVec (tok i) + E.posVec i := rfl

@[simp] theorem embedInput_apply (E : AdditiveEmbedding T P V) (enc : Encoder In P T) (x : In) :
    E.embedInput enc x = E.embed (enc x) := rfl

@[simp] theorem tokenVec_ofFunctions (e : T → V) (p : P → V) (t : T) :
    (ofFunctions e p).tokenVec t = e t := by
  simp [tokenVec, ofFunctions]

@[simp] theorem posVec_ofFunctions (e : T → V) (p : P → V) (i : P) :
    (ofFunctions e p).posVec i = p i := by
  simp [posVec, ofFunctions]

@[simp] theorem posVec_tokenOnly (e : T → V) (i : P) :
    (tokenOnly e : AdditiveEmbedding T P V).posVec i = 0 := by
  simp [tokenOnly]

/-- A token-only embedding is equivariant under relabeling positions. -/
theorem embed_tokenOnly_comp {P' : Type*} [Fintype P'] [DecidableEq P'] (e : T → V)
    (tok : P → T) (π : P' → P) :
    (tokenOnly e : AdditiveEmbedding T P' V).embed (tok ∘ π) =
      (tokenOnly e : AdditiveEmbedding T P V).embed tok ∘ π := by
  funext i
  simp [tokenOnly]

end AdditiveEmbedding

end MechInterp

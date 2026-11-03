import Xorformer.Theorems.Model.Literal
import Xorformer.Theorems.Model.Head
import MechInterp.Theorems.Math.Square

set_option linter.style.header false

/-!
# Two-coordinate restrictions of literal heads (Theorems 1 and 2)

Fix all bits except `i ≠ j`. Any sum over positions whose term at `p` depends only on `p` and
the token at `p` satisfies the antipode identity
`T(0,0) + T(1,1) = T(0,1) + T(1,0)` (`tokenLocal_antipode`). Equivalently, it splits
additively as `A a + B b + C`. Within a literal head, the query embedding is constant, so the
softmax numerator `∑ j, exp⟪W_Q u_q, W_K u_j⟫ W_V u_j` and the denominator are token-local
sums. The identities therefore hold for every head of the literal model.
-/

namespace Xorformer

open MechInterp
open scoped InnerProductSpace

variable {n : ℕ} {M : Type*} [AddCommGroup M]

/-- **Antipode identity for token-local sums.** -/
theorem tokenLocal_antipode (G : SeqPos n → Fin 3 → M) (base : Fin n → Bool) (i j : Fin n)
    (hij : i ≠ j) :
    (∑ p, G p (Head.seqTok (Head.restrictBits base i j (false, false)) p))
      + (∑ p, G p (Head.seqTok (Head.restrictBits base i j (true, true)) p)) =
    (∑ p, G p (Head.seqTok (Head.restrictBits base i j (false, true)) p))
      + (∑ p, G p (Head.seqTok (Head.restrictBits base i j (true, false)) p)) := by
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  cases p with
  | none => rfl
  | some k =>
      by_cases hk : k = i
      · subst hk
        simp [Head.seqTok, Head.restrictBits]
      · by_cases hj : k = j
        · subst hj
          simp [Head.seqTok, Head.restrictBits, hk, add_comm]
        · simp [Head.seqTok, Head.restrictBits, hk, hj]

/-- **Additive split for token-local sums.** -/
theorem tokenLocal_additive_split (G : SeqPos n → Fin 3 → M) (base : Fin n → Bool)
    (i j : Fin n) (hij : i ≠ j) :
    ∃ (A B : Bool → M) (C : M), ∀ a b : Bool,
      ∑ p, G p (Head.seqTok (Head.restrictBits base i j (a, b)) p) = A a + B b + C :=
  boolSquare_additive_split_of_antipode
    (fun a b => ∑ p, G p (Head.seqTok (Head.restrictBits base i j (a, b)) p))
    (tokenLocal_antipode G base i j hij)

namespace LiteralParams

variable {H d dh : ℕ} (θ : LiteralParams n H d dh)

/-- The softmax numerator of a literal head is a token-local sum. -/
theorem headNumerator_eq_tokenLocal (h : Fin H) (x : Fin n → Bool) :
    θ.headNumerator h x = ∑ p, (fun p t =>
      Real.exp ⟪θ.WQ h (θ.embedding.tokenVec 2 + θ.embedding.posVec none),
          θ.WK h (θ.embedding.tokenVec t + θ.embedding.posVec p)⟫_ℝ •
        θ.WV h (θ.embedding.tokenVec t + θ.embedding.posVec p)) p (Head.seqTok x p) := rfl

/-- The softmax denominator of a literal head is a token-local sum. -/
theorem headDenominator_eq_tokenLocal (h : Fin H) (x : Fin n → Bool) :
    θ.headDenominator h x = ∑ p, (fun p t =>
      Real.exp ⟪θ.WQ h (θ.embedding.tokenVec 2 + θ.embedding.posVec none),
          θ.WK h (θ.embedding.tokenVec t + θ.embedding.posVec p)⟫_ℝ) p (Head.seqTok x p) := rfl

/-- **Theorem 2 (numerator), literal model.** -/
theorem headNumerator_antipode (h : Fin H) (base : Fin n → Bool) (i j : Fin n) (hij : i ≠ j) :
    θ.headNumerator h (Head.restrictBits base i j (false, false))
      + θ.headNumerator h (Head.restrictBits base i j (true, true)) =
    θ.headNumerator h (Head.restrictBits base i j (false, true))
      + θ.headNumerator h (Head.restrictBits base i j (true, false)) := by
  exact tokenLocal_antipode (M := Vec dh) (fun p t =>
    Real.exp ⟪θ.WQ h (θ.embedding.tokenVec 2 + θ.embedding.posVec none),
        θ.WK h (θ.embedding.tokenVec t + θ.embedding.posVec p)⟫_ℝ •
      θ.WV h (θ.embedding.tokenVec t + θ.embedding.posVec p)) base i j hij

/-- **Theorem 2 (denominator), literal model.** -/
theorem headDenominator_antipode (h : Fin H) (base : Fin n → Bool) (i j : Fin n)
    (hij : i ≠ j) :
    θ.headDenominator h (Head.restrictBits base i j (false, false))
      + θ.headDenominator h (Head.restrictBits base i j (true, true)) =
    θ.headDenominator h (Head.restrictBits base i j (false, true))
      + θ.headDenominator h (Head.restrictBits base i j (true, false)) := by
  exact tokenLocal_antipode (M := ℝ) (fun p t =>
    Real.exp ⟪θ.WQ h (θ.embedding.tokenVec 2 + θ.embedding.posVec none),
        θ.WK h (θ.embedding.tokenVec t + θ.embedding.posVec p)⟫_ℝ) base i j hij

/-- **Theorem 1 (numerator), literal model.** -/
theorem headNumerator_additive_split (h : Fin H) (base : Fin n → Bool) (i j : Fin n)
    (hij : i ≠ j) :
    ∃ (A B : Bool → Vec dh) (C : Vec dh), ∀ a b : Bool,
      θ.headNumerator h (Head.restrictBits base i j (a, b)) = A a + B b + C := by
  exact tokenLocal_additive_split (M := Vec dh) (fun p t =>
    Real.exp ⟪θ.WQ h (θ.embedding.tokenVec 2 + θ.embedding.posVec none),
        θ.WK h (θ.embedding.tokenVec t + θ.embedding.posVec p)⟫_ℝ •
      θ.WV h (θ.embedding.tokenVec t + θ.embedding.posVec p)) base i j hij

/-- **Theorem 1 (denominator), literal model.** -/
theorem headDenominator_additive_split (h : Fin H) (base : Fin n → Bool) (i j : Fin n)
    (hij : i ≠ j) :
    ∃ (α β : Bool → ℝ) (γ : ℝ), ∀ a b : Bool,
      θ.headDenominator h (Head.restrictBits base i j (a, b)) = α a + β b + γ := by
  exact tokenLocal_additive_split (M := ℝ) (fun p t =>
    Real.exp ⟪θ.WQ h (θ.embedding.tokenVec 2 + θ.embedding.posVec none),
        θ.WK h (θ.embedding.tokenVec t + θ.embedding.posVec p)⟫_ℝ) base i j hij

end LiteralParams

end Xorformer

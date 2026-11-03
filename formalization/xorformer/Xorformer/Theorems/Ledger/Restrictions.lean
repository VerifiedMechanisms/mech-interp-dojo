import Xorformer.Theorems.Model.Restrictions
import Xorformer.Theorems.Model.Computability
import Xorformer.Theorems.Results.RestrictionLowerBounds

set_option linter.style.header false

/-!
# Ledger 1–3: two-coordinate restrictions of the literal model

1. **Additive decomposition.** On a two-coordinate restriction, the softmax numerator and
   denominator of every literal head split as `A a + B b + C`.
2. **Antipode identities.** Equivalently, `T(0,0) + T(1,1) = T(0,1) + T(1,0)` for both.
3. **Checkerboard obstruction.** A checkerboard restriction rules out zero and one literal
   heads, so `2 ≤ HStar n f`.
-/

namespace Xorformer

open MechInterp

variable {n : ℕ}

/-- **Theorem 1 (numerator).** -/
theorem literal_numerator_additive_split {H d dh : ℕ} (θ : LiteralParams n H d dh) (h : Fin H)
    (base : Fin n → Bool) (i j : Fin n) (hij : i ≠ j) :
    ∃ (A B : Bool → Vec dh) (C : Vec dh), ∀ a b : Bool,
      θ.headNumerator h (Head.restrictBits base i j (a, b)) = A a + B b + C :=
  θ.headNumerator_additive_split h base i j hij

/-- **Theorem 1 (denominator).** -/
theorem literal_denominator_additive_split {H d dh : ℕ} (θ : LiteralParams n H d dh)
    (h : Fin H) (base : Fin n → Bool) (i j : Fin n) (hij : i ≠ j) :
    ∃ (α β : Bool → ℝ) (γ : ℝ), ∀ a b : Bool,
      θ.headDenominator h (Head.restrictBits base i j (a, b)) = α a + β b + γ :=
  θ.headDenominator_additive_split h base i j hij

/-- **Theorem 2 (numerator).** -/
theorem literal_numerator_antipode {H d dh : ℕ} (θ : LiteralParams n H d dh) (h : Fin H)
    (base : Fin n → Bool) (i j : Fin n) (hij : i ≠ j) :
    θ.headNumerator h (Head.restrictBits base i j (false, false))
      + θ.headNumerator h (Head.restrictBits base i j (true, true)) =
    θ.headNumerator h (Head.restrictBits base i j (false, true))
      + θ.headNumerator h (Head.restrictBits base i j (true, false)) :=
  θ.headNumerator_antipode h base i j hij

/-- **Theorem 2 (denominator).** -/
theorem literal_denominator_antipode {H d dh : ℕ} (θ : LiteralParams n H d dh) (h : Fin H)
    (base : Fin n → Bool) (i j : Fin n) (hij : i ≠ j) :
    θ.headDenominator h (Head.restrictBits base i j (false, false))
      + θ.headDenominator h (Head.restrictBits base i j (true, true)) =
    θ.headDenominator h (Head.restrictBits base i j (false, true))
      + θ.headDenominator h (Head.restrictBits base i j (true, false)) :=
  θ.headDenominator_antipode h base i j hij

/-- A nonconstant function is not computed by zero literal heads. -/
theorem not_computableWithHeads_zero_of_false_true (f : (Fin n → Bool) → Bool)
    (bitsFalse bitsTrue : Fin n → Bool) (hFalse : f bitsFalse = false)
    (hTrue : f bitsTrue = true) : ¬ ComputableWithHeads n 0 f := by
  rw [computableWithHeads_iff_reduced]
  exact not_reducedComputableWithHeads_zero_of_false_true f bitsFalse bitsTrue hFalse hTrue

/-- **Theorem 3 (one head).** A checkerboard restriction cannot be computed by one literal
head. -/
theorem checkerboard_not_computableWithHeads_one (f : (Fin n → Bool) → Bool)
    (base : Fin n → Bool) (i j : Fin n) (hij : i ≠ j) (c : Bool)
    (h00 : f (Head.restrictBits base i j (false, false)) = c)
    (h11 : f (Head.restrictBits base i j (true, true)) = c)
    (h01 : f (Head.restrictBits base i j (false, true)) = !c)
    (h10 : f (Head.restrictBits base i j (true, false)) = !c) :
    ¬ ComputableWithHeads n 1 f := by
  rw [computableWithHeads_iff_reduced]
  exact checkerboard_restriction_not_computable_with_one_head f base i j hij c h00 h11 h01 h10

/-- **Theorem 3.** A checkerboard restriction forces `H* ≥ 2`. -/
theorem checkerboard_HStar_ge_two (f : (Fin n → Bool) → Bool) (base : Fin n → Bool)
    (i j : Fin n) (hij : i ≠ j)
    (h00 : f (Head.restrictBits base i j (false, false)) = false)
    (h11 : f (Head.restrictBits base i j (true, true)) = false)
    (h01 : f (Head.restrictBits base i j (false, true)) = true)
    (h10 : f (Head.restrictBits base i j (true, false)) = true) :
    2 ≤ HStar n f := by
  rw [HStar_eq_ReducedHStar]
  exact checkerboard_restriction_ReducedHStar_ge_two f base i j hij h00 h11 h01 h10

end Xorformer

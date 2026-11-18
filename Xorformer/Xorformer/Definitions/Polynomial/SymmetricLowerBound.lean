import Xorformer.Definitions.Prelude
import Xorformer.Definitions.Polynomial.ModelToPolynomial
import Xorformer.Definitions.BooleanCube.SymmetricSignChanges
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Order.IntermediateValue

set_option linter.style.header false

/-!
# L12 lower bound chain.

This module holds the definitions of this part of the development. Their proofs are in
`Xorformer.Theorems.Polynomial.SymmetricLowerBound`.

Assembling `ReducedHStar n (symmetricFn F) ≥ signChanges n F` from:
* `signReprDegLe_of_reducedComputableWithHeads` (L6): `H` heads → degree-≤H sign rep;
* strictification (here): turn `0 < eval ↔ f` into a strict sign representation;
* symmetrization (here): average over `Equiv.Perm` to a symmetric polynomial;
* univariate reduction (`Polynomial/UnivariateReduction.lean`): a symmetric polynomial of
  total degree `≤ H` on the cube is a univariate polynomial of degree `≤ H` in the
  Hamming weight (no multilinearity assumed — on the cube any polynomial reduces);
* `signChanges_le_natDegree` (`Polynomial/UnivariateSignChanges.lean`): degree ≥ sign changes.

The chain is complete: `signChanges_le_of_reducedComputableWithHeads`
(`Polynomial/UnivariateReduction.lean`) discharges the lower bound, and together with the
upper bound it yields the unconditional `ReducedHStar_symmetricFn` in
`Results/SymmetricComplexity.lean`.
-/

namespace Xorformer

open MechInterp
open MvPolynomial

variable {n : ℕ}

/-- Strict sign representation: positive on true points, negative on false points. -/
def StrictSignRep (P : MvPolynomial (Fin n) ℝ) (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ x, (f x = true → 0 < eval (cubePoint x) P) ∧ (f x = false → eval (cubePoint x) P < 0)

/-! ## Symmetrization (Phase 3a) -/

open scoped BigOperators

/-- Average over all coordinate permutations. -/
noncomputable def symmetrize (P : MvPolynomial (Fin n) ℝ) : MvPolynomial (Fin n) ℝ :=
  ∑ σ : Equiv.Perm (Fin n), rename σ P

end Xorformer

import Xorformer.Definitions.Prelude
import Xorformer.Definitions.BooleanCube.Families

set_option linter.style.header false

/-!
# Symmetric sign changes.

This module holds the definitions of this part of the development. Their proofs are in
`Xorformer.Theorems.BooleanCube.SymmetricSignChanges`.

For a symmetric Boolean function `f(x) = F(|x|)`, the final theorem
`ReducedHStar_symmetricFn` in `Results/SymmetricComplexity.lean` states that the head complexity
equals
the number of sign changes of the profile `F` along the Hamming-weight axis:

$$ H^{*}(f) = C(F) := \#\{ t \in \{1,\dots,n\} : F(t-1) \neq F(t) \}. $$

This file contains the profile-level definitions and elementary checkerboard
consequences used by that theorem:

* `symmetricFn F` and the sign-change count `signChanges n F = C(F)`;
* the general-`n` lower bound that a *width-1 spike* in `F`
  (`F w = F (w+2) ≠ F (w+1)`) forces `H^{*} ≥ 2`, via the checkerboard engine.
  This single theorem subsumes the parity and exact-count lower bounds;
* the parity sign-change count `signChanges_parity`.
-/

namespace Xorformer

open MechInterp
open scoped BigOperators
open Head (restrictBits)

variable {n : ℕ}

/-- A symmetric Boolean function: its value depends only on the Hamming weight,
through a profile `F : ℕ → Bool`. -/
def symmetricFn (F : ℕ → Bool) (bits : Fin n → Bool) : Bool :=
  F (hammingWeight bits)

/-- The number of sign changes of the weight profile `F` along `0, 1, …, n`. -/
def signChanges (n : ℕ) (F : ℕ → Bool) : ℕ :=
  ((Finset.range n).filter fun t => F t ≠ F (t + 1)).card

/-! ## A base of prescribed off-coordinate weight -/

/-! ## General-`n` lower bound from a width-1 spike -/

/-! ## Sign-change counts -/

/-! ## Theorem 12

The full Theorem 12 is the equality

  `ReducedHStar n (symmetricFn F) = signChanges n F`,

proved unconditionally in `Results/SymmetricComplexity.lean` (`ReducedHStar_symmetricFn`): its
lower bound
is built in `Polynomial/SymmetricLowerBound.lean` + `Polynomial/UnivariateReduction.lean` (model →
threshold degree → symmetrize → univariate root count) and its upper bound is the
explicit `signChanges`-many-head softmax construction in `Atoms/SignPolynomial.lean` +
`MechInterp.Math.PartialFraction` + `Atoms/HammingAtom.lean`.

What this file contributes is the first nontrivial slice of that lower bound: a
*width-1 spike* in `F` simultaneously forces `signChanges n F ≥ 2`
(`signChanges_ge_two_of_spike`) and `¬ reducedComputableWithHeads n 1 (symmetricFn F)`
(`symmetricFn_spike_not_computable_with_one_head`), i.e. `H^{*} ≥ 2`. Combined
with `signChanges_parity = n`, the parity end of the spectrum (`C = n`) is in
place on the combinatorial side, and its `≥ 2` complexity bound on the model
side. -/

end Xorformer

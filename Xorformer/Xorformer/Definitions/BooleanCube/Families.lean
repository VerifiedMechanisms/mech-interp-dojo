import Xorformer.Definitions.Prelude
import Xorformer.Definitions.Model.Head

set_option linter.style.header false

/-!
# Symmetric families: parity and exact-count lower bounds.

This module holds the definitions of this part of the development. Their proofs are in
`Xorformer.Theorems.BooleanCube.Families`.

This file defines the `n`-bit symmetric functions `PARITY` and `EXACT`, and
proves checkerboard lower bounds used by the current L1-L12 theorem stack:

* `PARITY n` needs at least two heads for `n ≥ 2`;
* `EXACT n k` needs at least two heads for `1 ≤ k ≤ n - 1`.

Both follow from the reusable general-`n` checkerboard engine in
`Model/Head.lean` (`parity_restriction_not_computable_with_one_head`,
`not_reducedComputableWithHeads_zero_of_false_true`). The only new work is the
elementary Hamming-weight bookkeeping under a two-coordinate restriction. Exact
values for these families are proved later from the symmetric sign-change
characterization in `Results/ExactFamilies.lean`.
-/

namespace Xorformer

open MechInterp
open scoped BigOperators
open Head (restrictBits)

variable {n : ℕ}

/-- Hamming weight: the number of `true` coordinates of an `n`-bit input. -/
def hammingWeight (bits : Fin n → Bool) : ℕ :=
  (Finset.univ.filter fun i => bits i = true).card

/-- `n`-bit parity (XOR of all bits), packaged as a Boolean function. -/
def PARITY (n : ℕ) (bits : Fin n → Bool) : Bool :=
  decide (Odd (hammingWeight bits))

/-- `EXACT n k`: true iff exactly `k` of the `n` input bits are set. -/
def EXACT (n k : ℕ) (bits : Fin n → Bool) : Bool :=
  decide (hammingWeight bits = k)

/-! ## Parity -/

/-! ## Exact-count predicates -/

end Xorformer

import Xorformer.Definitions.Prelude
import Xorformer.Definitions.Atoms.HammingAtom
import MechInterp.Definitions.Math.Polynomial
import Xorformer.Definitions.Atoms.SignPolynomial
import Xorformer.Definitions.Polynomial.UnivariateReduction

set_option linter.style.header false

/-!
# Exact head complexity of the standard symmetric families (L4, L5, L8).

This module holds the definitions of this part of the development. Their proofs are in
`Xorformer.Theorems.Results.ExactFamilies`.

Corollaries of the symmetric sign-change characterization
`ReducedHStar_symmetricFn : ReducedHStar n (symmetricFn F) = signChanges n F` (Theorem 12):
once the head complexity of a symmetric function is its profile's sign-change
count, the standard families reduce to a sign-change computation.

* **Theorem 8** `ReducedHStar n (PARITY n) = n` — parity's profile alternates, so `C = n`.
* **Theorem 4** `ReducedHStar n (THRESHOLD n t) = 1` for `1 ≤ t ≤ n` — a monotone threshold
  profile has a single sign change at `t-1`.
* **Theorem 5 (exact)** `ReducedHStar n (EXACT n k) = 2` for `1 ≤ k ≤ n-1` — an internal
  spike profile changes sign twice, at `k-1` and `k`.
-/

namespace Xorformer

open MechInterp
open Finset

variable {n : ℕ}

/-- The monotone symmetric threshold `T_{n,t}(x) = [|x| ≥ t]` as a symmetric function. -/
def THRESHOLD (n t : ℕ) : (Fin n → Bool) → Bool := symmetricFn (fun k => decide (t ≤ k))

/-! ## Sign-change counts of the standard profiles -/

/-! ## Exact head complexities -/

end Xorformer

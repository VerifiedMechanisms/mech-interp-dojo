import Xorformer.Definitions.Prelude
import Xorformer.Definitions.Polynomial.UnivariateReduction
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option linter.style.header false

/-!
# L12 upper bound: one head realizes one linear-fractional atom.

This module holds the definitions of this part of the development. Their proofs are in
`Xorformer.Theorems.Atoms.HammingAtom`.

Following the linear-fractional normal form, each attention head whose scores
depend only on the token type contributes, under a fixed readout, a term
`b / (k + a)` in the Hamming weight `k = |x|`.  We build such a head explicitly
with `d = 2` and `W_Q = W_K = W_V = id`, pushing all structure into the token
embedding:

* coordinate `0` is the **score** channel, coordinate `1` the **value** channel;
* `tokenEmbed 0 = (0, b/n)`, `tokenEmbed 1 = (log 2 / s, b/(2n))`,
  `tokenEmbed 2 = (s, 0)` with `s = sqrt (log (a - n))`.

Then the softmax weight at a bit position is `1` (bit `0`) or `2` (bit `1`), the
query weight is `a - n`, the denominator is `(n-k)·1 + k·2 + (a-n) = k + a`, and
the readout `⟪e₁, ·⟫` of the numerator is the constant `b`.  Hence
`⟪e₁, attnUpdate x⟫ = b / (k + a)`.  The same readout `e₁` adds the atoms of
several heads, so a partial-fraction decomposition of the sign pattern gives the
full `C(F)`-head construction.
-/

namespace Xorformer

open MechInterp
open MvPolynomial Finset Head
open scoped BigOperators InnerProductSpace

variable {n : ℕ}

/-- Token embedding of the atom head for parameters `a, b` over `n` bits. -/
noncomputable def atomTok (n : ℕ) (a b : ℝ) : Fin 3 → Vec 2 :=
  ![ EuclideanSpace.single 1 (b / n),
     EuclideanSpace.single 0 (Real.log 2 / Real.sqrt (Real.log (a - n)))
       + EuclideanSpace.single 1 (b / (2 * n)),
     EuclideanSpace.single 0 (Real.sqrt (Real.log (a - n))) ]

/-- The atom head: scores depend only on the token, values live in coordinate 1. -/
noncomputable def atomHead (n : ℕ) (a b : ℝ) : Head n 2 where
  tokenEmbed := atomTok n a b
  posEmbed := fun _ => 0
  WQ := LinearMap.id
  WK := LinearMap.id
  WV := LinearMap.id

/-- The shared readout vector `e₁`. -/
noncomputable def atomReadout : Vec 2 := EuclideanSpace.single 1 1

section
variable (a b : ℝ)

end

/-! ## Softmax weights, denominator, numerator readout -/

section
variable (a b : ℝ) (hn : 1 ≤ n) (ha : (n : ℝ) + 1 < a)

include ha in
include ha in
include ha in
include ha in
include ha in
include ha in
include hn ha in
include hn ha in
end

end Xorformer

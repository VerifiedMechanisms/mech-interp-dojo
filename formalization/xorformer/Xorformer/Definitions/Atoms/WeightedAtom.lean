import Xorformer.Definitions.Prelude
import Xorformer.Definitions.Atoms.HammingAtom
import MechInterp.Math.PartialFraction
import MechInterp.Architecture.Softmax
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Algebra.BigOperators.Fin

set_option linter.style.header false

/-!
# Weighted-sum interpolation construction.

This module holds the definitions of this part of the development. Their proofs are in
`Xorformer.Theorems.Atoms.WeightedAtom`.

If `f(x) = F(t(x))` for a positive weighted sum `t(x) = ∑ λ_i x_i` with image of
size `M`, then `f` is computable with `M - 1` heads. The `H*` corollaries live
in `Results/WeightedUpperBound.lean`.

The head construction generalizes `atomHead`: with `d = 2`, `W_Q = W_K = W_V = id`,
score channel `0`, value channel `1`, and `s = √(log (a - Λ))` (`Λ = ∑ λ_i`):

* `posEmbed (some i) = single 0 (log λ_i / s)` injects `log λ_i` into position `i`'s
  logit, so the softmax weight there is `λ_i` (bit 0) or `2 λ_i` (bit 1);
* the query token has logit `s² = log (a - Λ)`, weight `a - Λ`.

Hence the denominator is `∑_i (λ_i + λ_i x_i) + (a - Λ) = t(x) + a`, and the readout
`⟪e₁, ·⟫` of the numerator is the constant `b`, so `⟪e₁, attnUpdate x⟫ = b/(t(x)+a)`.
Reusing `real_partial_fraction` and a Lagrange sign polynomial gives the `M-1` heads.
-/

namespace Xorformer

open MechInterp
open MvPolynomial Finset Head
open scoped BigOperators InnerProductSpace

variable {n : ℕ}

/-- Total weight `Λ = ∑ λ_i`. -/
noncomputable def wLam (lam : Fin n → ℝ) : ℝ := ∑ i, lam i

/-- Weighted statistic `t(x) = ∑_{i : x_i} λ_i`. -/
noncomputable def wT (lam : Fin n → ℝ) (bits : Fin n → Bool) : ℝ := ∑ i, if bits i then lam i else 0

/-- Score scale `s = √(log (a - Λ))`. -/
noncomputable def wScore (lam : Fin n → ℝ) (a : ℝ) : ℝ := Real.sqrt (Real.log (a - wLam lam))

/-- Token embedding of the weighted atom head. -/
noncomputable def wTok (lam : Fin n → ℝ) (a b : ℝ) : Fin 3 → Vec 2 :=
  ![ EuclideanSpace.single 1 (b / wLam lam),
     EuclideanSpace.single 0 (Real.log 2 / wScore lam a)
       + EuclideanSpace.single 1 (b / (2 * wLam lam)),
     EuclideanSpace.single 0 (wScore lam a) ]

/-- Positional embedding: position `i` carries `log λ_i / s` in the score channel. -/
noncomputable def wPos (lam : Fin n → ℝ) (a : ℝ) : SeqPos n → Vec 2
  | some i => EuclideanSpace.single 0 (Real.log (lam i) / wScore lam a)
  | none => 0

/-- The weighted atom head over `n` bits. -/
noncomputable def weightedAtomHead (lam : Fin n → ℝ) (a b : ℝ) : Head n 2 where
  tokenEmbed := wTok lam a b
  posEmbed := wPos lam a
  WQ := LinearMap.id
  WK := LinearMap.id
  WV := LinearMap.id

section
variable (lam : Fin n → ℝ) (a b : ℝ)

end

section
variable (lam : Fin n → ℝ) (a b : ℝ) (hn : 1 ≤ n) (hlam : ∀ i, 0 < lam i)
  (ha : wLam lam + 1 < a)

include hn hlam in
include ha in
include ha in
include ha in
include ha in
include ha in
include hlam ha in
include hlam ha in
include hn hlam ha in
include hn hlam ha in
end

/-! ## Universal computability: every function is computable -/

end Xorformer

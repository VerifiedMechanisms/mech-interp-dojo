import Xorformer.Definitions.Prelude
import Xorformer.Definitions.Atoms.WeightedAtom

set_option linter.style.header false

/-!
# Affine functionals are computable with one head.

This module holds the definitions of this part of the development. Their proofs are in
`Xorformer.Theorems.Atoms.AffineHead`.

If a Boolean function `f` is sign-represented by an affine functional
`c + ∑ i, cs i * x i` (with `x i = boolToReal (bits i)`), then `f` is computed by
a single attention head.

The construction uses `d = n + 1` with `W_Q = W_K = W_V = id`:

* coordinate `0` is the **score** channel;
* coordinate `i.succ` is the **private value** channel of input position `i`.

With `a i := cs i + τ` and `τ := (∑ j, cs j - c) / Real.exp 1`:

* `tokenEmbed 0 = 0`, `tokenEmbed 1 = single 0 (log 2)`, `tokenEmbed 2 = single 0 1`;
* `posEmbed (some i) = single i.succ (a i)`, `posEmbed none = 0`.

The query `x_=` is `single 0 1`, so its only nonzero coordinate is the score
channel.  Hence the softmax weight at position `i` is `2` (bit set) or `1`
(bit clear), and `exp 1` at the query.  The readout
`w = ∑ i, single i.succ 1` reads value channel `i.succ`, which holds `a i`, so
`⟪w, numerator⟫ = ∑ j, a j * (1 + boolToReal (bits j))`.  The sign identity
`⟪w, numerator⟫ - τ * denominator = c + ∑ i, cs i * boolToReal (bits i)`
then transfers the affine sign condition to the head readout.
-/

namespace Xorformer

open MechInterp
open Finset Head
open scoped BigOperators InnerProductSpace

variable {n : ℕ}

/-- The affine coefficients `a i = cs i + τ`. -/
noncomputable def affCoeff (cs : Fin n → ℝ) (c : ℝ) : Fin n → ℝ :=
  fun i => cs i + (∑ j, cs j - c) / Real.exp 1

/-- The threshold `τ = (∑ j, cs j - c) / exp 1`. -/
noncomputable def affTau (cs : Fin n → ℝ) (c : ℝ) : ℝ :=
  (∑ j, cs j - c) / Real.exp 1

/-- Token embedding of the affine head. -/
noncomputable def affTok : Fin 3 → Vec (n + 1) :=
  ![ 0,
     EuclideanSpace.single 0 (Real.log 2),
     EuclideanSpace.single 0 1 ]

/-- Positional embedding: position `i` carries `a i` in its private value channel. -/
noncomputable def affPos (cs : Fin n → ℝ) (c : ℝ) : SeqPos n → Vec (n + 1)
  | some i => EuclideanSpace.single i.succ (affCoeff cs c i)
  | none => 0

/-- The affine head over `n` bits. -/
noncomputable def affHead (cs : Fin n → ℝ) (c : ℝ) : Head n (n + 1) where
  tokenEmbed := affTok
  posEmbed := affPos cs c
  WQ := LinearMap.id
  WK := LinearMap.id
  WV := LinearMap.id

/-- The readout vector `w = ∑ i, single i.succ 1`. -/
noncomputable def affReadout (n : ℕ) : Vec (n + 1) := ∑ i : Fin n, EuclideanSpace.single i.succ 1

section
variable (cs : Fin n → ℝ) (c : ℝ)

end

/-! ## Coordinate readings -/

section
variable (cs : Fin n → ℝ) (c : ℝ)

end

/-! ## Readout of value channels -/

section
variable (cs : Fin n → ℝ) (c : ℝ)

end

/-! ## Denominator, numerator readout, and the sign identity -/

section
variable (cs : Fin n → ℝ) (c : ℝ)

end

/-! ## Assembly -/

end Xorformer

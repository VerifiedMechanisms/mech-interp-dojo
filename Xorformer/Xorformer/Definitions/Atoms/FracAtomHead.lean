import Xorformer.Definitions.Prelude
import Xorformer.Definitions.Atoms.FracAtom
import Xorformer.Definitions.Atoms.HammingAtom
import Xorformer.Definitions.Model.SharedEmbedding
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option linter.style.header false

/-!
# Theorem 10 (one direction) — every linear-fractional atom is one head.

This module holds the definitions of this part of the development. Their proofs are in
`Xorformer.Theorems.Atoms.FracAtomHead`.

Given a `FracAtom φ` over `n` bits we build a single attention head
`atomHead' φ : Head n 3` whose readout under `w = e₁` is exactly `φ.eval`.
Summing such heads (all sharing the readout `e₁`) realizes any
`fracComputable` function, giving

```
computable_of_fracComputable : fracComputable n H f → reducedComputableWithHeads n H f
```

The construction uses `d = 3`.  Coordinate `0` is the **score** channel,
coordinate `1` the **value** channel, coordinate `2` a **query marker**.  The
value map is the identity `W_V = id`, while `W_K` and `W_Q` are coordinate
projections back into the score channel (using the identity for both would let
the value channel pollute the scores):

* `W_K x = single 0 (x 0)`  (read coordinate `0`),
* `W_Q x = single 0 (x 2)`  (read coordinate `2`).

The embeddings carry the atom's parameters in log-space so that the softmax
weights reproduce `φ.wt` and `φ.γ`:

* `tokenEmbed 0 = 0`,
  `tokenEmbed 1 = single 0 (log α) + single 1 δ`,
  `tokenEmbed 2 = single 0 (log γ) + single 1 (η/γ) + single 2 1`;
* `posEmbed (some i) = single 0 (log ρ_i) + single 1 (m_i)`, `posEmbed none = 0`.

The query marker `x_= 2 = 1`, so the score at position `p` is `(x_p) 0`, giving
softmax weight `ρ_i α^{x_i} = φ.wt` at a bit and `γ` at the query.  The readout
of the numerator is `η + ∑ φ.wt·(m_i + δ x_i)` and the denominator is
`γ + ∑ φ.wt`, so `⟪e₁, attnUpdate⟫ = φ.eval`.
-/

namespace Xorformer

open MechInterp
open Finset Head
open scoped BigOperators InnerProductSpace

variable {n : ℕ}

/-- A coordinate projection back into the score channel:
`projTo0 j x = single 0 (x j)` as a linear map on `Vec 3`. -/
noncomputable def projTo0 (j : Fin 3) : Vec 3 →ₗ[ℝ] Vec 3 :=
  (LinearMap.toSpanSingleton ℝ (Vec 3) (EuclideanSpace.single 0 1)).comp
    (EuclideanSpace.projₗ j)

/-! ## The atom head -/

/-- Token embedding of the one-atom head for the atom `φ` (`d = 3`). -/
noncomputable def fracTok (φ : FracAtom n) : Fin 3 → Vec 3 :=
  ![ 0,
     EuclideanSpace.single 0 (Real.log φ.α) + EuclideanSpace.single 1 φ.δ,
     EuclideanSpace.single 0 (Real.log φ.γ) + EuclideanSpace.single 1 (φ.η / φ.γ)
       + EuclideanSpace.single 2 1 ]

/-- Positional embedding of the one-atom head: position `i` carries
`log ρ_i` in the score channel and `m_i` in the value channel. -/
noncomputable def fracPos (φ : FracAtom n) : SeqPos n → Vec 3
  | some i => EuclideanSpace.single 0 (Real.log (φ.ρ i)) + EuclideanSpace.single 1 (φ.m i)
  | none => 0

/-- **One head realizing one atom.** -/
noncomputable def atomHead' (φ : FracAtom n) : Head n 3 where
  tokenEmbed := fracTok φ
  posEmbed := fracPos φ
  WQ := projTo0 2
  WK := projTo0 0
  WV := LinearMap.id

/-- The shared readout vector `e₁`. -/
noncomputable def fracReadout : Vec 3 := EuclideanSpace.single 1 1

section
variable (φ : FracAtom n)

/-! ### Coordinate readings of the embedded vectors -/

end

/-! ## Softmax weights -/

section
variable (φ : FracAtom n)

end

/-! ## Denominator and numerator readout -/

section
variable (φ : FracAtom n)

end

end Xorformer

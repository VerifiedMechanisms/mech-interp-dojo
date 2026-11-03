import Xorformer.Definitions.Prelude
import Xorformer.Definitions.Atoms.FracAtom
import Xorformer.Definitions.Polynomial.ModelToPolynomial

set_option linter.style.header false

/-!
# Clearing two fractional atoms

This module holds the definitions of this part of the development. Their proofs are in
`Xorformer.Theorems.Atoms.TwoHeadClearing`.

This module exposes the product structure hidden by the general model-to-polynomial
degree bound. Each fractional atom has an affine numerator and a positive affine
denominator on the Boolean cube. Clearing two positive denominators produces a
sum of two products of affine polynomials.
-/

namespace Xorformer

open MechInterp
open Finset MvPolynomial
open scoped BigOperators

namespace FracAtom

/-- The affine denominator polynomial of a fractional atom. -/
noncomputable def denPoly (φ : FracAtom n) : MvPolynomial (Fin n) ℝ :=
  C φ.γ + ∑ i, affineAt i (φ.ρ i) (φ.ρ i * φ.α)

/-- The affine numerator polynomial of a fractional atom. -/
noncomputable def numPoly (φ : FracAtom n) : MvPolynomial (Fin n) ℝ :=
  C φ.η + ∑ i, affineAt i (φ.ρ i * φ.m i)
    (φ.ρ i * φ.α * (φ.m i + φ.δ))

end FracAtom

end Xorformer

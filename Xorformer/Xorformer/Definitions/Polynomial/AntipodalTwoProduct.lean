import Xorformer.Definitions.Prelude
import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option linter.style.header false

/-!
# Antipodal two-product obstruction

This module holds the definitions of this part of the development. Their proofs are in
`Xorformer.Theorems.Polynomial.AntipodalTwoProduct`.

This file isolates the linear-algebra argument used by the strict-separation
result about antipodal slices ruling out every two-product affine sign representation.
-/

namespace Xorformer

open MechInterp
namespace AntipodalTwoProduct

open Finset
open scoped BigOperators

abbrev FiveBits := Fin 5 → Bool

/-- The centered real encoding of a bit. -/
def bitSign (b : Bool) : ℝ := if b then -1 else 1

/-- Flip every bit. -/
def bitAntipode (x : FiveBits) : FiveBits := fun i ↦ !(x i)

/-- The sign vector with a single negative coordinate. -/
def antipodalSlice (j : Fin 5) : FiveBits := fun i ↦ decide (i = j)

/-- An affine form on two blocks of five centered Boolean variables. -/
structure BiAffine where
  const : ℝ
  xCoeff : Fin 5 → ℝ
  yCoeff : Fin 5 → ℝ

namespace BiAffine

/-- Evaluation of a two-block affine form. -/
def eval (L : BiAffine) (x y : FiveBits) : ℝ :=
  L.const + ∑ i, L.xCoeff i * bitSign (x i) + ∑ j, L.yCoeff j * bitSign (y j)

/-- The homogeneous part in the first block. -/
def xPart (L : BiAffine) (x : FiveBits) : ℝ :=
  ∑ i, L.xCoeff i * bitSign (x i)

/-- The homogeneous part in the second block. -/
def yPart (L : BiAffine) (y : FiveBits) : ℝ :=
  ∑ j, L.yCoeff j * bitSign (y j)

end BiAffine

/-- A sum of two products of affine forms. -/
def twoProductScore (L₁ R₁ L₂ R₂ : BiAffine) (x y : FiveBits) : ℝ :=
  L₁.eval x y * R₁.eval x y + L₂.eval x y * R₂.eval x y

/-- The mixed antipodal difference of a two-block function. -/
def mixedAntipodalDifference (g : FiveBits → FiveBits → ℝ)
    (x y : FiveBits) : ℝ :=
  g x y - g x (bitAntipode y) - g (bitAntipode x) y
    + g (bitAntipode x) (bitAntipode y)

/-- The coefficient matrix of the five mixed slice differences. -/
def mixedCoefficientMatrix (L₁ R₁ L₂ R₂ : BiAffine) : Matrix (Fin 5) (Fin 5) ℝ :=
  fun i j ↦ 4 * (L₁.xCoeff i * R₁.yPart (antipodalSlice j)
    + R₁.xCoeff i * L₁.yPart (antipodalSlice j)
    + L₂.xCoeff i * R₂.yPart (antipodalSlice j)
    + R₂.xCoeff i * L₂.yPart (antipodalSlice j))

/-- The five-by-four matrix containing the four first-block coefficient vectors. -/
def mixedLeftFactor (L₁ R₁ L₂ R₂ : BiAffine) : Matrix (Fin 5) (Fin 4) ℝ :=
  fun i ↦ ![L₁.xCoeff i, R₁.xCoeff i, L₂.xCoeff i, R₂.xCoeff i]

/-- The four-by-five matrix of slice-dependent coefficients. -/
def mixedRightFactor (L₁ R₁ L₂ R₂ : BiAffine) : Matrix (Fin 4) (Fin 5) ℝ :=
  fun h j ↦ ![4 * R₁.yPart (antipodalSlice j), 4 * L₁.yPart (antipodalSlice j),
    4 * R₂.yPart (antipodalSlice j), 4 * L₂.yPart (antipodalSlice j)] h

/-- Choose signs that make every off-diagonal contribution nonpositive. -/
noncomputable def oppositeColumnInput (A : Matrix (Fin 5) (Fin 5) ℝ) (j : Fin 5) :
    FiveBits := fun i ↦ if i = j then false else decide (0 ≤ A i j)

/-- The antipodal-slice truth pattern used by the obstruction. -/
def HasFiveAntipodalSlices (f : FiveBits → FiveBits → Bool) : Prop :=
  ∀ x j,
    f x (antipodalSlice j) = !x j ∧
    f x (bitAntipode (antipodalSlice j)) = x j ∧
    f (bitAntipode x) (antipodalSlice j) = x j ∧
    f (bitAntipode x) (bitAntipode (antipodalSlice j)) = !x j

end AntipodalTwoProduct

end Xorformer

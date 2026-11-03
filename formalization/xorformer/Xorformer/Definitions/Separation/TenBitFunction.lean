import Xorformer.Definitions.Prelude
import Xorformer.Definitions.Atoms.TwoHeadClearing
import Xorformer.Definitions.Polynomial.AntipodalTwoProduct
import Xorformer.Definitions.Polynomial.ParityThresholdDegree
import Xorformer.Definitions.Atoms.FracAtomHead
import Xorformer.Definitions.Atoms.HeadToFracAtom
import Xorformer.Definitions.Polynomial.LinearThreshold
import Xorformer.Definitions.Atoms.WeightedAtom
import Xorformer.Definitions.Model.Head

set_option linter.style.header false

/-!
# Theorem 13: threshold degree is not head complexity

This module holds the definitions of this part of the development. Their proofs are in
`Xorformer.Theorems.Results.StrictSeparation`.

Define `f10` by the sign of

`Q(x,y) = (∑ i, x i) * (∑ j, y j) - 3 * ∑ i, x i * y i`

for two blocks of five signed Boolean variables. The explicit quadratic gives
`thresholdDeg f10 = 2`. Five antipodal slices force full rank in every cleared
quadratic sign representation, while two attention heads can produce rank at
most four. Consequently `3 ≤ ReducedHStar 10 f10`.

Theorem 13 reuses the fractional normal form, clears two positive denominators,
and applies a five-dimensional antipodal rank obstruction. The auxiliary theorem
`f10QInt_mod_four` proves nonvanishing analytically, without an exhaustive
Boolean-cube computation.
-/

namespace Xorformer

open MechInterp
open MvPolynomial Finset
open AntipodalTwoProduct

/-- The first five coordinates of a ten-bit input. -/
def f10Left (z : Fin 10 → Bool) (i : Fin 5) : Bool :=
  z (Fin.castAdd 5 i)

/-- The last five coordinates of a ten-bit input. -/
def f10Right (z : Fin 10 → Bool) (i : Fin 5) : Bool :=
  z (Fin.natAdd 5 i)

/-- The ten-bit quadratic score
`(∑ xᵢ)(∑ yᵢ) - 3 ∑ xᵢyᵢ` in the `{±1}` encoding. -/
def f10Q (z : Fin 10 → Bool) : ℝ :=
  (∑ i : Fin 5, bitSign (f10Left z i)) *
      (∑ i : Fin 5, bitSign (f10Right z i)) -
    3 * ∑ i : Fin 5, bitSign (f10Left z i) * bitSign (f10Right z i)

/-- The Boolean function cut out by the positive values of `f10Q`. -/
noncomputable def f10 (z : Fin 10 → Bool) : Bool :=
  decide (0 < f10Q z)

/-- The affine polynomial representing one signed Boolean coordinate. -/
noncomputable def f10SpinPoly (j : Fin 10) : MvPolynomial (Fin 10) ℝ :=
  C 1 - C 2 * X j

/-- The multivariate polynomial corresponding to `f10Q`. -/
noncomputable def f10Poly : MvPolynomial (Fin 10) ℝ :=
  (∑ i : Fin 5, f10SpinPoly (Fin.castAdd 5 i)) *
      (∑ i : Fin 5, f10SpinPoly (Fin.natAdd 5 i)) -
    C 3 * ∑ i : Fin 5,
      f10SpinPoly (Fin.castAdd 5 i) * f10SpinPoly (Fin.natAdd 5 i)

/-- A two-dimensional face on which `f10` is XOR. -/
def f10CheckerBase : Fin 10 → Bool :=
  ![false, false, false, true, true,
    false, false, true, false, true]

/-! ## The two-head obstruction -/

/-- Join two five-bit blocks into the ten-bit model input. -/
def f10Join (x y : FiveBits) : Fin 10 → Bool :=
  fun i ↦ @Fin.addCases 5 5 (fun _ ↦ Bool) x y i

/-- Re-express a degree-at-most-one polynomial as a centered affine form on
the two five-bit blocks. -/
noncomputable def affinePolynomialToBiAffine
    (P : MvPolynomial (Fin 10) ℝ) : BiAffine where
  const := P.coeff 0
    + ∑ i : Fin 5, P.coeff (Finsupp.single (Fin.castAdd 5 i) 1) / 2
    + ∑ j : Fin 5, P.coeff (Finsupp.single (Fin.natAdd 5 j) 1) / 2
  xCoeff := fun i ↦ -P.coeff (Finsupp.single (Fin.castAdd 5 i) 1) / 2
  yCoeff := fun j ↦ -P.coeff (Finsupp.single (Fin.natAdd 5 j) 1) / 2

/-- The concrete target viewed as a function of two five-bit blocks. -/
noncomputable def f10Pair (x y : FiveBits) : Bool :=
  f10 (f10Join x y)

/-! The following integer certificate replaces the finite Python check that the
quadratic never vanishes. The proof is the identity
`Q = 10 + 4 * (-A - B + A * B - 3 * C)`, where `A`, `B`, and `C` are integer
bit counts. -/

def bitSignInt (b : Bool) : ℤ := if b then -1 else 1

def bitValueInt (b : Bool) : ℤ := if b then 1 else 0

def f10QInt (x y : FiveBits) : ℤ :=
  (∑ i, bitSignInt (x i)) * (∑ j, bitSignInt (y j)) -
    3 * ∑ i, bitSignInt (x i) * bitSignInt (y i)

end Xorformer

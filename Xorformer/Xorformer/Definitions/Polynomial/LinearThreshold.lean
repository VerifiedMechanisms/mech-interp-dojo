import Xorformer.Definitions.Prelude
import Xorformer.Definitions.Atoms.WeightedAtom
import Xorformer.Definitions.Atoms.AffineHead

set_option linter.style.header false

/-!
# Theorem 11 — exact characterization of the zero- and one-head levels.

This module holds the definitions of this part of the development. Their proofs are in
`Xorformer.Theorems.Results.LowComplexity`.

`H*(f) = 0 ⟺ f constant`, and `H*(f) = 1 ⟺ f is a nonconstant linear threshold
function`.  A linear threshold function is one sign-represented by an affine
functional (`isLTF`); this coincides with `ThresholdDegLE f 1`.

This file proves the parts not needing the affine-head construction: the
zero-head characterization (using that every function is computable, from the
Theorem 9 universal bound) and `isLTF`.  The one-head converse uses
`affine_computable` (the affine head, `Atoms/AffineHead.lean`).
-/

namespace Xorformer

open MechInterp
open Finset
open scoped BigOperators InnerProductSpace

variable {n : ℕ}

/-- `f` is a **linear threshold function**: its truth is the sign of an affine
functional of the bits. -/
def isLTF (f : (Fin n → Bool) → Bool) : Prop :=
  ∃ (c : ℝ) (cs : Fin n → ℝ),
    ∀ x : Fin n → Bool, (0 < c + ∑ i, cs i * boolToReal (x i)) ↔ f x = true

/-! ## Zero heads ⟺ constant -/

/-! ## Threshold degree `≤ 1` is exactly LTF -/

/-! ## The level-1 characterization -/

end Xorformer

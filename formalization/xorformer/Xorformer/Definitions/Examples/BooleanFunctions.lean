import Xorformer.Definitions.Prelude
import Xorformer.Definitions.Examples.TwoHeads

set_option linter.style.header false

/-!
# Boolean-function examples in the head-complexity model.

This module holds the definitions of this part of the development. Their proofs are in
`Xorformer.Theorems.Examples.BooleanFunctions`.

This file keeps a compact two-bit example layer: named Boolean functions,
explicit one- and two-head constructions, and the exact head-complexity
table for all symmetric two-bit functions.
-/

namespace Xorformer

open MechInterp
open scoped InnerProductSpace

variable {d : ℕ}

/-- A vector-valued two-bit function computes a Boolean target under a linear
readout. -/
def computesBool (f : (Fin 2 → Bool) → Bool) (g : (Fin 2 → Bool) → Vec d) : Prop :=
  computesPred f g

/-- Named versions of the standard 2-bit Boolean functions. -/
def falseFn : (Fin 2 → Bool) → Bool := fun _ => false
def trueFn : (Fin 2 → Bool) → Bool := fun _ => true
def orFn : (Fin 2 → Bool) → Bool := fun bits => bits 0 || bits 1
def andFn : (Fin 2 → Bool) → Bool := fun bits => bits 0 && bits 1
def norFn : (Fin 2 → Bool) → Bool := fun bits => !(orFn bits)
def nandFn : (Fin 2 → Bool) → Bool := fun bits => !(andFn bits)
def xnorFn : (Fin 2 → Bool) → Bool := fun bits => !(xorFn bits)

/-- The 2-bit symmetric Boolean function determined by its values on Hamming
weights `0`, `1`, and `2`. -/
def symmFn (c0 c1 c2 : Bool) : (Fin 2 → Bool) → Bool := fun bits =>
  match bits 0, bits 1 with
  | false, false => c0
  | false, true => c1
  | true, false => c1
  | true, true => c2

/-- Two-bit head families are just the model specialized to `n = 2`. -/
abbrev TwoBitHeadFamily (d H : ℕ) : Type := HeadFamily 2 d H

/-- The summed attention update of a two-bit head family. -/
noncomputable def twoBitHeadFamilyAttnUpdate {H : ℕ} (Hs : TwoBitHeadFamily d H) :
    (Fin 2 → Bool) → Vec d :=
  headFamilyAttnUpdate Hs

/-- Two-bit computability with `H` heads. -/
abbrev reducedComputableWithHeads2 (f : (Fin 2 → Bool) → Bool) (H : ℕ) : Prop :=
  reducedComputableWithHeads 2 H f

/-- Exact two-bit head complexity. -/
abbrev reducedExactHeadComplexity2 (f : (Fin 2 → Bool) → Bool) (k : ℕ) : Prop :=
  reducedExactHeadComplexity 2 f k

/-- Explicit two-bit head complexity value. -/
noncomputable def ReducedHStar2 (f : (Fin 2 → Bool) → Bool) : ℕ :=
  ReducedHStar 2 f

/-- A concrete 2-head family realizing the existing XOR construction. -/
noncomputable def xorTwoHeadFamily : TwoBitHeadFamily 3 2
  | 0 => head0
  | 1 => head1

end Xorformer

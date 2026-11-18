import Xorformer.Definitions.Prelude
import Xorformer.Definitions.Model.Head

set_option linter.style.header false

/-!
# Two-bit example helpers.

This module holds the definitions of this part of the development. Their proofs are in
`Xorformer.Theorems.Examples.TwoBit`.

The examples use the `Head` model directly.  This file keeps only
the lightweight two-bit notation: named Boolean functions on `Fin 2 → Bool` and
the XOR-specific readout predicate used by the endpoint examples.
-/

namespace Xorformer

open MechInterp
/-- The two-bit input with first bit `a` and second bit `b`. -/
def bits2 (a b : Bool) : Fin 2 → Bool
  | 0 => a
  | 1 => b

/-- XOR on two generalized-model input bits. -/
def xorFn : (Fin 2 → Bool) → Bool := fun bits => xor (bits 0) (bits 1)

/-- A vector-valued two-bit function computes XOR under a linear readout. -/
def computesXor {d : ℕ} (g : (Fin 2 → Bool) → Vec d) : Prop :=
  computesPred xorFn g

end Xorformer

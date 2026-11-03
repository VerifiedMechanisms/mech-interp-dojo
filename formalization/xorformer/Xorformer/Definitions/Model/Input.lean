import Xorformer.Definitions.Prelude

set_option linter.style.header false

/-!
# XORFormer inputs and their token encoding

An input is `x : Fin n → Bool`. The model reads the sequence `(x₁, …, xₙ, =)`. Its positions
are `SeqPos n = Option (Fin n)`: `some i` is bit `i` and `none` is the dedicated query token.
The vocabulary is `Fin 3`: `0` for a zero bit, `1` for a one bit, and `2` for the query token.
The explicit order `seqOrd` puts the query last; causal masks use it.
-/

namespace Xorformer

open MechInterp

/-- `n`-bit inputs. -/
abbrev Bits (n : ℕ) := Fin n → Bool

/-- Sequence positions: `some i` is input bit `i`, `none` is the query token. -/
abbrev SeqPos (n : ℕ) := Option (Fin n)

/-- The token for a zero bit. -/
def tokZero : Fin 3 := 0

/-- The token for a one bit. -/
def tokOne : Fin 3 := 1

/-- The query token `=`. -/
def tokQuery : Fin 3 := 2

/-- Token IDs of an input: each bit position holds token `0` or `1`, and the query position
holds token `2`. -/
def Head.seqTok {n : ℕ} (bits : Fin n → Bool) : SeqPos n → Fin 3
  | some i => cond (bits i) 1 0
  | none => 2

/-- The position order with the query last: bit `i` has order `i`, the query has order `n`. -/
def seqOrd {n : ℕ} : SeqPos n → ℕ
  | some i => i
  | none => n

end Xorformer

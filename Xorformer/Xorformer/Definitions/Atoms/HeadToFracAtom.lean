import Xorformer.Definitions.Prelude
import Xorformer.Definitions.Atoms.FracAtom
import Xorformer.Definitions.Model.Head

set_option linter.style.header false

/-!
# Theorem 10 (one direction): every head's readout is a linear-fractional atom.

This module holds the definitions of this part of the development. Their proofs are in
`Xorformer.Theorems.Atoms.HeadToFracAtom`.

A single attention head's readout `⟪w, attnUpdate⟫` is exactly the value of a
one-head linear-fractional atom (`FracAtom`).  Summing over a family of heads and
transferring the sign condition gives

`fracComputable_of_computable :
  reducedComputableWithHeads n H f → fracComputable n H f`.

The construction `headToAtom` reads off the atom parameters from the head and the
readout vector `w`.  The query embedding `x none = tokenEmbed 2 + posEmbed none`
is independent of the input bits, so the atom's `γ`, `η` (which reference it) are
well defined.
-/

namespace Xorformer

open MechInterp
open Finset Head
open scoped BigOperators InnerProductSpace

variable {n d : ℕ}

/-- The (bits-independent) query-side embedding `tokenEmbed 2 + posEmbed none`. -/
noncomputable def Head.queryVec (H : Head n d) : Vec d :=
  H.tokenEmbed 2 + H.posEmbed none

/-- The query vector after `W_Q`. -/
noncomputable def Head.queryQ (H : Head n d) : Vec d := H.WQ H.queryVec

/-- The linear-fractional atom realized by head `H` under readout `w`. -/
noncomputable def headToAtom (H : Head n d) (w : Vec d) : FracAtom n where
  η := Real.exp ⟪H.WK H.queryVec, H.queryQ⟫_ℝ * ⟪w, H.WV H.queryVec⟫_ℝ
  δ := ⟪w, H.WV (H.tokenEmbed 1 - H.tokenEmbed 0)⟫_ℝ
  γ := Real.exp ⟪H.WK H.queryVec, H.queryQ⟫_ℝ
  α := Real.exp ⟪H.WK (H.tokenEmbed 1 - H.tokenEmbed 0), H.queryQ⟫_ℝ
  ρ := fun i => Real.exp ⟪H.WK (H.tokenEmbed 0 + H.posEmbed (some i)), H.queryQ⟫_ℝ
  m := fun i => ⟪w, H.WV (H.tokenEmbed 0 + H.posEmbed (some i))⟫_ℝ
  hγ := Real.exp_pos _
  hα := Real.exp_pos _
  hρ := fun _ => Real.exp_pos _

section
variable (H : Head n d) (w : Vec d) (bits : Fin n → Bool)

end

end Xorformer

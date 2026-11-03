import Xorformer.Definitions.Atoms.FracAtom
import Xorformer.Theorems.Atoms.AffineHead

set_option linter.style.header false

/-!
# Theorem 10 — exact linear-fractional normal form.

The definitions used here are in `Xorformer.Definitions.Atoms.FracAtom`.

A **one-head atom** is a function
`φ(x) = (η + ∑ ρ_i α^{x_i}(m_i + δ x_i)) / (γ + ∑ ρ_i α^{x_i})` with `γ, ρ_i, α > 0`.
`L_frac(f)` is the least number of atoms whose sum, plus a constant, sign-represents
`f`.  Then `H*(f) = L_frac(f)`:

* every attention head's readout `⟪w, attnUpdate⟫ = (∑_p σ_p ⟪w, WV x_p⟫)/(∑_p σ_p)`
  is such an atom (Theorem 1, `fracComputable_of_computable`);
* every atom is realized by one head (Theorem 2, `computable_of_fracComputable`).

`α^{x_i}` is interpreted on the cube: `1` when `x_i = 0`, `α` when `x_i = 1`.
-/

namespace Xorformer

open MechInterp
open Finset
open scoped BigOperators InnerProductSpace

variable {n : ℕ}

namespace FracAtom

theorem wt_pos (φ : FracAtom n) (x : Fin n → Bool) (i : Fin n) : 0 < φ.wt x i := by
  have hr := φ.hρ i; have ha := φ.hα
  unfold wt; split <;> positivity

/-- The atom's denominator is positive. -/
theorem denom_pos (φ : FracAtom n) (x : Fin n → Bool) : 0 < φ.γ + ∑ i, φ.wt x i :=
  add_pos_of_pos_of_nonneg φ.hγ (Finset.sum_nonneg fun i _ => (φ.wt_pos x i).le)

end FracAtom

end Xorformer

import Xorformer.Definitions.Model.Literal

set_option linter.style.header false

/-!
# Head complexity of the literal model

`ComputableWithHeads n H f` says that some literal XORFormer with `H` heads computes `f`.
Its residual width `dModel` and head width `dHead` are positive, as `model.md` requires, and
otherwise unrestricted. `HStar n f` is the least such `H`. It is defined with `Nat.find` and
defaults to zero when no head count works; the theorem layer proves that every function is
computable and that the minimum is attained.
-/

namespace Xorformer

/-- Some literal XORFormer with `H` heads and positive widths computes `f`. -/
def ComputableWithHeads (n H : ℕ) (f : (Fin n → Bool) → Bool) : Prop :=
  ∃ d dh : ℕ, 0 < d ∧ 0 < dh ∧ ∃ θ : LiteralParams n H d dh, θ.Computes f

/-- `f` has exact head complexity `k`. -/
def ExactHeadComplexity (n : ℕ) (f : (Fin n → Bool) → Bool) (k : ℕ) : Prop :=
  ComputableWithHeads n k f ∧ ∀ h < k, ¬ ComputableWithHeads n h f

/-- The head complexity `H*(f)` of the literal model. -/
noncomputable def HStar (n : ℕ) (f : (Fin n → Bool) → Bool) : ℕ := by
  classical
  exact if h : ∃ k, ComputableWithHeads n k f then Nat.find h else 0

end Xorformer

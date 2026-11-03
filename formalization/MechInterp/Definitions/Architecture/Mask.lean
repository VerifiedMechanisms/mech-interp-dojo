import Mathlib.Data.Fintype.Basic
import Mathlib.Order.Basic

set_option linter.style.header false

/-!
# Attention masks

A mask is a decidable relation between destination and source positions. It is well formed
when every destination row allows at least one source. Causal, local-window, and prefix-LM
masks use an explicit order `ord : P → ℕ`, never an incidental order on the position type.
-/

namespace MechInterp

/-- A mask: which source positions each destination may attend to. -/
structure Mask (Pdst Psrc : Type*) where
  allowed : Pdst → Psrc → Prop
  [dec : ∀ i j, Decidable (allowed i j)]

attribute [instance] Mask.dec

namespace Mask

variable {Pdst Psrc P : Type*}

/-- Every destination row allows at least one source. -/
def WellFormed (M : Mask Pdst Psrc) : Prop := ∀ i, ∃ j, M.allowed i j

/-- Every position may attend to itself. -/
def ContainsDiag (M : Mask P P) : Prop := ∀ i, M.allowed i i

/-- The full mask. -/
def full : Mask Pdst Psrc := ⟨fun _ _ => True⟩

/-- The causal mask for an explicit order: `j` is visible from `i` when `ord j ≤ ord i`. -/
def causal (ord : P → ℕ) : Mask P P := ⟨fun i j => ord j ≤ ord i⟩

/-- A causal local window of width `w`: `ord i - w < ord j ≤ ord i`. -/
def window (ord : P → ℕ) (w : ℕ) : Mask P P := ⟨fun i j => ord j ≤ ord i ∧ ord i < ord j + w⟩

/-- Prefix-LM mask: full attention within the prefix, causal elsewhere. -/
def prefixLM (ord : P → ℕ) (isPrefix : P → Prop) [DecidablePred isPrefix] : Mask P P :=
  ⟨fun i j => (isPrefix i ∧ isPrefix j) ∨ ord j ≤ ord i⟩

/-- Intersection of masks. -/
def inter (M N : Mask Pdst Psrc) : Mask Pdst Psrc := ⟨fun i j => M.allowed i j ∧ N.allowed i j⟩

/-- The finite set of allowed sources of a destination. -/
def allowedSet [Fintype Psrc] (M : Mask Pdst Psrc) (i : Pdst) : Finset Psrc :=
  Finset.univ.filter (M.allowed i)

end Mask

end MechInterp

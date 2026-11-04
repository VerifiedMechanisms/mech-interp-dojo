/-
Copyright (c) 2026 Malhar A. Patel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Malhar A. Patel
-/
import Mathlib.Data.Fintype.Basic
import Mathlib.Order.Basic

/-!
# Attention masks

A mask says which source positions `j` each destination position `i` may attend to. Positions
are arbitrary types, so destination and source positions may differ, as in cross-attention.

## Main definitions

* `Mask Pdst Psrc`: a decidable relation `allowed i j` between destination and source positions.
* `Mask.WellFormed`: every destination row allows at least one source. This is the condition that
  makes softmax normalizers positive.
* `Mask.ContainsDiag`: every position may attend to itself.
* Standard masks: `Mask.full`, `Mask.causal ord`, `Mask.window ord w`, `Mask.prefixLM`, and the
  intersection `M.inter N`.
* `Mask.allowedSet M i`: the finite set of sources that `i` may attend to.

## Main results

* `wellFormed_of_containsDiag`: a mask containing the diagonal is well formed.
* The full, causal, positive-width window, and prefix-LM masks contain the diagonal, as does the
  intersection of two diagonal-containing masks. Hence they are well formed.

## Implementation notes

Causal, window, and prefix-LM masks take an explicit order `ord : P → ℕ` on positions instead of
relying on an incidental order of the position type. This keeps "which token comes first" a
visible modelling choice.
-/

namespace MechInterp

/-- A mask: which source positions each destination position may attend to. -/
structure Mask (Pdst Psrc : Type*) where
  /-- `allowed i j` holds when destination `i` may attend to source `j`. -/
  allowed : Pdst → Psrc → Prop
  /-- Membership in the mask is decidable, so allowed sets are computable finsets. -/
  [dec : ∀ i j, Decidable (allowed i j)]

attribute [instance] Mask.dec

namespace Mask

variable {Pdst Psrc P : Type*}

/-! ### Properties of masks -/

/-- A mask is **well formed** when every destination row allows at least one source. -/
def WellFormed (M : Mask Pdst Psrc) : Prop := ∀ i, ∃ j, M.allowed i j

/-- A self-attention mask **contains the diagonal** when every position may attend to itself. -/
def ContainsDiag (M : Mask P P) : Prop := ∀ i, M.allowed i i

/-- The finite set of sources that destination `i` may attend to. -/
def allowedSet [Fintype Psrc] (M : Mask Pdst Psrc) (i : Pdst) : Finset Psrc :=
  Finset.univ.filter (M.allowed i)

@[simp] theorem mem_allowedSet [Fintype Psrc] (M : Mask Pdst Psrc) (i : Pdst) (j : Psrc) :
    j ∈ M.allowedSet i ↔ M.allowed i j := by
  simp [allowedSet]

/-- A mask in which every position sees itself is well formed. -/
theorem wellFormed_of_containsDiag {M : Mask P P} (h : M.ContainsDiag) : M.WellFormed :=
  fun i => ⟨i, h i⟩

/-! ### Standard masks -/

/-- The full mask: every destination may attend to every source. -/
def full : Mask Pdst Psrc := ⟨fun _ _ => True⟩

/-- The causal mask for an explicit order `ord`: `j` is visible from `i` when `ord j ≤ ord i`. -/
def causal (ord : P → ℕ) : Mask P P := ⟨fun i j => ord j ≤ ord i⟩

/-- A causal local window of width `w`: `j` is visible from `i` when
`ord i - w < ord j ≤ ord i`. -/
def window (ord : P → ℕ) (w : ℕ) : Mask P P := ⟨fun i j => ord j ≤ ord i ∧ ord i < ord j + w⟩

/-- The prefix-LM mask: full attention among prefix positions, causal attention otherwise. -/
def prefixLM (ord : P → ℕ) (isPrefix : P → Prop) [DecidablePred isPrefix] : Mask P P :=
  ⟨fun i j => (isPrefix i ∧ isPrefix j) ∨ ord j ≤ ord i⟩

/-- The intersection of two masks: `j` is visible from `i` when both masks allow it. -/
def inter (M N : Mask Pdst Psrc) : Mask Pdst Psrc := ⟨fun i j => M.allowed i j ∧ N.allowed i j⟩

@[simp] theorem causal_allowed (ord : P → ℕ) (i j : P) :
    (causal ord).allowed i j ↔ ord j ≤ ord i := Iff.rfl

/-- A window mask only allows what the causal mask allows. -/
theorem window_le_causal (ord : P → ℕ) (w : ℕ) (i j : P) (h : (window ord w).allowed i j) :
    (causal ord).allowed i j :=
  h.1

/-! ### Well-formedness of the standard masks -/

/-- The full mask over a nonempty source type is well formed. -/
theorem full_wellFormed [Nonempty Psrc] : (full : Mask Pdst Psrc).WellFormed :=
  fun _ => ⟨Classical.arbitrary Psrc, trivial⟩

/-- The full self-attention mask contains the diagonal. -/
theorem full_containsDiag : (full : Mask P P).ContainsDiag := fun _ => trivial

/-- A causal mask contains the diagonal, since `ord i ≤ ord i`. -/
theorem causal_containsDiag (ord : P → ℕ) : (causal ord).ContainsDiag := fun _ => le_refl _

/-- A window of positive width contains the diagonal. -/
theorem window_containsDiag (ord : P → ℕ) {w : ℕ} (hw : 0 < w) : (window ord w).ContainsDiag :=
  fun _ => ⟨le_refl _, Nat.lt_add_of_pos_right hw⟩

/-- A prefix-LM mask contains the diagonal (through its causal part). -/
theorem prefixLM_containsDiag (ord : P → ℕ) (isPrefix : P → Prop) [DecidablePred isPrefix] :
    (prefixLM ord isPrefix).ContainsDiag :=
  fun _ => Or.inr (le_refl _)

/-- The intersection of two diagonal-containing masks contains the diagonal. -/
theorem inter_containsDiag {M N : Mask P P} (hM : M.ContainsDiag) (hN : N.ContainsDiag) :
    (M.inter N).ContainsDiag :=
  fun i => ⟨hM i, hN i⟩

/-- A causal mask is well formed. -/
theorem causal_wellFormed (ord : P → ℕ) : (causal ord).WellFormed :=
  wellFormed_of_containsDiag (causal_containsDiag ord)

/-- A window of positive width is well formed. -/
theorem window_wellFormed (ord : P → ℕ) {w : ℕ} (hw : 0 < w) : (window ord w).WellFormed :=
  wellFormed_of_containsDiag (window_containsDiag ord hw)

end Mask

end MechInterp

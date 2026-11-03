import MechInterp.Definitions.Architecture.Mask

set_option linter.style.header false

/-!
# Mask well-formedness

Masks containing the diagonal are well formed. Full masks on nonempty sources, causal masks,
positive-width windows, prefix-LM masks, and intersections of diagonal-containing masks all
contain the diagonal.
-/

namespace MechInterp

namespace Mask

variable {Pdst Psrc P : Type*}

theorem full_wellFormed [Nonempty Psrc] : (full : Mask Pdst Psrc).WellFormed :=
  fun _ => ⟨Classical.arbitrary Psrc, trivial⟩

theorem wellFormed_of_containsDiag {M : Mask P P} (h : M.ContainsDiag) : M.WellFormed :=
  fun i => ⟨i, h i⟩

theorem full_containsDiag : (full : Mask P P).ContainsDiag := fun _ => trivial

theorem causal_containsDiag (ord : P → ℕ) : (causal ord).ContainsDiag := fun _ => le_refl _

theorem window_containsDiag (ord : P → ℕ) {w : ℕ} (hw : 0 < w) : (window ord w).ContainsDiag :=
  fun _ => ⟨le_refl _, Nat.lt_add_of_pos_right hw⟩

theorem prefixLM_containsDiag (ord : P → ℕ) (isPrefix : P → Prop) [DecidablePred isPrefix] :
    (prefixLM ord isPrefix).ContainsDiag :=
  fun _ => Or.inr (le_refl _)

theorem inter_containsDiag {M N : Mask P P} (hM : M.ContainsDiag) (hN : N.ContainsDiag) :
    (M.inter N).ContainsDiag :=
  fun i => ⟨hM i, hN i⟩

theorem causal_wellFormed (ord : P → ℕ) : (causal ord).WellFormed :=
  wellFormed_of_containsDiag (causal_containsDiag ord)

theorem window_wellFormed (ord : P → ℕ) {w : ℕ} (hw : 0 < w) : (window ord w).WellFormed :=
  wellFormed_of_containsDiag (window_containsDiag ord hw)

@[simp] theorem mem_allowedSet [Fintype Psrc] (M : Mask Pdst Psrc) (i : Pdst) (j : Psrc) :
    j ∈ M.allowedSet i ↔ M.allowed i j := by
  simp [allowedSet]

@[simp] theorem causal_allowed (ord : P → ℕ) (i j : P) :
    (causal ord).allowed i j ↔ ord j ≤ ord i := Iff.rfl

theorem window_le_causal (ord : P → ℕ) (w : ℕ) (i j : P) (h : (window ord w).allowed i j) :
    (causal ord).allowed i j :=
  h.1

end Mask

end MechInterp

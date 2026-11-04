/-
Copyright (c) 2026 Malhar A. Patel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Malhar A. Patel
-/
import Mathlib.Algebra.Group.Basic
import Mathlib.Tactic.Abel

/-!
# Additive functions on the Boolean square

A function `f : Bool → Bool → A` into an abelian group is a 2 × 2 table of values. It splits as a
row term plus a column term plus a constant, `f a b = row a + col b + c`, exactly when its two
diagonals have the same sum:

  `f false false + f true true = f false true + f true false`.

We call the diagonal condition the *antipode identity*. XOR violates it, which is why it is the
basic obstruction for single attention heads.

## Main results

* `boolSquare_additive_split_of_antipode`: the antipode identity gives an additive split.
* `boolSquare_antipode_of_additive_split`: an additive split gives the antipode identity.
* `boolSquare_antipode_iff_additive_split`: the two conditions are equivalent.
-/

namespace MechInterp

/-- If the two diagonals of a Boolean-square table have the same sum, the table splits as
`row a + col b + c`. The witnesses are `row a = f a false`, `col b = f false b`, and
`c = -f false false`; three corners hold by definition and the fourth is the hypothesis. -/
theorem boolSquare_additive_split_of_antipode {A : Type*} [AddCommGroup A]
    (f : Bool → Bool → A)
    (hanti : f false false + f true true = f false true + f true false) :
    ∃ (row col : Bool → A) (c : A), ∀ a b : Bool, f a b = row a + col b + c := by
  refine ⟨fun a => f a false, fun b => f false b, -f false false, ?_⟩
  intro a b
  cases a <;> cases b <;> dsimp only
  · abel
  · abel
  · abel
  · -- The corner `(true, true)` is determined by the antipode identity.
    have hsum : f true true + f false false = f false true + f true false := by
      rw [add_comm (f true true)]
      exact hanti
    rw [eq_sub_of_add_eq hsum]
    abel

/-- If a Boolean-square table splits as `row a + col b + c`, its two diagonals have the same sum:
both equal `row false + row true + col false + col true + 2 • c`. -/
theorem boolSquare_antipode_of_additive_split {A : Type*} [AddCommGroup A]
    (f : Bool → Bool → A)
    (hsplit : ∃ (row col : Bool → A) (c : A), ∀ a b : Bool, f a b = row a + col b + c) :
    f false false + f true true = f false true + f true false := by
  rcases hsplit with ⟨row, col, c, h⟩
  rw [h false false, h true true, h false true, h true false]
  abel

/-- A Boolean-square table satisfies the antipode identity if and only if it splits additively
into a row term, a column term, and a constant. -/
theorem boolSquare_antipode_iff_additive_split {A : Type*} [AddCommGroup A]
    (f : Bool → Bool → A) :
    f false false + f true true = f false true + f true false ↔
      ∃ (row col : Bool → A) (c : A), ∀ a b : Bool, f a b = row a + col b + c :=
  ⟨boolSquare_additive_split_of_antipode f, boolSquare_antipode_of_additive_split f⟩

end MechInterp

import Xorformer.Theorems.Model.Equivalence
import Xorformer.Theorems.Results.LowComplexity

set_option linter.style.header false

/-!
# The literal head-complexity measure

Every Boolean function is computable by some literal XORFormer, and the minimum `HStar` is
attained. A realization with `k` heads bounds `HStar` above. An exact complexity fixes it.
-/

namespace Xorformer

variable {n : ℕ}

/-- Every Boolean function is computed by a literal XORFormer with some number of heads. -/
theorem exists_computableWithHeads (f : (Fin n → Bool) → Bool) :
    ∃ k, ComputableWithHeads n k f :=
  (exists_computable f).imp fun k => (computableWithHeads_iff_reduced k f).mpr

/-- **Attainment.** `HStar n f` heads suffice. -/
theorem HStar_computable (f : (Fin n → Bool) → Bool) : ComputableWithHeads n (HStar n f) f := by
  classical
  have hex := exists_computableWithHeads f
  unfold HStar
  rw [dif_pos hex]
  exact Nat.find_spec hex

/-- A realization with `k` heads bounds the head complexity above. -/
theorem HStar_le_of_computable {k : ℕ} {f : (Fin n → Bool) → Bool}
    (h : ComputableWithHeads n k f) : HStar n f ≤ k := by
  classical
  have hex : ∃ k, ComputableWithHeads n k f := ⟨k, h⟩
  unfold HStar
  rw [dif_pos hex]
  exact Nat.find_min' hex h

/-- Impossibility below `m` bounds the head complexity below. -/
theorem le_HStar_of_not_computable {m : ℕ} {f : (Fin n → Bool) → Bool}
    (h : ∀ k < m, ¬ ComputableWithHeads n k f) : m ≤ HStar n f := by
  by_contra hlt
  exact h _ (Nat.lt_of_not_le hlt) (HStar_computable f)

/-- Below `HStar n f`, no head count suffices. -/
theorem not_computable_of_lt_HStar {k : ℕ} {f : (Fin n → Bool) → Bool} (hk : k < HStar n f) :
    ¬ ComputableWithHeads n k f :=
  fun h => absurd (HStar_le_of_computable h) (not_le.mpr hk)

/-- An exact complexity determines `HStar`. -/
theorem HStar_eq_of_exact {k : ℕ} {f : (Fin n → Bool) → Bool}
    (hk : ExactHeadComplexity n f k) : HStar n f = k :=
  le_antisymm (HStar_le_of_computable hk.1) (le_HStar_of_not_computable hk.2)

/-- `HStar n f` is the exact head complexity of `f`. -/
theorem exactHeadComplexity_HStar (f : (Fin n → Bool) → Bool) :
    ExactHeadComplexity n f (HStar n f) :=
  ⟨HStar_computable f, fun _ hk => not_computable_of_lt_HStar hk⟩

end Xorformer

import MechInterp.Definitions.Architecture.Mask
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.Module.Basic
import Mathlib.Data.Real.Basic

set_option linter.style.header false

/-!
# Attention patterns, pattern rules, and weight rules

An `AttnPattern` is a row-stochastic matrix. A `PatternRule` turns scores into certified
patterns supported on a mask; softmax and hardmax are instances. A `WeightRule` produces raw,
not necessarily normalized, weights (linear and sigmoid attention). Value aggregation `mix`
is defined for arbitrary weights.
-/

namespace MechInterp

/-- A row-stochastic attention pattern. -/
structure AttnPattern (Pdst Psrc : Type*) [Fintype Psrc] where
  A : Pdst → Psrc → ℝ
  nonneg : ∀ i j, 0 ≤ A i j
  row_sum : ∀ i, ∑ j, A i j = 1

/-- Weighted aggregation `(mix A v)_i = ∑ j, A i j • v j`. -/
def mix {Pdst Psrc U : Type*} [Fintype Psrc] [AddCommMonoid U] [Module ℝ U]
    (A : Pdst → Psrc → ℝ) (v : Psrc → U) : Pdst → U :=
  fun i => ∑ j, A i j • v j

namespace AttnPattern

variable {Pdst Psrc Pmid : Type*} [Fintype Psrc]

/-- The pattern vanishes outside the mask. -/
def SupportedOn (A : AttnPattern Pdst Psrc) (M : Mask Pdst Psrc) : Prop :=
  ∀ i j, ¬ M.allowed i j → A.A i j = 0

/-- Composition (matrix product) of patterns: `(A B)_ik = ∑ j, A_ij B_jk`. -/
def comp [Fintype Pmid] (A : AttnPattern Pdst Pmid) (B : AttnPattern Pmid Psrc) :
    AttnPattern Pdst Psrc where
  A i k := ∑ j, A.A i j * B.A j k
  nonneg i k := Finset.sum_nonneg fun j _ => mul_nonneg (A.nonneg i j) (B.nonneg j k)
  row_sum i := by
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, B.row_sum, mul_one, A.row_sum]

/-- The pattern that attends from `i` to the single source `f i`. -/
def point [DecidableEq Psrc] (f : Pdst → Psrc) : AttnPattern Pdst Psrc where
  A i j := if j = f i then 1 else 0
  nonneg i j := by split_ifs <;> norm_num
  row_sum i := by simp

/-- The uniform pattern over all sources. -/
noncomputable def uniform [Nonempty Psrc] : AttnPattern Pdst Psrc where
  A _ _ := 1 / (Fintype.card Psrc : ℝ)
  nonneg _ _ := div_nonneg zero_le_one (Nat.cast_nonneg _)
  row_sum _ := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have : (Fintype.card Psrc : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    field_simp

end AttnPattern

/-- A rule turning scores into certified patterns supported on the mask `M`. -/
structure PatternRule (Pdst Psrc : Type*) [Fintype Psrc] (M : Mask Pdst Psrc) where
  toPattern : (Pdst → Psrc → ℝ) → AttnPattern Pdst Psrc
  supported : ∀ s, (toPattern s).SupportedOn M

namespace PatternRule

variable {Pdst Psrc : Type*} [Fintype Psrc] {M : Mask Pdst Psrc}

/-- Adding a constant to every score in a row leaves the pattern unchanged. -/
def RowShiftInvariant (ρ : PatternRule Pdst Psrc M) : Prop :=
  ∀ s (c : Pdst → ℝ), ρ.toPattern (fun i j => s i j + c i) = ρ.toPattern s

/-- Row `i` of the pattern depends only on the allowed scores of row `i`. -/
def RowLocal (ρ : PatternRule Pdst Psrc M) : Prop :=
  ∀ s s' i, (∀ j, M.allowed i j → s i j = s' i j) →
    ∀ j, (ρ.toPattern s).A i j = (ρ.toPattern s').A i j

end PatternRule

/-- A rule producing raw attention weights from scores. -/
structure WeightRule (Pdst Psrc : Type*) where
  toWeights : (Pdst → Psrc → ℝ) → Pdst → Psrc → ℝ

end MechInterp

import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import MechInterp.Definitions.Math.Polynomial

set_option linter.style.header false

/-!
# Real partial-fraction identity

Given `P : ℝ[X]` with `natDegree P ≤ K` and `K` distinct shifts `a_h`, there are `A` and
`b_h` with `P = A · ∏ h, (X + a_h) + ∑ h, b_h · ∏_{j ≠ h} (X + a_j)`. Dividing by the full
product gives the linear-fractional decomposition `P/Q = A + ∑ h, b_h / (X + a_h)`.
-/

open Polynomial Finset

namespace MechInterp

theorem eval_shiftProd {K : ℕ} (av : Fin K → ℝ) (k : ℝ) :
    (shiftProd av).eval k = ∏ h : Fin K, (k + av h) := by
  rw [shiftProd, eval_prod]; simp

theorem eval_shiftProdErase {K : ℕ} (av : Fin K → ℝ) (h : Fin K) (k : ℝ) :
    (shiftProdErase av h).eval k = ∏ j ∈ Finset.univ.erase h, (k + av j) := by
  rw [shiftProdErase, eval_prod]; simp

/-- **Real partial-fraction identity**, polynomial form. -/
theorem real_partial_fraction_poly {K : ℕ} (P : ℝ[X]) (av : Fin K → ℝ)
    (hinj : Function.Injective av) (hdeg : P.natDegree ≤ K) :
    ∃ (A : ℝ) (bv : Fin K → ℝ),
      P = C A * shiftProd av + ∑ h : Fin K, C (bv h) * shiftProdErase av h := by
  classical
  set Q : ℝ[X] := shiftProd av with hQ
  set L : Fin K → ℝ[X] := fun h => shiftProdErase av h with hL
  have hdeg_factor : ∀ a : ℝ, (X + C a).natDegree = 1 := fun a => natDegree_X_add_C a
  have hfac_ne : ∀ a : ℝ, (X + C a) ≠ 0 := fun a => (monic_X_add_C a).ne_zero
  have hQmonic : Q.Monic := monic_prod_of_monic _ _ (fun i _ => monic_X_add_C _)
  have hQdeg : Q.natDegree = K := by
    rw [hQ, shiftProd, natDegree_prod _ _ (fun i _ => hfac_ne _)]; simp [hdeg_factor]
  have hLdeg : ∀ h, (L h).natDegree = K - 1 := by
    intro h
    change (shiftProdErase av h).natDegree = K - 1
    rw [shiftProdErase, natDegree_prod _ _ (fun i _ => hfac_ne _)]
    simp only [hdeg_factor, Finset.sum_const, smul_eq_mul, mul_one]
    rw [Finset.card_erase_of_mem (Finset.mem_univ h), Finset.card_univ, Fintype.card_fin]
  have hdist : ∀ i : Fin K, (∏ j ∈ Finset.univ.erase i, (av j - av i)) ≠ 0 := by
    intro i
    refine Finset.prod_ne_zero_iff.mpr (fun j hj => ?_)
    rw [Finset.mem_erase] at hj
    exact sub_ne_zero.mpr (fun h => hj.1 (hinj h))
  set A : ℝ := P.coeff K with hA
  set bv : Fin K → ℝ :=
    fun i => P.eval (-av i) / (∏ j ∈ Finset.univ.erase i, (av j - av i)) with hbv
  have hevalQ : ∀ k : ℝ, Q.eval k = ∏ h : Fin K, (k + av h) := eval_shiftProd av
  have hevalL : ∀ (h : Fin K) (k : ℝ), (L h).eval k = ∏ j ∈ Finset.univ.erase h, (k + av j) :=
    eval_shiftProdErase av
  set R : ℝ[X] := C A * Q + ∑ h : Fin K, C (bv h) * L h with hR
  have hsumdeg : (∑ h : Fin K, C (bv h) * L h).natDegree ≤ K - 1 := by
    refine natDegree_sum_le_of_forall_le _ _ (fun h _ => ?_)
    exact (natDegree_C_mul_le _ _).trans (le_of_eq (hLdeg h))
  have hRroot : ∀ i : Fin K, (P - R).eval (-av i) = 0 := by
    intro i
    have hQroot : Q.eval (-av i) = 0 := by
      rw [hevalQ]; exact Finset.prod_eq_zero (Finset.mem_univ i) (by ring)
    have hLroot : ∀ h, h ≠ i → (L h).eval (-av i) = 0 := by
      intro h hhi
      rw [hevalL]
      exact Finset.prod_eq_zero
        (Finset.mem_erase.mpr ⟨fun e => hhi e.symm, Finset.mem_univ i⟩) (by ring)
    have hLi : (L i).eval (-av i) = ∏ j ∈ Finset.univ.erase i, (av j - av i) := by
      rw [hevalL]; exact Finset.prod_congr rfl (fun j _ => by ring)
    rw [eval_sub, hR, eval_add, eval_mul, eval_C, hQroot, mul_zero, zero_add, eval_finsetSum]
    rw [Finset.sum_eq_single i (fun h _ hhi => by rw [eval_mul, eval_C, hLroot h hhi, mul_zero])
      (fun h => absurd (Finset.mem_univ i) h)]
    rw [eval_mul, eval_C, hLi, hbv]
    field_simp [hdist i]
    ring
  have hpoly : P = R := by
    rcases Nat.eq_zero_or_pos K with hK0 | hKpos
    · subst hK0
      have hP : P = C A := by
        rw [eq_C_of_natDegree_le_zero (show P.natDegree ≤ 0 by omega), hA]
      rw [hP, hR]; simp [hQ, hL, shiftProd]
    · have hPRdeg : (P - R).natDegree < K := by
        have hle : (P - R).natDegree ≤ K - 1 := by
          rw [natDegree_le_iff_coeff_eq_zero]
          intro m hm
          have hmK : K ≤ m := by omega
          rw [coeff_sub, hR, coeff_add, coeff_C_mul]
          have hsumc : (∑ h : Fin K, C (bv h) * L h).coeff m = 0 :=
            coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hsumdeg (by omega))
          rw [hsumc, add_zero]
          rcases eq_or_lt_of_le hmK with hmeq | hmgt
          · rw [← hmeq, hA]
            have hQc : Q.coeff K = 1 := by rw [← hQdeg]; exact hQmonic.coeff_natDegree
            rw [hQc, mul_one, sub_self]
          · rw [coeff_eq_zero_of_natDegree_lt (hdeg.trans_lt hmgt),
              coeff_eq_zero_of_natDegree_lt (hQdeg ▸ hmgt), mul_zero, sub_zero]
        omega
      have hPR : P - R = 0 :=
        eq_zero_of_natDegree_lt_card_of_eval_eq_zero (P - R)
          (f := fun i => -av i) (fun a b hab => hinj (neg_injective hab)) hRroot
          (by rw [Fintype.card_fin]; exact hPRdeg)
      rwa [sub_eq_zero] at hPR
  exact ⟨A, bv, hpoly⟩

/-- **Real partial-fraction identity**, evaluated form. -/
theorem real_partial_fraction {K : ℕ} (P : ℝ[X]) (av : Fin K → ℝ)
    (hinj : Function.Injective av) (hdeg : P.natDegree ≤ K) :
    ∃ (A : ℝ) (bv : Fin K → ℝ), ∀ k : ℝ,
      P.eval k = A * (∏ h : Fin K, (k + av h))
        + ∑ h : Fin K, bv h * (∏ j ∈ Finset.univ.erase h, (k + av j)) := by
  obtain ⟨A, bv, hP⟩ := real_partial_fraction_poly P av hinj hdeg
  refine ⟨A, bv, fun k => ?_⟩
  have hev := congrArg (eval k) hP
  rw [eval_add, eval_mul, eval_C, eval_shiftProd, eval_finsetSum] at hev
  simp only [eval_mul, eval_C, eval_shiftProdErase] at hev
  exact hev

end MechInterp

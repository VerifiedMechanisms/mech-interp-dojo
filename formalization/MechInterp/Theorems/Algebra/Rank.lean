import MechInterp.Definitions.Algebra.Rank
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Rank theorems

* `ovRealizable_iff`: a linear map factors through `ℝ^r` iff its rank is at most `r`.
* `qkRealizable_iff`: a bilinear form factors as `⟪Q u, K v⟫` through `ℝ^r` iff its rank is
  at most `r`.
-/

namespace MechInterp

open scoped InnerProductSpace

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

/-- A map that factors through `ℝ^r` has rank at most `r`. -/
theorem linRank_le_of_ovRealizable {M : V →ₗ[ℝ] W} {r : ℕ} (h : OVRealizable M r) :
    linRank M ≤ r := by
  obtain ⟨Wv, O, rfl⟩ := h
  unfold linRank
  rw [LinearMap.range_comp]
  calc Module.finrank ℝ (Submodule.map O (LinearMap.range Wv))
      ≤ Module.finrank ℝ (LinearMap.range Wv) := Submodule.finrank_map_le O _
    _ ≤ Module.finrank ℝ (Vec r) := Submodule.finrank_le _
    _ = r := finrank_euclideanSpace_fin

/-- A map of rank at most `r` from a finite-dimensional space factors through `ℝ^r`. -/
theorem ovRealizable_of_linRank_le [FiniteDimensional ℝ V] {M : V →ₗ[ℝ] W} {r : ℕ}
    (h : linRank M ≤ r) : OVRealizable M r := by
  classical
  set k := Module.finrank ℝ (LinearMap.range M) with hk
  let b : Module.Basis (Fin k) ℝ (LinearMap.range M) := Module.finBasis ℝ _
  let c : V →ₗ[ℝ] (Fin k →₀ ℝ) := b.repr.toLinearMap ∘ₗ M.rangeRestrict
  let Wv : V →ₗ[ℝ] Vec r :=
    { toFun := fun v => RVec.ofFun fun j : Fin r =>
        if hj : (j : ℕ) < k then c v ⟨j, hj⟩ else 0
      map_add' := fun x y => by
        ext j
        simp only [RVec.ofFun_apply, map_add, Finsupp.add_apply, PiLp.add_apply]
        split_ifs <;> simp
      map_smul' := fun a x => by
        ext j
        simp only [RVec.ofFun_apply, map_smul, Finsupp.smul_apply, PiLp.smul_apply,
          RingHom.id_apply, smul_eq_mul]
        split_ifs <;> simp }
  let O : Vec r →ₗ[ℝ] W := RVec.linearOfFun fun j : Fin r =>
    if hj : (j : ℕ) < k then ((b ⟨j, hj⟩ : LinearMap.range M) : W) else 0
  refine ⟨Wv, O, LinearMap.ext fun v => ?_⟩
  have hsum : ∑ j : Fin r, (Wv v) j • (if hj : (j : ℕ) < k then
      ((b ⟨j, hj⟩ : LinearMap.range M) : W) else 0) =
      ∑ i : Fin k, c v i • ((b i : LinearMap.range M) : W) := by
    rw [← Finset.sum_subset (Finset.subset_univ
      (Finset.univ.map (Fin.castLEEmb (show k ≤ r from h))))]
    · rw [Finset.sum_map]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hi : ((Fin.castLEEmb (show k ≤ r from h) i : Fin r) : ℕ) < k := by simp
      simp only [Wv, LinearMap.coe_mk, AddHom.coe_mk, RVec.ofFun_apply, dif_pos hi]
      rfl
    · intro j _ hj
      have : ¬ (j : ℕ) < k := by
        intro hlt
        exact hj (Finset.mem_map.mpr ⟨⟨j, hlt⟩, Finset.mem_univ _, by ext; simp⟩)
      simp [this]
  change M v = O (Wv v)
  simp only [O, RVec.linearOfFun_apply]
  rw [hsum]
  have hrep := b.sum_repr (M.rangeRestrict v)
  calc M v = ((M.rangeRestrict v : LinearMap.range M) : W) := rfl
    _ = ((∑ i, b.repr (M.rangeRestrict v) i • b i : LinearMap.range M) : W) := by rw [hrep]
    _ = ∑ i : Fin k, c v i • ((b i : LinearMap.range M) : W) := by
      simp only [Submodule.coe_sum, Submodule.coe_smul]
      rfl

/-- **OV rank theorem.** A linear map from a finite-dimensional space factors through `ℝ^r`
exactly when its rank is at most `r`. -/
theorem ovRealizable_iff [FiniteDimensional ℝ V] (M : V →ₗ[ℝ] W) (r : ℕ) :
    OVRealizable M r ↔ linRank M ≤ r :=
  ⟨linRank_le_of_ovRealizable, ovRealizable_of_linRank_le⟩

/-- **QK rank theorem.** A bilinear form on a finite-dimensional space factors as
`⟪Q u, K v⟫` through `ℝ^r` exactly when its rank is at most `r`. -/
theorem qkRealizable_iff [FiniteDimensional ℝ V] (B : V →ₗ[ℝ] W →ₗ[ℝ] ℝ) (r : ℕ) :
    QKRealizable B r ↔ bilinRank B ≤ r := by
  classical
  constructor
  · rintro ⟨Q, K, hQK⟩
    apply linRank_le_of_ovRealizable
    refine ⟨Q, LinearMap.mk₂ ℝ (fun x v => ⟪x, K v⟫_ℝ) (fun x y v => inner_add_left _ _ _)
      (fun a x v => real_inner_smul_left _ _ _)
      (fun x v w => by simp [inner_add_right])
      (fun a x v => by simp [real_inner_smul_right]), ?_⟩
    ext u v
    simp [hQK]
  · intro h
    obtain ⟨Q, O, hO⟩ := ovRealizable_of_linRank_le h
    let K : W →ₗ[ℝ] Vec r :=
      { toFun := fun v => RVec.ofFun fun j => O (RVec.oneHot j) v
        map_add' := fun x y => by ext j; simp
        map_smul' := fun a x => by ext j; simp }
    refine ⟨Q, K, fun u v => ?_⟩
    rw [hO, LinearMap.comp_apply, RVec.linearMap_apply_eq_sum O, RVec.inner_eq_sum]
    simp [K, LinearMap.sum_apply]

theorem frobeniusNormSq_nonneg {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (f : RVec ι →ₗ[ℝ] RVec κ) : 0 ≤ frobeniusNormSq f :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem frobeniusNorm_nonneg {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (f : RVec ι →ₗ[ℝ] RVec κ) : 0 ≤ frobeniusNorm f :=
  Real.sqrt_nonneg _

@[simp] theorem frobeniusNorm_zero {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] :
    frobeniusNorm (0 : RVec ι →ₗ[ℝ] RVec κ) = 0 := by
  simp [frobeniusNorm, frobeniusNormSq]

theorem frobeniusNorm_sq {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (f : RVec ι →ₗ[ℝ] RVec κ) : frobeniusNorm f ^ 2 = frobeniusNormSq f :=
  Real.sq_sqrt (frobeniusNormSq_nonneg f)

end MechInterp

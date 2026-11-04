/-
Copyright (c) 2026 Malhar A. Patel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Malhar A. Patel
-/
import MechInterp.Algebra.Spaces
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Rank, low-rank factorizations, and Frobenius norms

An attention head with query/key width `r` scores tokens through the bilinear form
`B u v = ⟪W_Q u, W_K v⟫`, which factors through `ℝ^r`. Its value path `W_O ∘ W_V` factors through
`ℝ^r'`, where `r'` is the value width. This file shows that these factorization constraints are
exactly rank bounds, so the dimensions of a head limit only the *rank* of what it computes.

## Main definitions

* `linRank M`: the rank of a linear map, the dimension of its range.
* `bilinRank B`: the rank of a bilinear form `B : V →ₗ W →ₗ ℝ`, viewed as a linear map into
  functionals on `W`.
* `QKRealizable B r`: `B u v = ⟪Q u, K v⟫` for some linear `Q, K` into `ℝ^r`.
* `OVRealizable M r`: `M = O ∘ Wv` for some linear `Wv : V → ℝ^r` and `O : ℝ^r → W`.
* `frobeniusNormSq`, `frobeniusNorm`: the Frobenius norm of a linear map between coordinate
  spaces, computed from its matrix entries `(f δ_i) k`.
* `compositionScore M N = ‖M ∘ N‖_F / (‖M‖_F ‖N‖_F)`, the composition score of Elhage et al.
  (2021), which measures how much of `M`'s input space is fed by `N`'s output.

## Main results

* `ovRealizable_iff`: a linear map out of a finite-dimensional space factors through `ℝ^r` if and
  only if its rank is at most `r`.
* `qkRealizable_iff`: a bilinear form on a finite-dimensional space factors as `⟪Q u, K v⟫`
  through `ℝ^r` if and only if its rank is at most `r`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

namespace MechInterp

open scoped InnerProductSpace

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

/-! ### Rank and realizability -/

/-- The rank of a linear map: the dimension of its range. -/
noncomputable def linRank (M : V →ₗ[ℝ] W) : ℕ := Module.finrank ℝ (LinearMap.range M)

/-- The rank of a bilinear form `B`, viewed as the linear map `u ↦ B u` into functionals. -/
noncomputable def bilinRank (B : V →ₗ[ℝ] W →ₗ[ℝ] ℝ) : ℕ := linRank B

/-- A bilinear form is **QK-realizable at width `r`** when `B u v = ⟪Q u, K v⟫` for linear maps
`Q, K` into `ℝ^r`. This is what a head with query/key width `r` can compute as its scores. -/
def QKRealizable (B : V →ₗ[ℝ] W →ₗ[ℝ] ℝ) (r : ℕ) : Prop :=
  ∃ (Q : V →ₗ[ℝ] Vec r) (K : W →ₗ[ℝ] Vec r), ∀ u v, B u v = ⟪Q u, K v⟫_ℝ

/-- A linear map is **OV-realizable at width `r`** when `M = O ∘ Wv` for linear maps
`Wv : V → ℝ^r` and `O : ℝ^r → W`. This is what a head with value width `r` can compute as its
value-output path. -/
def OVRealizable (M : V →ₗ[ℝ] W) (r : ℕ) : Prop :=
  ∃ (Wv : V →ₗ[ℝ] Vec r) (O : Vec r →ₗ[ℝ] W), M = O ∘ₗ Wv

/-- A map that factors through `ℝ^r` has rank at most `r`: its range is the image under `O` of the
range of `Wv`, which sits inside the `r`-dimensional space `ℝ^r`. -/
theorem linRank_le_of_ovRealizable {M : V →ₗ[ℝ] W} {r : ℕ} (h : OVRealizable M r) :
    linRank M ≤ r := by
  obtain ⟨Wv, O, rfl⟩ := h
  unfold linRank
  rw [LinearMap.range_comp]
  calc Module.finrank ℝ (Submodule.map O (LinearMap.range Wv))
      ≤ Module.finrank ℝ (LinearMap.range Wv) := Submodule.finrank_map_le O _
    _ ≤ Module.finrank ℝ (Vec r) := Submodule.finrank_le _
    _ = r := finrank_euclideanSpace_fin

/-- A map of rank at most `r` from a finite-dimensional space factors through `ℝ^r`.

*Construction.* Pick a basis `b_1, …, b_k` of the range of `M` (so `k ≤ r`) and write
`M v = ∑ i, c_i(v) • b_i`. Let `Wv v = (c_1(v), …, c_k(v), 0, …, 0) ∈ ℝ^r`, and let `O` send the
`j`-th one-hot vector to `b_j` for `j < k` and to `0` otherwise. Then `O ∘ Wv = M`. -/
theorem ovRealizable_of_linRank_le [FiniteDimensional ℝ V] {M : V →ₗ[ℝ] W} {r : ℕ}
    (h : linRank M ≤ r) : OVRealizable M r := by
  classical
  set k := Module.finrank ℝ (LinearMap.range M) with hk
  -- A basis of the range of `M`, and the coordinates `c v` of `M v` in it.
  let b : Module.Basis (Fin k) ℝ (LinearMap.range M) := Module.finBasis ℝ _
  let c : V →ₗ[ℝ] (Fin k →₀ ℝ) := b.repr.toLinearMap ∘ₗ M.rangeRestrict
  -- `Wv` writes the `k` coordinates into the first `k` slots of `ℝ^r`.
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
  -- `O` sends slot `j < k` to the basis vector `b_j` and the other slots to zero.
  let O : Vec r →ₗ[ℝ] W := RVec.linearOfFun fun j : Fin r =>
    if hj : (j : ℕ) < k then ((b ⟨j, hj⟩ : LinearMap.range M) : W) else 0
  refine ⟨Wv, O, LinearMap.ext fun v => ?_⟩
  -- Only the first `k` slots contribute to `O (Wv v)`.
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
  -- Expand `M v` in the basis `b`.
  have hrep := b.sum_repr (M.rangeRestrict v)
  calc M v = ((M.rangeRestrict v : LinearMap.range M) : W) := rfl
    _ = ((∑ i, b.repr (M.rangeRestrict v) i • b i : LinearMap.range M) : W) := by rw [hrep]
    _ = ∑ i : Fin k, c v i • ((b i : LinearMap.range M) : W) := by
      simp only [Submodule.coe_sum, Submodule.coe_smul]
      rfl

/-- **OV rank theorem.** A linear map out of a finite-dimensional space factors through `ℝ^r`
exactly when its rank is at most `r`. -/
theorem ovRealizable_iff [FiniteDimensional ℝ V] (M : V →ₗ[ℝ] W) (r : ℕ) :
    OVRealizable M r ↔ linRank M ≤ r :=
  ⟨linRank_le_of_ovRealizable, ovRealizable_of_linRank_le⟩

/-- **QK rank theorem.** A bilinear form on a finite-dimensional space factors as `⟪Q u, K v⟫`
through `ℝ^r` exactly when its rank is at most `r`.

*Proof.* (⇒) `u ↦ B u` factors through `ℝ^r` as `x ↦ ⟪x, K ·⟫` after `Q`, so the OV bound
applies. (⇐) The OV theorem gives `B = O ∘ Q` with `O : ℝ^r → W*`. Set
`K v = (O δ_j v)_j`; then `⟪Q u, K v⟫ = ∑ j, (Q u)_j · O δ_j v = O (Q u) v = B u v`. -/
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

/-! ### Frobenius norms and composition scores -/

section Frobenius

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

/-- The squared Frobenius norm `∑ i, ∑ k, ((f δ_i) k)²`, the sum of squared matrix entries. -/
noncomputable def frobeniusNormSq (f : RVec ι →ₗ[ℝ] RVec κ) : ℝ :=
  ∑ i, ∑ k, (f (RVec.oneHot i) k) ^ 2

/-- The Frobenius norm `‖f‖_F`, the square root of `frobeniusNormSq f`. -/
noncomputable def frobeniusNorm (f : RVec ι →ₗ[ℝ] RVec κ) : ℝ := √(frobeniusNormSq f)

/-- The composition score `‖M ∘ N‖_F / (‖M‖_F ‖N‖_F)`. It is large when the output of `N` lands
in the part of the input space that `M` reads. -/
noncomputable def compositionScore {μ : Type*} [Fintype μ] [DecidableEq κ]
    (M : RVec κ →ₗ[ℝ] RVec μ) (N : RVec ι →ₗ[ℝ] RVec κ) : ℝ :=
  frobeniusNorm (M ∘ₗ N) / (frobeniusNorm M * frobeniusNorm N)

end Frobenius

/-- A squared Frobenius norm is a sum of squares, hence nonnegative. -/
theorem frobeniusNormSq_nonneg {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (f : RVec ι →ₗ[ℝ] RVec κ) : 0 ≤ frobeniusNormSq f :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- A Frobenius norm is nonnegative. -/
theorem frobeniusNorm_nonneg {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (f : RVec ι →ₗ[ℝ] RVec κ) : 0 ≤ frobeniusNorm f :=
  Real.sqrt_nonneg _

/-- The zero map has Frobenius norm zero. -/
@[simp] theorem frobeniusNorm_zero {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] :
    frobeniusNorm (0 : RVec ι →ₗ[ℝ] RVec κ) = 0 := by
  simp [frobeniusNorm, frobeniusNormSq]

/-- Squaring the Frobenius norm gives the squared Frobenius norm. -/
theorem frobeniusNorm_sq {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (f : RVec ι →ₗ[ℝ] RVec κ) : frobeniusNorm f ^ 2 = frobeniusNormSq f :=
  Real.sq_sqrt (frobeniusNormSq_nonneg f)

end MechInterp

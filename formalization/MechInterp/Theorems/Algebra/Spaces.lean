import MechInterp.Definitions.Algebra.Spaces

set_option linter.style.header false

/-!
# Coordinates, one-hot vectors, and inner products on `RVec`
-/

namespace MechInterp

open scoped InnerProductSpace

namespace RVec

variable {ι : Type*}

@[simp] theorem ofFun_apply (f : ι → ℝ) (i : ι) : ofFun f i = f i := rfl

@[simp] theorem ones_apply (i : ι) : (ones : RVec ι) i = 1 := rfl

@[simp] theorem hadamard_apply (x y : RVec ι) (i : ι) : hadamard x y i = x i * y i := rfl

@[simp] theorem map_apply (f : ℝ → ℝ) (x : RVec ι) (i : ι) : map f x i = f (x i) := rfl

theorem ext_iff' {x y : RVec ι} : x = y ↔ ∀ i, x i = y i :=
  ⟨fun h _ => h ▸ rfl, fun h => by ext i; exact h i⟩

@[simp] theorem oneHot_apply [DecidableEq ι] (i j : ι) :
    oneHot i j = if j = i then 1 else 0 := by
  simp [oneHot]

theorem inner_eq_sum [Fintype ι] (x y : RVec ι) : ⟪x, y⟫_ℝ = ∑ i, x i * y i := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem inner_oneHot_left [Fintype ι] [DecidableEq ι] (i : ι) (x : RVec ι) :
    ⟪oneHot i, x⟫_ℝ = x i := by
  simp [oneHot, EuclideanSpace.inner_single_left]

theorem inner_oneHot_right [Fintype ι] [DecidableEq ι] (i : ι) (x : RVec ι) :
    ⟪x, oneHot i⟫_ℝ = x i := by
  rw [real_inner_comm, inner_oneHot_left]

theorem sum_smul_oneHot [Fintype ι] [DecidableEq ι] (x : RVec ι) :
    ∑ i, x i • oneHot i = x := by
  ext j
  simp [Finset.sum_apply]

@[simp] theorem linearOfFun_apply [Fintype ι] {V : Type*} [AddCommGroup V] [Module ℝ V]
    (e : ι → V) (x : RVec ι) : linearOfFun e x = ∑ i, x i • e i := rfl

@[simp] theorem linearOfFun_oneHot [Fintype ι] [DecidableEq ι] {V : Type*} [AddCommGroup V]
    [Module ℝ V] (e : ι → V) (i : ι) : linearOfFun e (oneHot i) = e i := by
  simp [ite_smul]

theorem linearMap_eq_linearOfFun [Fintype ι] [DecidableEq ι] {V : Type*} [AddCommGroup V]
    [Module ℝ V] (f : RVec ι →ₗ[ℝ] V) : f = linearOfFun fun i => f (oneHot i) := by
  apply LinearMap.ext
  intro x
  conv_lhs => rw [← sum_smul_oneHot x]
  simp [map_sum, map_smul]

theorem linearMap_apply_eq_sum [Fintype ι] [DecidableEq ι] {V : Type*} [AddCommGroup V]
    [Module ℝ V] (f : RVec ι →ₗ[ℝ] V) (x : RVec ι) : f x = ∑ i, x i • f (oneHot i) := by
  conv_lhs => rw [linearMap_eq_linearOfFun f]
  rfl

theorem norm_sq_eq_sum [Fintype ι] (x : RVec ι) : ‖x‖ ^ 2 = ∑ i, x i ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_eq_sum]
  exact Finset.sum_congr rfl fun i _ => (sq (x i)).symm

@[simp] theorem restrictAlong_apply {κ : Type*} (e : κ → ι) (w : RVec ι) (k : κ) :
    restrictAlong e w k = w (e k) := rfl

theorem extendAlong_apply [DecidableEq ι] {κ : Type*} [Fintype κ] (e : κ → ι) (v : RVec κ)
    (i : ι) : extendAlong e v i = ∑ k, if e k = i then v k else 0 := by
  simp [extendAlong, Finset.sum_apply, eq_comm]

theorem extendAlong_apply_self [DecidableEq ι] {κ : Type*} [Fintype κ] {e : κ → ι}
    (he : Function.Injective e) (v : RVec κ) (k : κ) : extendAlong e v (e k) = v k := by
  rw [extendAlong_apply,
    Finset.sum_eq_single k (fun b _ hb => by rw [if_neg (fun h => hb (he h))]) (by simp)]
  simp

theorem extendAlong_apply_of_forall_ne [DecidableEq ι] {κ : Type*} [Fintype κ] {e : κ → ι}
    (v : RVec κ) {i : ι} (hi : ∀ k, e k ≠ i) : extendAlong e v i = 0 := by
  rw [extendAlong_apply]
  exact Finset.sum_eq_zero fun k _ => by simp [hi k]

/-- Extension along `e` is adjoint to restriction along `e`. -/
theorem inner_extendAlong_left [Fintype ι] [DecidableEq ι] {κ : Type*} [Fintype κ]
    (e : κ → ι) (v : RVec κ) (w : RVec ι) :
    ⟪extendAlong e v, w⟫_ℝ = ⟪v, restrictAlong e w⟫_ℝ := by
  simp only [extendAlong, linearOfFun_apply, sum_inner, real_inner_smul_left,
    inner_oneHot_left]
  rw [inner_eq_sum]
  rfl

theorem restrictAlong_extendAlong [DecidableEq ι] {κ : Type*} [Fintype κ] {e : κ → ι}
    (he : Function.Injective e) (v : RVec κ) : restrictAlong e (extendAlong e v) = v := by
  ext k
  simp [extendAlong_apply_self he]

/-- Extension along an injective map preserves inner products. -/
theorem inner_extendAlong [Fintype ι] [DecidableEq ι] {κ : Type*} [Fintype κ] {e : κ → ι}
    (he : Function.Injective e) (v w : RVec κ) :
    ⟪extendAlong e v, extendAlong e w⟫_ℝ = ⟪v, w⟫_ℝ := by
  rw [inner_extendAlong_left, restrictAlong_extendAlong he]

end RVec

namespace Stream

variable {P V : Type*}

@[simp] theorem update_same [DecidableEq P] (X : Stream P V) (p : P) (v : V) :
    X.update p v p = v := by simp [update]

theorem update_of_ne [DecidableEq P] (X : Stream P V) {p q : P} (h : q ≠ p) (v : V) :
    X.update p v q = X q := by simp [update, h]

@[simp] theorem mapPos_apply {W : Type*} (f : V → W) (X : Stream P V) (p : P) :
    mapPos f X p = f (X p) := rfl

end Stream

end MechInterp

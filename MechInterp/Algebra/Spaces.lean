/-
Copyright (c) 2026 Malhar A. Patel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Malhar A. Patel
-/
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Coordinate spaces and residual streams

Transformers manipulate real vectors whose coordinates have meaning: one coordinate per token in
a one-hot encoding, one per neuron, one per head dimension. This file fixes the spaces that hold
such vectors and the basic coordinate operations on them.

## Main definitions

* `RVec ι`: the Euclidean space `ℝ^ι` with one coordinate per element of a finite type `ι` and
  the standard inner product `⟪x, y⟫ = ∑ i, x i * y i`. It is Mathlib's `EuclideanSpace ℝ ι`.
* `Vec d`: the special case `ι = Fin d`, the usual `ℝᵈ`.
* `Stream P V`: a *residual stream*, one vector of `V` for each position `p : P`.
* Coordinate constructions in the namespace `RVec`: `ofFun`, `oneHot`, `ones`, `hadamard`, `map`,
  `l0`, and `linearOfFun` (the linear map that sends `oneHot i` to a chosen `e i`).
* Reindexing along a map `e : κ → ι`: `RVec.restrictAlong e` reads the coordinates `e k`, and
  `RVec.extendAlong e` writes coordinate `k` into position `e k`. For injective `e` these are
  restriction to a block and extension by zero; `MechInterp.Algebra.Blocks` builds on them.

## Main results

* `RVec.inner_eq_sum`, `RVec.norm_sq_eq_sum`: inner products and norms in coordinates.
* `RVec.linearMap_eq_linearOfFun`: a linear map out of `RVec ι` is determined by the images of
  the one-hot vectors.
* `RVec.inner_extendAlong_left`: `extendAlong e` and `restrictAlong e` are adjoint.
* `RVec.inner_extendAlong`: for injective `e`, `extendAlong e` preserves inner products.

## Implementation notes

Coordinates are indexed by arbitrary finite types rather than only by `Fin d`. Concatenated
spaces can then be indexed by sum, product, or sigma types, so block maps never need index
arithmetic.
-/

namespace MechInterp

open scoped InnerProductSpace

/-- The Euclidean space `ℝ^ι` indexed by a finite type `ι`, with the standard inner product. -/
abbrev RVec (ι : Type*) := EuclideanSpace ℝ ι

/-- The standard `d`-dimensional real inner product space `ℝᵈ`. -/
abbrev Vec (d : ℕ) := RVec (Fin d)

/-- A residual stream: one vector of `V` for each position `p : P`. -/
abbrev Stream (P V : Type*) := P → V

namespace RVec

variable {ι : Type*}

/-! ### Coordinate constructions -/

/-- The vector whose `i`-th coordinate is `f i`. -/
def ofFun (f : ι → ℝ) : RVec ι := WithLp.toLp 2 f

@[simp] theorem ofFun_apply (f : ι → ℝ) (i : ι) : ofFun f i = f i := rfl

/-- Two vectors are equal when all their coordinates are. -/
theorem ext_iff' {x y : RVec ι} : x = y ↔ ∀ i, x i = y i :=
  ⟨fun h _ => h ▸ rfl, fun h => by ext i; exact h i⟩

/-- The one-hot (standard basis) vector `δ_i`, with a `1` at index `i` and `0` elsewhere. -/
noncomputable def oneHot [DecidableEq ι] (i : ι) : RVec ι := EuclideanSpace.single i 1

@[simp] theorem oneHot_apply [DecidableEq ι] (i j : ι) :
    oneHot i j = if j = i then 1 else 0 := by
  simp [oneHot]

/-- The all-ones vector. -/
def ones : RVec ι := ofFun fun _ => 1

@[simp] theorem ones_apply (i : ι) : (ones : RVec ι) i = 1 := rfl

/-- The coordinatewise (Hadamard) product `(x ⊙ y) i = x i * y i`. -/
def hadamard (x y : RVec ι) : RVec ι := ofFun fun i => x i * y i

@[simp] theorem hadamard_apply (x y : RVec ι) (i : ι) : hadamard x y i = x i * y i := rfl

/-- Apply a scalar function `f` to every coordinate, as an activation function does. -/
def map (f : ℝ → ℝ) (x : RVec ι) : RVec ι := ofFun fun i => f (x i)

@[simp] theorem map_apply (f : ℝ → ℝ) (x : RVec ι) (i : ι) : map f x i = f (x i) := rfl

/-- The number of nonzero coordinates, `‖x‖₀`. -/
noncomputable def l0 [Fintype ι] (x : RVec ι) : ℕ := by
  classical exact (Finset.univ.filter fun i => x i ≠ 0).card

/-! ### Inner products in coordinates -/

/-- The inner product is the sum of coordinatewise products. -/
theorem inner_eq_sum [Fintype ι] (x y : RVec ι) : ⟪x, y⟫_ℝ = ∑ i, x i * y i := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- The squared norm is the sum of squared coordinates. -/
theorem norm_sq_eq_sum [Fintype ι] (x : RVec ι) : ‖x‖ ^ 2 = ∑ i, x i ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_eq_sum]
  exact Finset.sum_congr rfl fun i _ => (sq (x i)).symm

/-- Pairing with a one-hot vector on the left reads off a coordinate: `⟪δ_i, x⟫ = x i`. -/
theorem inner_oneHot_left [Fintype ι] [DecidableEq ι] (i : ι) (x : RVec ι) :
    ⟪oneHot i, x⟫_ℝ = x i := by
  simp [oneHot, EuclideanSpace.inner_single_left]

/-- Pairing with a one-hot vector on the right reads off a coordinate: `⟪x, δ_i⟫ = x i`. -/
theorem inner_oneHot_right [Fintype ι] [DecidableEq ι] (i : ι) (x : RVec ι) :
    ⟪x, oneHot i⟫_ℝ = x i := by
  rw [real_inner_comm, inner_oneHot_left]

/-- Every vector is the sum of its coordinates times the one-hot vectors: `∑ i, x i • δ_i = x`. -/
theorem sum_smul_oneHot [Fintype ι] [DecidableEq ι] (x : RVec ι) :
    ∑ i, x i • oneHot i = x := by
  ext j
  simp [Finset.sum_apply]

/-! ### Linear maps out of a coordinate space -/

/-- The linear map `x ↦ ∑ i, x i • e i`, which sends the one-hot vector `δ_i` to `e i`.
Embedding matrices are built this way from a list of vectors. -/
noncomputable def linearOfFun [Fintype ι] {V : Type*} [AddCommGroup V] [Module ℝ V]
    (e : ι → V) : RVec ι →ₗ[ℝ] V where
  toFun x := ∑ i, x i • e i
  map_add' x y := by
    simp only [PiLp.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [PiLp.smul_apply, smul_eq_mul, mul_smul, RingHom.id_apply, Finset.smul_sum]

@[simp] theorem linearOfFun_apply [Fintype ι] {V : Type*} [AddCommGroup V] [Module ℝ V]
    (e : ι → V) (x : RVec ι) : linearOfFun e x = ∑ i, x i • e i := rfl

/-- `linearOfFun e` sends the one-hot vector `δ_i` to `e i`. -/
@[simp] theorem linearOfFun_oneHot [Fintype ι] [DecidableEq ι] {V : Type*} [AddCommGroup V]
    [Module ℝ V] (e : ι → V) (i : ι) : linearOfFun e (oneHot i) = e i := by
  simp [ite_smul]

/-- A linear map out of `RVec ι` is determined by where it sends the one-hot vectors. -/
theorem linearMap_eq_linearOfFun [Fintype ι] [DecidableEq ι] {V : Type*} [AddCommGroup V]
    [Module ℝ V] (f : RVec ι →ₗ[ℝ] V) : f = linearOfFun fun i => f (oneHot i) := by
  apply LinearMap.ext
  intro x
  conv_lhs => rw [← sum_smul_oneHot x]
  simp [map_sum, map_smul]

/-- A linear map applied to `x` is `∑ i, x i • f δ_i`. -/
theorem linearMap_apply_eq_sum [Fintype ι] [DecidableEq ι] {V : Type*} [AddCommGroup V]
    [Module ℝ V] (f : RVec ι →ₗ[ℝ] V) (x : RVec ι) : f x = ∑ i, x i • f (oneHot i) := by
  conv_lhs => rw [linearMap_eq_linearOfFun f]
  rfl

/-! ### Reindexing along a map of index types -/

/-- Restriction along `e : κ → ι`: read the coordinates `w (e k)`. When `e` is the inclusion of a
block of coordinates, this projects onto that block. -/
def restrictAlong {κ : Type*} (e : κ → ι) : RVec ι →ₗ[ℝ] RVec κ where
  toFun w := ofFun fun k => w (e k)
  map_add' x y := by ext k; simp [ofFun]
  map_smul' c x := by ext k; simp [ofFun]

@[simp] theorem restrictAlong_apply {κ : Type*} (e : κ → ι) (w : RVec ι) (k : κ) :
    restrictAlong e w k = w (e k) := rfl

/-- Extension along `e : κ → ι`: `v ↦ ∑ k, v k • δ_{e k}`. When `e` is injective this copies `v k`
into coordinate `e k` and puts `0` everywhere else (extension by zero). -/
noncomputable def extendAlong [DecidableEq ι] {κ : Type*} [Fintype κ] (e : κ → ι) :
    RVec κ →ₗ[ℝ] RVec ι :=
  linearOfFun fun k => oneHot (e k)

/-- Coordinate `i` of an extension sums the entries that land on `i`. -/
theorem extendAlong_apply [DecidableEq ι] {κ : Type*} [Fintype κ] (e : κ → ι) (v : RVec κ)
    (i : ι) : extendAlong e v i = ∑ k, if e k = i then v k else 0 := by
  simp [extendAlong, Finset.sum_apply, eq_comm]

/-- For injective `e`, coordinate `e k` of the extension is `v k`. -/
theorem extendAlong_apply_self [DecidableEq ι] {κ : Type*} [Fintype κ] {e : κ → ι}
    (he : Function.Injective e) (v : RVec κ) (k : κ) : extendAlong e v (e k) = v k := by
  rw [extendAlong_apply,
    Finset.sum_eq_single k (fun b _ hb => by rw [if_neg (fun h => hb (he h))]) (by simp)]
  simp

/-- Coordinates outside the range of `e` are zero in the extension. -/
theorem extendAlong_apply_of_forall_ne [DecidableEq ι] {κ : Type*} [Fintype κ] {e : κ → ι}
    (v : RVec κ) {i : ι} (hi : ∀ k, e k ≠ i) : extendAlong e v i = 0 := by
  rw [extendAlong_apply]
  exact Finset.sum_eq_zero fun k _ => by simp [hi k]

/-- Extension along `e` is adjoint to restriction along `e`:
`⟪extendAlong e v, w⟫ = ⟪v, restrictAlong e w⟫`. -/
theorem inner_extendAlong_left [Fintype ι] [DecidableEq ι] {κ : Type*} [Fintype κ]
    (e : κ → ι) (v : RVec κ) (w : RVec ι) :
    ⟪extendAlong e v, w⟫_ℝ = ⟪v, restrictAlong e w⟫_ℝ := by
  simp only [extendAlong, linearOfFun_apply, sum_inner, real_inner_smul_left,
    inner_oneHot_left]
  rw [inner_eq_sum]
  rfl

/-- For injective `e`, restricting an extension recovers the original vector. -/
theorem restrictAlong_extendAlong [DecidableEq ι] {κ : Type*} [Fintype κ] {e : κ → ι}
    (he : Function.Injective e) (v : RVec κ) : restrictAlong e (extendAlong e v) = v := by
  ext k
  simp [extendAlong_apply_self he]

/-- For injective `e`, extension preserves inner products. This follows from adjointness and
`restrictAlong_extendAlong`: `⟪E v, E w⟫ = ⟪v, R (E w)⟫ = ⟪v, w⟫`. -/
theorem inner_extendAlong [Fintype ι] [DecidableEq ι] {κ : Type*} [Fintype κ] {e : κ → ι}
    (he : Function.Injective e) (v w : RVec κ) :
    ⟪extendAlong e v, extendAlong e w⟫_ℝ = ⟪v, w⟫_ℝ := by
  rw [inner_extendAlong_left, restrictAlong_extendAlong he]

end RVec

/-! ### Stream operations -/

namespace Stream

variable {P V : Type*}

/-- Replace the vector at position `p` by `v`, leaving every other position unchanged. -/
def update [DecidableEq P] (X : Stream P V) (p : P) (v : V) : Stream P V :=
  Function.update X p v

@[simp] theorem update_same [DecidableEq P] (X : Stream P V) (p : P) (v : V) :
    X.update p v p = v := by simp [update]

/-- Updating position `p` does not change any other position `q`. -/
theorem update_of_ne [DecidableEq P] (X : Stream P V) {p q : P} (h : q ≠ p) (v : V) :
    X.update p v q = X q := by simp [update, h]

/-- Apply a map `f` at every position. -/
def mapPos {W : Type*} (f : V → W) (X : Stream P V) : Stream P W := fun p => f (X p)

@[simp] theorem mapPos_apply {W : Type*} (f : V → W) (X : Stream P V) (p : P) :
    mapPos f X p = f (X p) := rfl

end Stream

end MechInterp

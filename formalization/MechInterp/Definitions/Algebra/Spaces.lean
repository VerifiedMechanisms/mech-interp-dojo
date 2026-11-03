import Mathlib.Analysis.InnerProductSpace.PiL2

set_option linter.style.header false

/-!
# Spaces and streams

* `RVec ι`: the Euclidean space indexed by a finite type `ι`.
* `Vec d`: the case `ι = Fin d`, kept for compatibility with dimension-indexed code.
* `Stream P V`: a residual stream, one vector per position.

Coordinates are written `x i`. One-hot vectors, the all-ones vector, the coordinatewise
product, coordinatewise maps, and the linear map determined by basis images are defined
here because embeddings, neurons, and normalizations are basis-dependent.
-/

namespace MechInterp

/-- The Euclidean space indexed by a finite type `ι`. -/
abbrev RVec (ι : Type*) := EuclideanSpace ℝ ι

/-- The standard `d`-dimensional real inner product space. -/
abbrev Vec (d : ℕ) := RVec (Fin d)

/-- A residual stream: one vector per position. -/
abbrev Stream (P V : Type*) := P → V

namespace RVec

variable {ι : Type*}

/-- The vector with coordinates `f`. -/
def ofFun (f : ι → ℝ) : RVec ι := WithLp.toLp 2 f

/-- The one-hot vector at index `i`. -/
noncomputable def oneHot [DecidableEq ι] (i : ι) : RVec ι := EuclideanSpace.single i 1

/-- The all-ones vector. -/
def ones : RVec ι := ofFun fun _ => 1

/-- Coordinatewise (Hadamard) product. -/
def hadamard (x y : RVec ι) : RVec ι := ofFun fun i => x i * y i

/-- Apply a scalar function to every coordinate. -/
def map (f : ℝ → ℝ) (x : RVec ι) : RVec ι := ofFun fun i => f (x i)

/-- The number of nonzero coordinates. -/
noncomputable def l0 [Fintype ι] (x : RVec ι) : ℕ := by
  classical exact (Finset.univ.filter fun i => x i ≠ 0).card

/-- The linear map sending the coordinate vector `x` to `∑ i, x i • e i`. -/
noncomputable def linearOfFun [Fintype ι] {V : Type*} [AddCommGroup V] [Module ℝ V]
    (e : ι → V) : RVec ι →ₗ[ℝ] V where
  toFun x := ∑ i, x i • e i
  map_add' x y := by
    simp only [PiLp.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [PiLp.smul_apply, smul_eq_mul, mul_smul, RingHom.id_apply, Finset.smul_sum]

/-- Read the coordinates selected by an index map `e : κ → ι`. -/
def restrictAlong {κ : Type*} (e : κ → ι) : RVec ι →ₗ[ℝ] RVec κ where
  toFun w := ofFun fun k => w (e k)
  map_add' x y := by ext k; simp [ofFun]
  map_smul' c x := by ext k; simp [ofFun]

/-- Place coordinates along an index map `e : κ → ι`: `v ↦ ∑ k, v k • oneHot (e k)`.
For injective `e` this is extension by zero. -/
noncomputable def extendAlong [DecidableEq ι] {κ : Type*} [Fintype κ] (e : κ → ι) :
    RVec κ →ₗ[ℝ] RVec ι :=
  linearOfFun fun k => oneHot (e k)

end RVec

namespace Stream

variable {P V : Type*}

/-- Replace the vector at one position. -/
def update [DecidableEq P] (X : Stream P V) (p : P) (v : V) : Stream P V :=
  Function.update X p v

/-- Apply a map to every position. -/
def mapPos {W : Type*} (f : V → W) (X : Stream P V) : Stream P W := fun p => f (X p)

end Stream

end MechInterp

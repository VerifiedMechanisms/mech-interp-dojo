import MechInterp.Theorems.Algebra.Spaces
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

set_option linter.style.header false

/-!
# Rank, factorization, and Frobenius norms

A bilinear form is *QK-realizable at rank `r`* when it factors as `⟪Q u, K v⟫` through
`ℝ^r`. A linear map is *OV-realizable at rank `r`* when it factors through `ℝ^r`. The rank
theorems in `Theorems/Algebra/Rank` characterize both by rank bounds, which is exactly the
constraint a head of query/key width `r` (or value width `r`) imposes.

The Frobenius norm of a linear map between Euclidean spaces is the root of the sum of
squared matrix entries `(f (oneHot i)) k`.
-/

namespace MechInterp

open scoped InnerProductSpace

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

/-- The rank of a linear map: the dimension of its range. -/
noncomputable def linRank (M : V →ₗ[ℝ] W) : ℕ := Module.finrank ℝ (LinearMap.range M)

/-- The rank of a bilinear form `B`, viewed as a linear map into functionals. -/
noncomputable def bilinRank (B : V →ₗ[ℝ] W →ₗ[ℝ] ℝ) : ℕ := linRank B

/-- `B u v = ⟪Q u, K v⟫` for linear `Q`, `K` into `ℝ^r`. -/
def QKRealizable (B : V →ₗ[ℝ] W →ₗ[ℝ] ℝ) (r : ℕ) : Prop :=
  ∃ (Q : V →ₗ[ℝ] Vec r) (K : W →ₗ[ℝ] Vec r), ∀ u v, B u v = ⟪Q u, K v⟫_ℝ

/-- `M = O ∘ W` for linear `W : V → ℝ^r` and `O : ℝ^r → W`. -/
def OVRealizable (M : V →ₗ[ℝ] W) (r : ℕ) : Prop :=
  ∃ (Wv : V →ₗ[ℝ] Vec r) (O : Vec r →ₗ[ℝ] W), M = O ∘ₗ Wv

section Frobenius

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

/-- Squared Frobenius norm of a linear map between Euclidean spaces. -/
noncomputable def frobeniusNormSq (f : RVec ι →ₗ[ℝ] RVec κ) : ℝ :=
  ∑ i, ∑ k, (f (RVec.oneHot i) k) ^ 2

/-- Frobenius norm of a linear map between Euclidean spaces. -/
noncomputable def frobeniusNorm (f : RVec ι →ₗ[ℝ] RVec κ) : ℝ := √(frobeniusNormSq f)

/-- The composition score `‖M N‖_F / (‖M‖_F ‖N‖_F)`. -/
noncomputable def compositionScore {μ : Type*} [Fintype μ] [DecidableEq κ]
    (M : RVec κ →ₗ[ℝ] RVec μ) (N : RVec ι →ₗ[ℝ] RVec κ) : ℝ :=
  frobeniusNorm (M ∘ₗ N) / (frobeniusNorm M * frobeniusNorm N)

end Frobenius

end MechInterp

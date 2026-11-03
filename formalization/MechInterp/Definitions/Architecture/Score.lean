import MechInterp.Theorems.Algebra.Spaces
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

set_option linter.style.header false

/-!
# Score rules

For queries `q_i` and keys `k_j`, the score is `s_ij = c ⟪R_i q_i, R'_j k_j⟫ + b_ij`, with a
scale `c`, position-dependent isometries `R_i`, `R'_j` (identity by default), and a positional
bias `b_ij` (zero by default). Standard, ALiBi, and RoPE rules are instances.
-/

namespace MechInterp

open scoped InnerProductSpace

/-- A score rule with scale, query/key rotations, and positional bias. -/
structure ScoreRule (Pdst Psrc K : Type*) [NormedAddCommGroup K] [InnerProductSpace ℝ K] where
  scale : ℝ
  qRot : Pdst → K →ₗᵢ[ℝ] K
  kRot : Psrc → K →ₗᵢ[ℝ] K
  bias : Pdst → Psrc → ℝ

namespace ScoreRule

variable {Pdst Psrc P K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K]

/-- The score of query `q` at destination `i` against key `k` at source `j`. -/
def score (σ : ScoreRule Pdst Psrc K) (i : Pdst) (j : Psrc) (q k : K) : ℝ :=
  σ.scale * ⟪σ.qRot i q, σ.kRot j k⟫_ℝ + σ.bias i j

/-- Dot-product scores with scale `c`, no rotations, and no bias. -/
def standard (c : ℝ) : ScoreRule Pdst Psrc K :=
  ⟨c, fun _ => LinearIsometry.id, fun _ => LinearIsometry.id, fun _ _ => 0⟩

/-- Replace the positional bias. -/
def withBias (σ : ScoreRule Pdst Psrc K) (b : Pdst → Psrc → ℝ) : ScoreRule Pdst Psrc K :=
  { σ with bias := b }

/-- ALiBi: dot-product scores with linear distance penalty `-m (ord i - ord j)`. -/
def alibi (ord : P → ℕ) (m c : ℝ) : ScoreRule P P K :=
  (standard c).withBias fun i j => -m * ((ord i : ℝ) - ord j)

/-- No rotation depends on position and the bias is constant. -/
def PositionFree (σ : ScoreRule Pdst Psrc K) : Prop :=
  (∀ i i', σ.qRot i = σ.qRot i') ∧ (∀ j j', σ.kRot j = σ.kRot j') ∧
    ∀ i j i' j', σ.bias i j = σ.bias i' j'

/-- Keys are not rotated in a position-dependent way. -/
def KeyRotationFree (σ : ScoreRule Pdst Psrc K) : Prop := ∀ j j', σ.kRot j = σ.kRot j'

/-- Rotate each plane `(x_{k,0}, x_{k,1})` of `ℝ^{m × 2}` by angle `φ k`. -/
noncomputable def planeRotation {m : ℕ} (φ : Fin m → ℝ) :
    RVec (Fin m × Fin 2) →ₗᵢ[ℝ] RVec (Fin m × Fin 2) :=
  LinearMap.isometryOfInner
    { toFun := fun x => RVec.ofFun fun kc =>
        if kc.2 = 0 then Real.cos (φ kc.1) * x (kc.1, 0) - Real.sin (φ kc.1) * x (kc.1, 1)
        else Real.sin (φ kc.1) * x (kc.1, 0) + Real.cos (φ kc.1) * x (kc.1, 1)
      map_add' := fun x y => by
        ext kc
        simp only [RVec.ofFun_apply, PiLp.add_apply]
        split_ifs <;> ring
      map_smul' := fun a x => by
        ext kc
        simp only [RVec.ofFun_apply, PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]
        split_ifs <;> ring }
    (fun x y => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, RVec.inner_eq_sum, RVec.ofFun_apply,
        Fintype.sum_prod_type, Fin.sum_univ_two, if_true, one_ne_zero, if_false]
      refine Finset.sum_congr rfl fun k _ => ?_
      have h := Real.sin_sq_add_cos_sq (φ k)
      linear_combination (x (k, 0) * y (k, 0) + x (k, 1) * y (k, 1)) * h)

/-- RoPE: queries and keys are rotated by angles `pos · θ_k` in each plane. -/
noncomputable def rope {m : ℕ} (posQ : Pdst → ℝ) (posK : Psrc → ℝ) (θ : Fin m → ℝ) (c : ℝ) :
    ScoreRule Pdst Psrc (RVec (Fin m × Fin 2)) :=
  ⟨c, fun i => planeRotation fun k => posQ i * θ k,
    fun j => planeRotation fun k => posK j * θ k, fun _ _ => 0⟩

end ScoreRule

end MechInterp

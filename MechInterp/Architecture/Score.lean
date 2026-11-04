/-
Copyright (c) 2026 Malhar A. Patel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Malhar A. Patel
-/
import MechInterp.Algebra.Spaces
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Attention score rules: dot products, ALiBi, and RoPE

An attention head compares the query `q_i` at a destination position `i` with the key `k_j` at
a source position `j`. A *score rule* fixes how: it computes

  `s_ij = c · ⟪R_i q_i, R'_j k_j⟫ + b_ij`,

where `c` is a scale, `R_i` and `R'_j` are position-dependent linear isometries of the query/key
space (the identity unless positions are encoded by rotation), and `b_ij` is a positional score
bias (zero unless positions are encoded additively).

## Main definitions

* `ScoreRule Pdst Psrc K` and its evaluation `ScoreRule.score`.
* `ScoreRule.standard c`: scaled dot products, for example with `c = 1 / √(dim K)`.
* `ScoreRule.alibi ord m c`: dot products plus the ALiBi penalty `-m (ord i - ord j)`.
* `ScoreRule.planeRotation φ`: rotation of each coordinate plane of `ℝ^{m × 2}` by `φ k`.
* `ScoreRule.rope posQ posK θ c`: rotary position embeddings (RoPE), which rotate the query at
  `i` by angles `posQ i · θ_k` and the key at `j` by `posK j · θ_k`.
* `ScoreRule.PositionFree`, `ScoreRule.KeyRotationFree`: the rule ignores positions (entirely, or
  only on the key side).

## Main results

* `inner_planeRotation_planeRotation` (**RoPE relativity**): `⟪R_a q, R_b k⟫ = ⟪q, R_{b-a} k⟫`.
* `score_rope`, `score_rope_eq_of_offset_eq`: RoPE scores depend on positions only through the
  relative offset `posK j - posQ i`.
* `alibi_bias_eq_of_offset_eq`: ALiBi biases depend only on `ord i - ord j`.
-/

namespace MechInterp

open scoped InnerProductSpace

/-- A score rule `s_ij = scale · ⟪qRot i q, kRot j k⟫ + bias i j`. -/
structure ScoreRule (Pdst Psrc K : Type*) [NormedAddCommGroup K] [InnerProductSpace ℝ K] where
  /-- The scale `c` multiplying the inner product. -/
  scale : ℝ
  /-- The isometry applied to the query at each destination position. -/
  qRot : Pdst → K →ₗᵢ[ℝ] K
  /-- The isometry applied to the key at each source position. -/
  kRot : Psrc → K →ₗᵢ[ℝ] K
  /-- The additive positional bias `b_ij`. -/
  bias : Pdst → Psrc → ℝ

namespace ScoreRule

variable {Pdst Psrc P K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K]

/-! ### Scores and simple rules -/

/-- The score of the query `q` at destination `i` against the key `k` at source `j`. -/
def score (σ : ScoreRule Pdst Psrc K) (i : Pdst) (j : Psrc) (q k : K) : ℝ :=
  σ.scale * ⟪σ.qRot i q, σ.kRot j k⟫_ℝ + σ.bias i j

/-- Scaled dot-product scores `c · ⟪q, k⟫`, with no rotations and no bias. -/
def standard (c : ℝ) : ScoreRule Pdst Psrc K :=
  ⟨c, fun _ => LinearIsometry.id, fun _ => LinearIsometry.id, fun _ _ => 0⟩

/-- The same rule with its positional bias replaced by `b`. -/
def withBias (σ : ScoreRule Pdst Psrc K) (b : Pdst → Psrc → ℝ) : ScoreRule Pdst Psrc K :=
  { σ with bias := b }

/-- ALiBi: scaled dot products plus the linear distance penalty `-m (ord i - ord j)`. -/
def alibi (ord : P → ℕ) (m c : ℝ) : ScoreRule P P K :=
  (standard c).withBias fun i j => -m * ((ord i : ℝ) - ord j)

/-- A rule is **position-free** when neither rotation depends on position and the bias is
constant. Such a rule sees only the query and key vectors. -/
def PositionFree (σ : ScoreRule Pdst Psrc K) : Prop :=
  (∀ i i', σ.qRot i = σ.qRot i') ∧ (∀ j j', σ.kRot j = σ.kRot j') ∧
    ∀ i j i' j', σ.bias i j = σ.bias i' j'

/-- A rule is **key-rotation-free** when the key rotation does not depend on position. -/
def KeyRotationFree (σ : ScoreRule Pdst Psrc K) : Prop := ∀ j j', σ.kRot j = σ.kRot j'

/-- Standard scores are scaled dot products. -/
@[simp] theorem score_standard (c : ℝ) (i : Pdst) (j : Psrc) (q k : K) :
    (standard c : ScoreRule Pdst Psrc K).score i j q k = c * ⟪q, k⟫_ℝ := by
  simp [score, standard]

/-- Standard scores are position-free. -/
theorem standard_positionFree (c : ℝ) : (standard c : ScoreRule Pdst Psrc K).PositionFree :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ _ _ => rfl⟩

/-- A position-free rule is in particular key-rotation-free. -/
theorem PositionFree.keyRotationFree {σ : ScoreRule Pdst Psrc K} (h : σ.PositionFree) :
    σ.KeyRotationFree :=
  h.2.1

theorem score_withBias (σ : ScoreRule Pdst Psrc K) (b : Pdst → Psrc → ℝ) (i : Pdst) (j : Psrc)
    (q k : K) : (σ.withBias b).score i j q k = σ.scale * ⟪σ.qRot i q, σ.kRot j k⟫_ℝ + b i j :=
  rfl

/-- ALiBi biases depend only on the offset `ord i - ord j`. -/
theorem alibi_bias_eq_of_offset_eq (ord : P → ℕ) (m c : ℝ) {i j i' j' : P}
    (h : (ord i : ℝ) - ord j = (ord i' : ℝ) - ord j') :
    (alibi ord m c : ScoreRule P P K).bias i j = (alibi ord m c : ScoreRule P P K).bias i' j' := by
  simp only [alibi, withBias]
  rw [h]

/-! ### Rotary position embeddings (RoPE) -/

/-- Rotate each coordinate plane `(x_{k,0}, x_{k,1})` of `ℝ^{m × 2}` by the angle `φ k`:

  `x_{k,0} ↦ cos φ_k · x_{k,0} - sin φ_k · x_{k,1}`,
  `x_{k,1} ↦ sin φ_k · x_{k,0} + cos φ_k · x_{k,1}`.

It is a linear isometry because `sin² + cos² = 1` in each plane. -/
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
      -- In each plane, the rotated inner product is the original one times `sin² + cos²`.
      simp only [LinearMap.coe_mk, AddHom.coe_mk, RVec.inner_eq_sum, RVec.ofFun_apply,
        Fintype.sum_prod_type, Fin.sum_univ_two, if_true, one_ne_zero, if_false]
      refine Finset.sum_congr rfl fun k _ => ?_
      have h := Real.sin_sq_add_cos_sq (φ k)
      linear_combination (x (k, 0) * y (k, 0) + x (k, 1) * y (k, 1)) * h)

/-- RoPE with frequencies `θ`: the query at destination `i` is rotated by angles `posQ i · θ_k`,
the key at source `j` by angles `posK j · θ_k`, and there is no additive bias. -/
noncomputable def rope {m : ℕ} (posQ : Pdst → ℝ) (posK : Psrc → ℝ) (θ : Fin m → ℝ) (c : ℝ) :
    ScoreRule Pdst Psrc (RVec (Fin m × Fin 2)) :=
  ⟨c, fun i => planeRotation fun k => posQ i * θ k,
    fun j => planeRotation fun k => posK j * θ k, fun _ _ => 0⟩

theorem planeRotation_apply {m : ℕ} (φ : Fin m → ℝ) (x : RVec (Fin m × Fin 2))
    (kc : Fin m × Fin 2) :
    planeRotation φ x kc =
      if kc.2 = 0 then Real.cos (φ kc.1) * x (kc.1, 0) - Real.sin (φ kc.1) * x (kc.1, 1)
      else Real.sin (φ kc.1) * x (kc.1, 0) + Real.cos (φ kc.1) * x (kc.1, 1) :=
  rfl

/-- **RoPE relativity.** Rotating the query by `a` and the key by `b` gives the same inner product
as rotating only the key by `b - a`. Plane by plane this is the angle-difference identities
`cos (b - a) = cos b cos a + sin b sin a` and `sin (b - a) = sin b cos a - cos b sin a`. -/
theorem inner_planeRotation_planeRotation {m : ℕ} (a b : Fin m → ℝ)
    (q k : RVec (Fin m × Fin 2)) :
    ⟪planeRotation a q, planeRotation b k⟫_ℝ = ⟪q, planeRotation (fun t => b t - a t) k⟫_ℝ := by
  simp only [RVec.inner_eq_sum, planeRotation_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
    if_true, one_ne_zero, if_false, Real.cos_sub, Real.sin_sub]
  refine Finset.sum_congr rfl fun t _ => ?_
  ring

/-- **RoPE scores are relative.** A RoPE score equals `c · ⟪q, R k⟫`, where `R` rotates by the
angles `(posK j - posQ i) · θ_k`. -/
theorem score_rope {m : ℕ} (posQ : Pdst → ℝ) (posK : Psrc → ℝ) (θ : Fin m → ℝ) (c : ℝ)
    (i : Pdst) (j : Psrc) (q k : RVec (Fin m × Fin 2)) :
    (rope posQ posK θ c).score i j q k =
      c * ⟪q, planeRotation (fun t => (posK j - posQ i) * θ t) k⟫_ℝ := by
  simp only [score, rope, add_zero, inner_planeRotation_planeRotation, sub_mul]

/-- Two position pairs with the same offset `posK j - posQ i` give the same RoPE score. -/
theorem score_rope_eq_of_offset_eq {m : ℕ} (posQ : Pdst → ℝ) (posK : Psrc → ℝ) (θ : Fin m → ℝ)
    (c : ℝ) {i i' : Pdst} {j j' : Psrc} (h : posK j - posQ i = posK j' - posQ i')
    (q k : RVec (Fin m × Fin 2)) :
    (rope posQ posK θ c).score i j q k = (rope posQ posK θ c).score i' j' q k := by
  rw [score_rope, score_rope, h]

end ScoreRule

end MechInterp

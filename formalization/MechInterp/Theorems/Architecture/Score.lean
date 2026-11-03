import MechInterp.Definitions.Architecture.Score

set_option linter.style.header false

/-!
# Score-rule identities

* Standard scores are scaled dot products.
* ALiBi biases depend only on position offsets.
* **RoPE relativity**: `⟪R_i q, R_j k⟫ = ⟪q, R_{j-i} k⟫`, so RoPE scores depend on relative
  position only.
-/

namespace MechInterp

open scoped InnerProductSpace

namespace ScoreRule

variable {Pdst Psrc P K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K]

@[simp] theorem score_standard (c : ℝ) (i : Pdst) (j : Psrc) (q k : K) :
    (standard c : ScoreRule Pdst Psrc K).score i j q k = c * ⟪q, k⟫_ℝ := by
  simp [score, standard]

theorem standard_positionFree (c : ℝ) : (standard c : ScoreRule Pdst Psrc K).PositionFree :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ _ _ => rfl⟩

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

theorem planeRotation_apply {m : ℕ} (φ : Fin m → ℝ) (x : RVec (Fin m × Fin 2))
    (kc : Fin m × Fin 2) :
    planeRotation φ x kc =
      if kc.2 = 0 then Real.cos (φ kc.1) * x (kc.1, 0) - Real.sin (φ kc.1) * x (kc.1, 1)
      else Real.sin (φ kc.1) * x (kc.1, 0) + Real.cos (φ kc.1) * x (kc.1, 1) :=
  rfl

/-- **RoPE relativity.** Rotating queries by `a` and keys by `b` is the same as rotating only
the keys by `b - a`. -/
theorem inner_planeRotation_planeRotation {m : ℕ} (a b : Fin m → ℝ)
    (q k : RVec (Fin m × Fin 2)) :
    ⟪planeRotation a q, planeRotation b k⟫_ℝ = ⟪q, planeRotation (fun t => b t - a t) k⟫_ℝ := by
  simp only [RVec.inner_eq_sum, planeRotation_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
    if_true, one_ne_zero, if_false, Real.cos_sub, Real.sin_sub]
  refine Finset.sum_congr rfl fun t _ => ?_
  ring

/-- **RoPE relativity for scores.** RoPE scores depend on positions only through
`posK j - posQ i`. -/
theorem score_rope {m : ℕ} (posQ : Pdst → ℝ) (posK : Psrc → ℝ) (θ : Fin m → ℝ) (c : ℝ)
    (i : Pdst) (j : Psrc) (q k : RVec (Fin m × Fin 2)) :
    (rope posQ posK θ c).score i j q k =
      c * ⟪q, planeRotation (fun t => (posK j - posQ i) * θ t) k⟫_ℝ := by
  simp only [score, rope, add_zero, inner_planeRotation_planeRotation, sub_mul]

theorem score_rope_eq_of_offset_eq {m : ℕ} (posQ : Pdst → ℝ) (posK : Psrc → ℝ) (θ : Fin m → ℝ)
    (c : ℝ) {i i' : Pdst} {j j' : Psrc} (h : posK j - posQ i = posK j' - posQ i')
    (q k : RVec (Fin m × Fin 2)) :
    (rope posQ posK θ c).score i j q k = (rope posQ posK θ c).score i' j' q k := by
  rw [score_rope, score_rope, h]

end ScoreRule

end MechInterp

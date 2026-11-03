import MechInterp.Definitions.Architecture.Attention
import MechInterp.Theorems.Architecture.Softmax
import MechInterp.Theorems.Architecture.Pattern
import MechInterp.Theorems.Algebra.Affine

set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# Attention-head theorems

* The output projection commutes with mixing; for a fixed pattern the output is linear in
  the values when `W_V` is bias-free.
* A value bias passes through as the constant `W_O b_V`.
* A key bias does not change row-shift-invariant patterns (softmax, hardmax).
* Without positional information, attention is permutation equivariant.
* With a causal mask and a row-local rule, the output at `i` depends only on positions `≤ i`.
* Mixed values lie in the convex hull of the allowed values.
-/

namespace MechInterp

open scoped InnerProductSpace

namespace AttentionHead

variable {V K U Pdst Psrc : Type*} [AddCommGroup V] [Module ℝ V] [NormedAddCommGroup K]
  [InnerProductSpace ℝ K] [AddCommGroup U] [Module ℝ U] [Fintype Psrc]

theorem resultWith_apply (h : AttentionHead V K U) (A : Pdst → Psrc → ℝ) (Y : Stream Psrc V)
    (i : Pdst) : h.resultWith A Y i = ∑ j, A i j • h.WO (h.WV (Y j)) := by
  simp [resultWith, mixWith, mix, values, map_sum]

/-- The output projection commutes with mixing. -/
theorem resultWith_eq_mix (h : AttentionHead V K U) (A : Pdst → Psrc → ℝ) (Y : Stream Psrc V) :
    h.resultWith A Y = mix A fun j => h.WO (h.WV (Y j)) :=
  funext (h.resultWith_apply A Y)

theorem result_eq_resultWith (h : AttentionHead V K U) (σ : ScoreRule Pdst Psrc K)
    {M : Mask Pdst Psrc} (ρ : PatternRule Pdst Psrc M) (X : Stream Pdst V) (Y : Stream Psrc V) :
    h.result σ ρ X Y = h.resultWith (h.pattern σ ρ X Y).A Y := rfl

/-- For a fixed pattern and a bias-free `W_V`, the head output is additive in the values. -/
theorem resultWith_add (h : AttentionHead V K U) (hV : IsBiasFree h.WV) (A : Pdst → Psrc → ℝ)
    (Y Y' : Stream Psrc V) : h.resultWith A (Y + Y') = h.resultWith A Y + h.resultWith A Y' := by
  funext i
  simp only [resultWith_apply, Pi.add_apply, hV.apply_eq, map_add, smul_add,
    Finset.sum_add_distrib]

/-- For a fixed pattern and a bias-free `W_V`, the head output is homogeneous in the values. -/
theorem resultWith_smul (h : AttentionHead V K U) (hV : IsBiasFree h.WV) (A : Pdst → Psrc → ℝ)
    (c : ℝ) (Y : Stream Psrc V) : h.resultWith A (c • Y) = c • h.resultWith A Y := by
  funext i
  simp only [resultWith_apply, Pi.smul_apply, hV.apply_eq, map_smul, Finset.smul_sum]
  exact Finset.sum_congr rfl fun j _ => smul_comm _ _ _

/-- **Value bias passes through.** With a row-stochastic pattern, the head output is the
mixed OV image plus the constant `W_O b_V`. -/
theorem resultWith_pattern (h : AttentionHead V K U) (A : AttnPattern Pdst Psrc)
    (Y : Stream Psrc V) (i : Pdst) :
    h.resultWith A.A Y i = (∑ j, A.A i j • h.WOV (Y j)) + h.WO (bias h.WV) := by
  rw [resultWith_apply]
  have hsplit : ∀ j, A.A i j • h.WO (h.WV (Y j)) =
      A.A i j • h.WOV (Y j) + A.A i j • h.WO (bias h.WV) := by
    intro j
    rw [affine_apply_eq_linear_add_bias h.WV (Y j), map_add, smul_add]
    rfl
  rw [Finset.sum_congr rfl fun j _ => hsplit j, Finset.sum_add_distrib, ← Finset.sum_smul,
    A.row_sum, one_smul]

/-- **Key-bias invariance.** Shifting every key by a constant does not change the pattern of
a row-shift-invariant rule when keys are not rotated position-dependently. -/
theorem pattern_eq_of_key_shift (h h' : AttentionHead V K U) (σ : ScoreRule Pdst Psrc K)
    {M : Mask Pdst Psrc} (ρ : PatternRule Pdst Psrc M) (hρ : ρ.RowShiftInvariant)
    (R : K →ₗᵢ[ℝ] K) (hR : ∀ j, σ.kRot j = R) (δ : K) (hQ : h'.WQ = h.WQ)
    (hK : ∀ y, h'.WK y = h.WK y + δ) (X : Stream Pdst V) (Y : Stream Psrc V) :
    h'.pattern σ ρ X Y = h.pattern σ ρ X Y := by
  have hs : h'.scores σ X Y = fun i j =>
      h.scores σ X Y i j + σ.scale * ⟪σ.qRot i (h.queries X i), R δ⟫_ℝ := by
    funext i j
    simp only [scores, ScoreRule.score, keys, queries, hK, hQ, hR, map_add, inner_add_right]
    ring
  rw [pattern, pattern, hs, hρ]

/-- A key shift leaves head outputs unchanged under row-shift-invariant rules. -/
theorem result_eq_of_key_shift (h h' : AttentionHead V K U) (σ : ScoreRule Pdst Psrc K)
    {M : Mask Pdst Psrc} (ρ : PatternRule Pdst Psrc M) (hρ : ρ.RowShiftInvariant)
    (R : K →ₗᵢ[ℝ] K) (hR : ∀ j, σ.kRot j = R) (δ : K) (hQ : h'.WQ = h.WQ)
    (hK : ∀ y, h'.WK y = h.WK y + δ) (hV : h'.WV = h.WV) (hO : h'.WO = h.WO)
    (X : Stream Pdst V) (Y : Stream Psrc V) : h'.result σ ρ X Y = h.result σ ρ X Y := by
  rw [result, result, pattern_eq_of_key_shift h h' σ ρ hρ R hR δ hQ hK]
  funext i
  rw [resultWith_apply, resultWith_apply, hV, hO]

/-- Mixed values lie in the convex hull of the allowed values. -/
theorem z_mem_convexHull (h : AttentionHead V K U) (σ : ScoreRule Pdst Psrc K)
    {M : Mask Pdst Psrc} (ρ : PatternRule Pdst Psrc M) (X : Stream Pdst V) (Y : Stream Psrc V)
    (i : Pdst) : h.z σ ρ X Y i ∈ convexHull ℝ (h.values Y '' {j | M.allowed i j}) :=
  mix_mem_convexHull _ (ρ.supported _) _ i

section SelfAttention

variable {P : Type*} [Fintype P]

/-- **Permutation equivariance.** Without positional information, relabeling positions
relabels the outputs. -/
theorem result_perm (h : AttentionHead V K U) (σ : ScoreRule P P K) (hσ : σ.PositionFree)
    {M : Mask P P} (ρ : PatternRule P P M) (π : Equiv.Perm P) (hρ : ρ.PermEquivariant π)
    (X : Stream P V) : h.result σ ρ (X ∘ π) (X ∘ π) = h.result σ ρ X X ∘ π := by
  have hs : h.scores σ (X ∘ π) (X ∘ π) = fun i j => h.scores σ X X (π i) (π j) := by
    funext i j
    simp only [scores, ScoreRule.score, queries, keys, Function.comp_apply,
      hσ.1 i (π i), hσ.2.1 j (π j), hσ.2.2 i j (π i) (π j)]
  funext i
  simp only [result, pattern, Function.comp_apply, resultWith_apply, hs]
  rw [Finset.sum_congr rfl fun x _ => by rw [hρ (h.scores σ X X) i x]]
  exact Equiv.sum_comp π fun j => (ρ.toPattern (h.scores σ X X)).A (π i) j • h.WO (h.WV (X j))

/-- **Causal locality.** If the mask only looks backwards in `ord` and the rule is row-local,
the output at `i` depends only on the stream at positions `j` with `ord j ≤ ord i`. -/
theorem result_eq_of_agree_before (h : AttentionHead V K U) (σ : ScoreRule P P K)
    {M : Mask P P} (ρ : PatternRule P P M) (hρ : ρ.RowLocal) (ord : P → ℕ)
    (hM : ∀ i j, M.allowed i j → ord j ≤ ord i) {X X' : Stream P V} (i : P)
    (hX : ∀ j, ord j ≤ ord i → X j = X' j) : h.result σ ρ X X i = h.result σ ρ X' X' i := by
  have hrow : ∀ j, M.allowed i j → h.scores σ X X i j = h.scores σ X' X' i j := by
    intro j hj
    simp only [scores, queries, keys, hX i (le_refl _), hX j (hM i j hj)]
  have hA := hρ _ _ i hrow
  simp only [result, pattern, resultWith_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hj : M.allowed i j
  · rw [hA j, hX j (hM i j hj)]
  · rw [ρ.supported _ i j hj, ρ.supported _ i j hj, zero_smul, zero_smul]

end SelfAttention

end AttentionHead

section Equivariance

variable {P : Type*} [Fintype P]

/-- Full-mask softmax is permutation equivariant. -/
theorem softmaxRule_full_permEquivariant (β : ℝ) (hM : (Mask.full : Mask P P).WellFormed)
    (π : Equiv.Perm P) : (softmaxRule β hM).PermEquivariant π := by
  intro s i j
  have hset : ∀ i, (Mask.full : Mask P P).allowedSet i = Finset.univ := fun i => by
    ext j; simp [Mask.allowedSet, Mask.full]
  have hall : ∀ i j, (Mask.full : Mask P P).allowed i j := fun _ _ => trivial
  simp only [softmaxRule_A, maskedSoftmax, maskedDenom, hset, hall, if_true]
  congr 1
  exact Equiv.sum_comp π fun j => Real.exp (β * s (π i) j)

end Equivariance

end MechInterp

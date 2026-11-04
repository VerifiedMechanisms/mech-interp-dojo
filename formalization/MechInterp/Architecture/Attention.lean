/-
Copyright (c) 2026 Malhar A. Patel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Malhar A. Patel
-/
import MechInterp.Algebra.Affine
import MechInterp.Architecture.Score
import MechInterp.Architecture.Softmax

/-!
# Attention heads

An attention head has affine query, key, and value projections and a linear output projection:
`W_Q, W_K : V →ᵃ K`, `W_V : V →ᵃ U`, and `W_O : U →ₗ V`, where `V` is the residual space, `K` the
query/key space, and `U` the value space. Given a score rule `σ`, a mask `M`, a pattern rule `ρ`
for `M`, a destination stream `X`, and a source stream `Y` (self-attention is `X = Y`), the head
computes

  `q_i = W_Q X_i`, `k_j = W_K Y_j`, `v_j = W_V Y_j`,
  `s_ij = σ.score i j q_i k_j`, `A = ρ s`,
  `z_i = ∑ j, A_ij • v_j`, `y_i = W_O z_i`.

Every intermediate quantity is a named definition, because interpretability questions are often
about these quantities rather than only the output.

## Main definitions

* `AttentionHead V K U`: the four projections.
* `AttentionHead.queries`, `keys`, `values`, `scores`, `pattern`, `z`, `result`: the quantities
  above, under the live pattern `ρ s`.
* `AttentionHead.mixWith A Y`, `resultWith A Y`: the same computation with a *supplied* weight
  matrix `A`. Fixing `A` is what "freezing" an attention pattern means: with `A` fixed the head is
  an affine function of its input.
* `AttentionHead.resultWeights`: the output under raw weights from a `WeightRule`.
* `AttentionHead.WOV`: the OV circuit `W_O ∘ (W_V).linear`.
* `PatternRule.PermEquivariant ρ π`: relabeling positions by `π` relabels the pattern.

## Main results

* `resultWith_apply`: `y_i = ∑ j, A_ij • W_O (W_V Y_j)`, so `W_O` commutes with mixing.
* `resultWith_pattern` (**value bias passes through**): for a stochastic `A`,
  `y_i = ∑ j, A_ij • W_OV Y_j + W_O b_V`.
* `pattern_eq_of_key_shift`, `result_eq_of_key_shift` (**key bias is irrelevant**): shifting every
  key by a constant does not change the pattern of a row-shift-invariant rule.
* `z_mem_convexHull`: mixed values lie in the convex hull of the allowed values.
* `result_perm` (**permutation equivariance**): without positional information, relabeling
  positions relabels the outputs.
* `result_eq_of_agree_before` (**causal locality**): with a backward-looking mask and a row-local
  rule, the output at `i` depends only on positions `j` with `ord j ≤ ord i`.
-/

set_option linter.unusedSectionVars false

namespace MechInterp

open scoped InnerProductSpace

/-- The parameters of one attention head: affine query, key, and value projections and a linear
output projection. -/
structure AttentionHead (V K U : Type*) [AddCommGroup V] [Module ℝ V] [AddCommGroup K]
    [Module ℝ K] [AddCommGroup U] [Module ℝ U] where
  /-- The query projection `W_Q`. -/
  WQ : V →ᵃ[ℝ] K
  /-- The key projection `W_K`. -/
  WK : V →ᵃ[ℝ] K
  /-- The value projection `W_V`. -/
  WV : V →ᵃ[ℝ] U
  /-- The output projection `W_O`. -/
  WO : U →ₗ[ℝ] V

namespace AttentionHead

variable {V K U Pdst Psrc : Type*} [AddCommGroup V] [Module ℝ V] [NormedAddCommGroup K]
  [InnerProductSpace ℝ K] [AddCommGroup U] [Module ℝ U] [Fintype Psrc]

/-! ### The forward pass -/

/-- The queries `q_i = W_Q X_i`. -/
def queries (h : AttentionHead V K U) (X : Stream Pdst V) : Stream Pdst K := fun i => h.WQ (X i)

/-- The keys `k_j = W_K Y_j`. -/
def keys (h : AttentionHead V K U) (Y : Stream Psrc V) : Stream Psrc K := fun j => h.WK (Y j)

/-- The values `v_j = W_V Y_j`. -/
def values (h : AttentionHead V K U) (Y : Stream Psrc V) : Stream Psrc U := fun j => h.WV (Y j)

/-- The scores `s_ij = σ.score i j q_i k_j`. -/
def scores (h : AttentionHead V K U) (σ : ScoreRule Pdst Psrc K) (X : Stream Pdst V)
    (Y : Stream Psrc V) : Pdst → Psrc → ℝ :=
  fun i j => σ.score i j (h.queries X i) (h.keys Y j)

/-- The attention pattern `A = ρ s` produced by the pattern rule from the scores. -/
def pattern (h : AttentionHead V K U) (σ : ScoreRule Pdst Psrc K) {M : Mask Pdst Psrc}
    (ρ : PatternRule Pdst Psrc M) (X : Stream Pdst V) (Y : Stream Psrc V) :
    AttnPattern Pdst Psrc :=
  ρ.toPattern (h.scores σ X Y)

/-- The mixed values `z_i = ∑ j, A_ij • v_j` for a supplied weight matrix `A`. -/
def mixWith (h : AttentionHead V K U) (A : Pdst → Psrc → ℝ) (Y : Stream Psrc V) :
    Stream Pdst U :=
  mix A (h.values Y)

/-- The mixed values `z` under the live pattern. -/
def z (h : AttentionHead V K U) (σ : ScoreRule Pdst Psrc K) {M : Mask Pdst Psrc}
    (ρ : PatternRule Pdst Psrc M) (X : Stream Pdst V) (Y : Stream Psrc V) : Stream Pdst U :=
  h.mixWith (h.pattern σ ρ X Y).A Y

/-- The head output `y_i = W_O z_i` for a supplied weight matrix `A`. -/
def resultWith (h : AttentionHead V K U) (A : Pdst → Psrc → ℝ) (Y : Stream Psrc V) :
    Stream Pdst V :=
  fun i => h.WO (h.mixWith A Y i)

/-- The head output under the live pattern. -/
def result (h : AttentionHead V K U) (σ : ScoreRule Pdst Psrc K) {M : Mask Pdst Psrc}
    (ρ : PatternRule Pdst Psrc M) (X : Stream Pdst V) (Y : Stream Psrc V) : Stream Pdst V :=
  h.resultWith (h.pattern σ ρ X Y).A Y

/-- The head output under raw (unnormalized) weights from a weight rule. -/
def resultWeights (h : AttentionHead V K U) (σ : ScoreRule Pdst Psrc K)
    (w : WeightRule Pdst Psrc) (X : Stream Pdst V) (Y : Stream Psrc V) : Stream Pdst V :=
  h.resultWith (w.toWeights (h.scores σ X Y)) Y

/-- The OV circuit `W_O ∘ W_V`, using the linear part of `W_V`. -/
def WOV (h : AttentionHead V K U) : V →ₗ[ℝ] V := h.WO ∘ₗ h.WV.linear

/-- All three input projections `W_Q`, `W_K`, `W_V` are bias-free. -/
def BiasFree (h : AttentionHead V K U) : Prop :=
  IsBiasFree h.WQ ∧ IsBiasFree h.WK ∧ IsBiasFree h.WV

/-! ### The output as a mixture of OV images -/

/-- The head output is the mixture of the OV images: `y_i = ∑ j, A_ij • W_O (W_V Y_j)`. -/
theorem resultWith_apply (h : AttentionHead V K U) (A : Pdst → Psrc → ℝ) (Y : Stream Psrc V)
    (i : Pdst) : h.resultWith A Y i = ∑ j, A i j • h.WO (h.WV (Y j)) := by
  simp [resultWith, mixWith, mix, values, map_sum]

/-- The output projection commutes with mixing. -/
theorem resultWith_eq_mix (h : AttentionHead V K U) (A : Pdst → Psrc → ℝ) (Y : Stream Psrc V) :
    h.resultWith A Y = mix A fun j => h.WO (h.WV (Y j)) :=
  funext (h.resultWith_apply A Y)

/-- The live output is the output with the live pattern supplied. -/
theorem result_eq_resultWith (h : AttentionHead V K U) (σ : ScoreRule Pdst Psrc K)
    {M : Mask Pdst Psrc} (ρ : PatternRule Pdst Psrc M) (X : Stream Pdst V) (Y : Stream Psrc V) :
    h.result σ ρ X Y = h.resultWith (h.pattern σ ρ X Y).A Y := rfl

/-- For a fixed pattern and a bias-free `W_V`, the head output is additive in the source
stream. -/
theorem resultWith_add (h : AttentionHead V K U) (hV : IsBiasFree h.WV) (A : Pdst → Psrc → ℝ)
    (Y Y' : Stream Psrc V) : h.resultWith A (Y + Y') = h.resultWith A Y + h.resultWith A Y' := by
  funext i
  simp only [resultWith_apply, Pi.add_apply, hV.apply_eq, map_add, smul_add,
    Finset.sum_add_distrib]

/-- For a fixed pattern and a bias-free `W_V`, the head output is homogeneous in the source
stream. -/
theorem resultWith_smul (h : AttentionHead V K U) (hV : IsBiasFree h.WV) (A : Pdst → Psrc → ℝ)
    (c : ℝ) (Y : Stream Psrc V) : h.resultWith A (c • Y) = c • h.resultWith A Y := by
  funext i
  simp only [resultWith_apply, Pi.smul_apply, hV.apply_eq, map_smul, Finset.smul_sum]
  exact Finset.sum_congr rfl fun j _ => smul_comm _ _ _

/-- **Value bias passes through.** With a row-stochastic pattern, the head output is the mixed OV
image plus the constant `W_O b_V`: since the weights sum to one, the bias contributes
`∑ j, A_ij • W_O b_V = W_O b_V`. -/
theorem resultWith_pattern (h : AttentionHead V K U) (A : AttnPattern Pdst Psrc)
    (Y : Stream Psrc V) (i : Pdst) :
    h.resultWith A.A Y i = (∑ j, A.A i j • h.WOV (Y j)) + h.WO (bias h.WV) := by
  rw [resultWith_apply]
  -- Split each value into its linear part and the bias.
  have hsplit : ∀ j, A.A i j • h.WO (h.WV (Y j)) =
      A.A i j • h.WOV (Y j) + A.A i j • h.WO (bias h.WV) := by
    intro j
    rw [affine_apply_eq_linear_add_bias h.WV (Y j), map_add, smul_add]
    rfl
  rw [Finset.sum_congr rfl fun j _ => hsplit j, Finset.sum_add_distrib, ← Finset.sum_smul,
    A.row_sum, one_smul]

/-! ### Invariances of a single head -/

/-- **Key-bias invariance.** Shift every key by a constant `δ` (`h'.WK y = h.WK y + δ`), keeping
the queries. If keys are rotated by the same isometry `R` at every position, each score in row `i`
changes by `scale · ⟪qRot i q_i, R δ⟫`, which does not depend on `j`. A row-shift-invariant rule
(such as softmax) therefore produces the same pattern. -/
theorem pattern_eq_of_key_shift (h h' : AttentionHead V K U) (σ : ScoreRule Pdst Psrc K)
    {M : Mask Pdst Psrc} (ρ : PatternRule Pdst Psrc M) (hρ : ρ.RowShiftInvariant)
    (R : K →ₗᵢ[ℝ] K) (hR : ∀ j, σ.kRot j = R) (δ : K) (hQ : h'.WQ = h.WQ)
    (hK : ∀ y, h'.WK y = h.WK y + δ) (X : Stream Pdst V) (Y : Stream Psrc V) :
    h'.pattern σ ρ X Y = h.pattern σ ρ X Y := by
  -- The shifted scores are the original scores plus a row constant.
  have hs : h'.scores σ X Y = fun i j =>
      h.scores σ X Y i j + σ.scale * ⟪σ.qRot i (h.queries X i), R δ⟫_ℝ := by
    funext i j
    simp only [scores, ScoreRule.score, keys, queries, hK, hQ, hR, map_add, inner_add_right]
    ring
  rw [pattern, pattern, hs, hρ]

/-- A key shift leaves the head output unchanged under a row-shift-invariant rule, when the two
heads also share `W_V` and `W_O`: they then compute the same pattern and mix the same values. -/
theorem result_eq_of_key_shift (h h' : AttentionHead V K U) (σ : ScoreRule Pdst Psrc K)
    {M : Mask Pdst Psrc} (ρ : PatternRule Pdst Psrc M) (hρ : ρ.RowShiftInvariant)
    (R : K →ₗᵢ[ℝ] K) (hR : ∀ j, σ.kRot j = R) (δ : K) (hQ : h'.WQ = h.WQ)
    (hK : ∀ y, h'.WK y = h.WK y + δ) (hV : h'.WV = h.WV) (hO : h'.WO = h.WO)
    (X : Stream Pdst V) (Y : Stream Psrc V) : h'.result σ ρ X Y = h.result σ ρ X Y := by
  rw [result, result, pattern_eq_of_key_shift h h' σ ρ hρ R hR δ hQ hK]
  funext i
  rw [resultWith_apply, resultWith_apply, hV, hO]

/-- The mixed values lie in the convex hull of the values the destination may attend to. -/
theorem z_mem_convexHull (h : AttentionHead V K U) (σ : ScoreRule Pdst Psrc K)
    {M : Mask Pdst Psrc} (ρ : PatternRule Pdst Psrc M) (X : Stream Pdst V) (Y : Stream Psrc V)
    (i : Pdst) : h.z σ ρ X Y i ∈ convexHull ℝ (h.values Y '' {j | M.allowed i j}) :=
  mix_mem_convexHull _ (ρ.supported _) _ i

end AttentionHead

/-! ### Permutation equivariance -/

namespace PatternRule

variable {P : Type*} [Fintype P] {M : Mask P P}

/-- A pattern rule is **equivariant** under a permutation `π` of positions when relabeling the
scores by `π` relabels the pattern: `ρ (s ∘ (π × π)) = ρ s ∘ (π × π)`. -/
def PermEquivariant (ρ : PatternRule P P M) (π : Equiv.Perm P) : Prop :=
  ∀ s i j, (ρ.toPattern fun i j => s (π i) (π j)).A i j = (ρ.toPattern s).A (π i) (π j)

end PatternRule

namespace AttentionHead

variable {V K U : Type*} [AddCommGroup V] [Module ℝ V] [NormedAddCommGroup K]
  [InnerProductSpace ℝ K] [AddCommGroup U] [Module ℝ U]

section SelfAttention

variable {P : Type*} [Fintype P]

/-- **Permutation equivariance.** With a position-free score rule and a pattern rule that is
equivariant under `π`, self-attention on the relabeled stream `X ∘ π` gives the relabeled output
`result X ∘ π`. -/
theorem result_perm (h : AttentionHead V K U) (σ : ScoreRule P P K) (hσ : σ.PositionFree)
    {M : Mask P P} (ρ : PatternRule P P M) (π : Equiv.Perm P) (hρ : ρ.PermEquivariant π)
    (X : Stream P V) : h.result σ ρ (X ∘ π) (X ∘ π) = h.result σ ρ X X ∘ π := by
  -- The scores of the relabeled stream are the relabeled scores.
  have hs : h.scores σ (X ∘ π) (X ∘ π) = fun i j => h.scores σ X X (π i) (π j) := by
    funext i j
    simp only [scores, ScoreRule.score, queries, keys, Function.comp_apply,
      hσ.1 i (π i), hσ.2.1 j (π j), hσ.2.2 i j (π i) (π j)]
  funext i
  simp only [result, pattern, Function.comp_apply, resultWith_apply, hs]
  rw [Finset.sum_congr rfl fun x _ => by rw [hρ (h.scores σ X X) i x]]
  -- Reindex the sum over sources by `π`.
  exact Equiv.sum_comp π fun j => (ρ.toPattern (h.scores σ X X)).A (π i) j • h.WO (h.WV (X j))

/-- **Causal locality.** Suppose the mask only looks backwards in `ord`
(`M.allowed i j → ord j ≤ ord i`) and the rule is row-local. If two streams agree at every
position `j` with `ord j ≤ ord i`, the self-attention outputs at `i` agree. -/
theorem result_eq_of_agree_before (h : AttentionHead V K U) (σ : ScoreRule P P K)
    {M : Mask P P} (ρ : PatternRule P P M) (hρ : ρ.RowLocal) (ord : P → ℕ)
    (hM : ∀ i j, M.allowed i j → ord j ≤ ord i) {X X' : Stream P V} (i : P)
    (hX : ∀ j, ord j ≤ ord i → X j = X' j) : h.result σ ρ X X i = h.result σ ρ X' X' i := by
  -- Row `i` of the scores agrees on every allowed source.
  have hrow : ∀ j, M.allowed i j → h.scores σ X X i j = h.scores σ X' X' i j := by
    intro j hj
    simp only [scores, queries, keys, hX i (le_refl _), hX j (hM i j hj)]
  have hA := hρ _ _ i hrow
  simp only [result, pattern, resultWith_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hj : M.allowed i j
  · -- Allowed sources: same weight and same value.
    rw [hA j, hX j (hM i j hj)]
  · -- Disallowed sources: both weights are zero.
    rw [ρ.supported _ i j hj, ρ.supported _ i j hj, zero_smul, zero_smul]

end SelfAttention

end AttentionHead

section Equivariance

variable {P : Type*} [Fintype P]

/-- Softmax over the full mask is equivariant under every permutation of positions: relabeling
permutes the terms of each normalizer. -/
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

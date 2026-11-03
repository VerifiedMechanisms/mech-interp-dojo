import MechInterp.Definitions.Architecture.Score
import MechInterp.Definitions.Architecture.Softmax
import MechInterp.Definitions.Algebra.Affine

set_option linter.style.header false

/-!
# Attention heads

A head has affine query, key, and value projections and a linear output projection:
`W_Q, W_K : V →ᵃ K`, `W_V : V →ᵃ U`, `W_O : U →ₗ V`. For a destination stream `X` and a
source stream `Y` (self-attention when `X = Y`):

`q_i = W_Q X_i`, `k_j = W_K Y_j`, `v_j = W_V Y_j`, `s_ij = score(q_i, k_j)`, `A = rule(s)`,
`z_i = ∑ j, A_ij v_j`, `y_i = W_O z_i`.

Every intermediate quantity is a named definition. `resultWith` uses a supplied pattern and
is the basis of frozen semantics; `resultWeights` uses raw (unnormalized) weights.
-/

namespace MechInterp

/-- Parameters of one attention head. -/
structure AttentionHead (V K U : Type*) [AddCommGroup V] [Module ℝ V] [AddCommGroup K]
    [Module ℝ K] [AddCommGroup U] [Module ℝ U] where
  WQ : V →ᵃ[ℝ] K
  WK : V →ᵃ[ℝ] K
  WV : V →ᵃ[ℝ] U
  WO : U →ₗ[ℝ] V

namespace AttentionHead

variable {V K U Pdst Psrc : Type*} [AddCommGroup V] [Module ℝ V] [NormedAddCommGroup K]
  [InnerProductSpace ℝ K] [AddCommGroup U] [Module ℝ U] [Fintype Psrc]

/-- Queries `q_i = W_Q X_i`. -/
def queries (h : AttentionHead V K U) (X : Stream Pdst V) : Stream Pdst K := fun i => h.WQ (X i)

/-- Keys `k_j = W_K Y_j`. -/
def keys (h : AttentionHead V K U) (Y : Stream Psrc V) : Stream Psrc K := fun j => h.WK (Y j)

/-- Values `v_j = W_V Y_j`. -/
def values (h : AttentionHead V K U) (Y : Stream Psrc V) : Stream Psrc U := fun j => h.WV (Y j)

/-- Scores `s_ij = score(q_i, k_j)`. -/
def scores (h : AttentionHead V K U) (σ : ScoreRule Pdst Psrc K) (X : Stream Pdst V)
    (Y : Stream Psrc V) : Pdst → Psrc → ℝ :=
  fun i j => σ.score i j (h.queries X i) (h.keys Y j)

/-- The attention pattern produced by a pattern rule. -/
def pattern (h : AttentionHead V K U) (σ : ScoreRule Pdst Psrc K) {M : Mask Pdst Psrc}
    (ρ : PatternRule Pdst Psrc M) (X : Stream Pdst V) (Y : Stream Psrc V) :
    AttnPattern Pdst Psrc :=
  ρ.toPattern (h.scores σ X Y)

/-- Mixed values `z_i = ∑ j, A_ij v_j` for supplied weights. -/
def mixWith (h : AttentionHead V K U) (A : Pdst → Psrc → ℝ) (Y : Stream Psrc V) :
    Stream Pdst U :=
  mix A (h.values Y)

/-- Mixed values `z` under the live pattern. -/
def z (h : AttentionHead V K U) (σ : ScoreRule Pdst Psrc K) {M : Mask Pdst Psrc}
    (ρ : PatternRule Pdst Psrc M) (X : Stream Pdst V) (Y : Stream Psrc V) : Stream Pdst U :=
  h.mixWith (h.pattern σ ρ X Y).A Y

/-- Head output `y_i = W_O z_i` for supplied weights. -/
def resultWith (h : AttentionHead V K U) (A : Pdst → Psrc → ℝ) (Y : Stream Psrc V) :
    Stream Pdst V :=
  fun i => h.WO (h.mixWith A Y i)

/-- Head output under the live pattern. -/
def result (h : AttentionHead V K U) (σ : ScoreRule Pdst Psrc K) {M : Mask Pdst Psrc}
    (ρ : PatternRule Pdst Psrc M) (X : Stream Pdst V) (Y : Stream Psrc V) : Stream Pdst V :=
  h.resultWith (h.pattern σ ρ X Y).A Y

/-- Head output under raw (unnormalized) weights. -/
def resultWeights (h : AttentionHead V K U) (σ : ScoreRule Pdst Psrc K)
    (w : WeightRule Pdst Psrc) (X : Stream Pdst V) (Y : Stream Psrc V) : Stream Pdst V :=
  h.resultWith (w.toWeights (h.scores σ X Y)) Y

/-- The OV map `W_O ∘ W_V` (linear part). -/
def WOV (h : AttentionHead V K U) : V →ₗ[ℝ] V := h.WO ∘ₗ h.WV.linear

/-- All three projections are bias-free. -/
def BiasFree (h : AttentionHead V K U) : Prop :=
  IsBiasFree h.WQ ∧ IsBiasFree h.WK ∧ IsBiasFree h.WV

end AttentionHead

namespace PatternRule

variable {P : Type*} [Fintype P] {M : Mask P P}

/-- Relabeling positions by `π` relabels the pattern. -/
def PermEquivariant (ρ : PatternRule P P M) (π : Equiv.Perm P) : Prop :=
  ∀ s i j, (ρ.toPattern fun i j => s (π i) (π j)).A i j = (ρ.toPattern s).A (π i) (π j)

end PatternRule

end MechInterp

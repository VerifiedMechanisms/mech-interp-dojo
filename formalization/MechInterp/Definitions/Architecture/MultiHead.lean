import MechInterp.Definitions.Architecture.Attention
import MechInterp.Definitions.Algebra.Blocks

set_option linter.style.header false

/-!
# Multi-head attention

A layer has a finite head type with per-head query/key and value widths. All heads read the
same pre-update stream:

`MHA(X)_i = b_O + ∑ h, y^{(h)}_i(X)`.

The concatenated view uses `z^cat_i = concat (z^{(h)}_i)` and
`W_O^cat = ∑ h, W_O^{(h)} ∘ proj_h`. `evalOver` evaluates with optional pattern overrides
and optional edits of head outputs; it is the semantics behind frozen patterns, head
ablations, and head patching.
-/

noncomputable section

namespace MechInterp

/-- Multi-head attention with heterogeneous head widths. -/
structure MultiHead (Pdst Psrc V : Type*) [Fintype Psrc] [AddCommGroup V] [Module ℝ V] where
  Head : Type
  [fin : Fintype Head]
  [deq : DecidableEq Head]
  dK : Head → ℕ
  dV : Head → ℕ
  heads : (h : Head) → AttentionHead V (Vec (dK h)) (Vec (dV h))
  score : (h : Head) → ScoreRule Pdst Psrc (Vec (dK h))
  mask : Mask Pdst Psrc
  rule : PatternRule Pdst Psrc mask
  bO : V

attribute [instance] MultiHead.fin MultiHead.deq

namespace MultiHead

variable {Pdst Psrc V : Type*} [Fintype Psrc] [AddCommGroup V] [Module ℝ V]

/-- The pattern of head `h`. -/
def pattern (M : MultiHead Pdst Psrc V) (h : M.Head) (X : Stream Pdst V) (Y : Stream Psrc V) :
    AttnPattern Pdst Psrc :=
  (M.heads h).pattern (M.score h) M.rule X Y

/-- The mixed values of head `h`. -/
def z (M : MultiHead Pdst Psrc V) (h : M.Head) (X : Stream Pdst V) (Y : Stream Psrc V) :
    Stream Pdst (Vec (M.dV h)) :=
  (M.heads h).z (M.score h) M.rule X Y

/-- The output of head `h`. -/
def headResult (M : MultiHead Pdst Psrc V) (h : M.Head) (X : Stream Pdst V)
    (Y : Stream Psrc V) : Stream Pdst V :=
  (M.heads h).result (M.score h) M.rule X Y

/-- Multi-head attention `b_O + ∑ h, y^{(h)}`. -/
def eval (M : MultiHead Pdst Psrc V) (X : Stream Pdst V) (Y : Stream Psrc V) : Stream Pdst V :=
  fun i => M.bO + ∑ h, M.headResult h X Y i

/-- Self-attention. -/
def evalSelf {P : Type*} [Fintype P] (M : MultiHead P P V) (X : Stream P V) : Stream P V :=
  M.eval X X

/-- Multi-head attention with optional pattern overrides and optional head-output edits. -/
def evalOver (M : MultiHead Pdst Psrc V) (pat : (h : M.Head) → Option (AttnPattern Pdst Psrc))
    (edit : (h : M.Head) → Option (Stream Pdst V → Stream Pdst V)) (X : Stream Pdst V)
    (Y : Stream Psrc V) : Stream Pdst V :=
  fun i => M.bO + ∑ h, ((edit h).getD id)
    ((M.heads h).resultWith ((pat h).getD (M.pattern h X Y)).A Y) i

/-- Concatenated mixed values. -/
def zCat (M : MultiHead Pdst Psrc V) (X : Stream Pdst V) (Y : Stream Psrc V) (i : Pdst) :
    RVec (Σ h : M.Head, Fin (M.dV h)) :=
  Block.concat fun h => M.z h X Y i

/-- The concatenated output projection `W_O^cat = ∑ h, W_O^{(h)} ∘ proj_h`. -/
def WOcat (M : MultiHead Pdst Psrc V) : RVec (Σ h : M.Head, Fin (M.dV h)) →ₗ[ℝ] V :=
  ∑ h, (M.heads h).WO ∘ₗ Block.proj h

/-- A multi-head layer with uniform head widths. -/
def uniform (H : Type) [Fintype H] [DecidableEq H] (dK dV : ℕ)
    (heads : H → AttentionHead V (Vec dK) (Vec dV)) (score : H → ScoreRule Pdst Psrc (Vec dK))
    (mask : Mask Pdst Psrc) (rule : PatternRule Pdst Psrc mask) (bO : V) :
    MultiHead Pdst Psrc V :=
  ⟨H, fun _ => dK, fun _ => dV, heads, score, mask, rule, bO⟩

end MultiHead

end MechInterp

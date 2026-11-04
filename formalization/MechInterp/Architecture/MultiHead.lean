/-
Copyright (c) 2026 Malhar A. Patel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Malhar A. Patel
-/
import MechInterp.Algebra.Blocks
import MechInterp.Architecture.Attention

/-!
# Multi-head attention

A multi-head attention layer runs several attention heads in parallel on the same input and adds
their outputs to an output bias:

  `MHA(X, Y)_i = b_O + ∑ h, y^{(h)}_i(X, Y)`.

Heads are indexed by an arbitrary finite type, and each head `h` has its own query/key width
`dK h` and value width `dV h`. Each head has its own score rule; the mask, the pattern rule, and
the output bias are shared.

## Main definitions

* `MultiHead Pdst Psrc V`: the layer.
* `MultiHead.pattern`, `MultiHead.z`, `MultiHead.headResult`: the per-head views.
* `MultiHead.eval` (and `evalSelf` for self-attention): the layer output. All heads read the same
  pre-update stream.
* `MultiHead.evalOver pat edit`: evaluation in which head `h` may use a supplied pattern
  (`pat h = some A`) instead of its live one, and may have its output passed through an edit
  (`edit h = some g`). This is the semantics behind frozen attention patterns, head ablation, and
  head patching.
* `MultiHead.zCat`, `MultiHead.WOcat`: the concatenated view of the standard presentation. The
  mixed values of all heads are concatenated into `z^cat_i ∈ ℝ^{Σ h, Fin (dV h)}`, and
  `W_O^cat = ∑ h, W_O^{(h)} ∘ proj_h`.
* `MultiHead.uniform`: a layer in which every head has the same widths.
-/

noncomputable section

namespace MechInterp

/-- A multi-head attention layer, with possibly different widths for different heads. -/
structure MultiHead (Pdst Psrc V : Type*) [Fintype Psrc] [AddCommGroup V] [Module ℝ V] where
  /-- The type indexing the heads. -/
  Head : Type
  /-- There are finitely many heads. -/
  [fin : Fintype Head]
  /-- Heads can be compared, so per-head edits can be stated. -/
  [deq : DecidableEq Head]
  /-- The query/key width of each head. -/
  dK : Head → ℕ
  /-- The value width of each head. -/
  dV : Head → ℕ
  /-- The parameters of each head. -/
  heads : (h : Head) → AttentionHead V (Vec (dK h)) (Vec (dV h))
  /-- The score rule of each head. -/
  score : (h : Head) → ScoreRule Pdst Psrc (Vec (dK h))
  /-- The mask shared by all heads. -/
  mask : Mask Pdst Psrc
  /-- The pattern rule shared by all heads. -/
  rule : PatternRule Pdst Psrc mask
  /-- The output bias `b_O`. -/
  bO : V

attribute [instance] MultiHead.fin MultiHead.deq

namespace MultiHead

variable {Pdst Psrc V : Type*} [Fintype Psrc] [AddCommGroup V] [Module ℝ V]

/-! ### Per-head views -/

/-- The attention pattern of head `h`. -/
def pattern (M : MultiHead Pdst Psrc V) (h : M.Head) (X : Stream Pdst V) (Y : Stream Psrc V) :
    AttnPattern Pdst Psrc :=
  (M.heads h).pattern (M.score h) M.rule X Y

/-- The mixed values `z^{(h)}` of head `h`. -/
def z (M : MultiHead Pdst Psrc V) (h : M.Head) (X : Stream Pdst V) (Y : Stream Psrc V) :
    Stream Pdst (Vec (M.dV h)) :=
  (M.heads h).z (M.score h) M.rule X Y

/-- The output `y^{(h)}` of head `h`. -/
def headResult (M : MultiHead Pdst Psrc V) (h : M.Head) (X : Stream Pdst V)
    (Y : Stream Psrc V) : Stream Pdst V :=
  (M.heads h).result (M.score h) M.rule X Y

/-! ### Evaluation -/

/-- The layer output `MHA(X, Y)_i = b_O + ∑ h, y^{(h)}_i`. -/
def eval (M : MultiHead Pdst Psrc V) (X : Stream Pdst V) (Y : Stream Psrc V) : Stream Pdst V :=
  fun i => M.bO + ∑ h, M.headResult h X Y i

/-- Self-attention: destination and source streams coincide. -/
def evalSelf {P : Type*} [Fintype P] (M : MultiHead P P V) (X : Stream P V) : Stream P V :=
  M.eval X X

/-- The layer output with interventions. Head `h` uses the supplied pattern when
`pat h = some A` and its live pattern otherwise, and its output is passed through `g` when
`edit h = some g`. With `pat = fun _ => none` and `edit = fun _ => none` this is `eval`. -/
def evalOver (M : MultiHead Pdst Psrc V) (pat : (h : M.Head) → Option (AttnPattern Pdst Psrc))
    (edit : (h : M.Head) → Option (Stream Pdst V → Stream Pdst V)) (X : Stream Pdst V)
    (Y : Stream Psrc V) : Stream Pdst V :=
  fun i => M.bO + ∑ h, ((edit h).getD id)
    ((M.heads h).resultWith ((pat h).getD (M.pattern h X Y)).A Y) i

/-! ### The concatenated view -/

/-- The mixed values of all heads at position `i`, concatenated into one vector. -/
def zCat (M : MultiHead Pdst Psrc V) (X : Stream Pdst V) (Y : Stream Psrc V) (i : Pdst) :
    RVec (Σ h : M.Head, Fin (M.dV h)) :=
  Block.concat fun h => M.z h X Y i

/-- The concatenated output projection `W_O^cat = ∑ h, W_O^{(h)} ∘ proj_h`, which reads each
head's block of `zCat` with that head's `W_O`. -/
def WOcat (M : MultiHead Pdst Psrc V) : RVec (Σ h : M.Head, Fin (M.dV h)) →ₗ[ℝ] V :=
  ∑ h, (M.heads h).WO ∘ₗ Block.proj h

/-! ### Uniform widths -/

/-- A multi-head layer with head type `H` in which every head has query/key width `dK` and value
width `dV`. -/
def uniform (H : Type) [Fintype H] [DecidableEq H] (dK dV : ℕ)
    (heads : H → AttentionHead V (Vec dK) (Vec dV)) (score : H → ScoreRule Pdst Psrc (Vec dK))
    (mask : Mask Pdst Psrc) (rule : PatternRule Pdst Psrc mask) (bO : V) :
    MultiHead Pdst Psrc V :=
  ⟨H, fun _ => dK, fun _ => dV, heads, score, mask, rule, bO⟩

end MultiHead

end MechInterp

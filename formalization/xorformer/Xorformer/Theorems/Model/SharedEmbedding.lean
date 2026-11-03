import Xorformer.Definitions.Model.SharedEmbedding
import Xorformer.Theorems.Model.Head

set_option linter.style.header false

/-!
# Shared-embedding and head-local attention models

The definitions used here are in `Xorformer.Definitions.Model.SharedEmbedding`.

`HeadFamily` permits each head to carry its own token and positional embeddings.
The prose model instead uses one token embedding and one positional embedding,
followed by head-specific attention maps. `SharedHeadFamily` encodes that model
literally.

This file proves that the two parameterizations have the same head-count
expressivity when width is unrestricted. A head-local family of width `d` is
sent to a shared-embedding family of width `H * d`. The shared embedding is the
concatenation of the `H` local embedding blocks. Head `h` projects to block `h`,
applies its original maps, and writes its result back into block `h`.
-/

namespace Xorformer

open MechInterp
open scoped BigOperators InnerProductSpace

/-! ## Block-coordinate maps -/

@[simp] private theorem finProdFinEquiv_divNat {H d : ℕ} (h : Fin H) (j : Fin d) :
    (finProdFinEquiv (h, j)).divNat = h := by
  exact congrArg Prod.fst
    ((finProdFinEquiv (m := H) (n := d)).symm_apply_apply (h, j))

@[simp] private theorem finProdFinEquiv_modNat {H d : ℕ} (h : Fin H) (j : Fin d) :
    (finProdFinEquiv (h, j)).modNat = j := by
  exact congrArg Prod.snd
    ((finProdFinEquiv (m := H) (n := d)).symm_apply_apply (h, j))

@[simp] theorem headBlockProject_inject {H d : ℕ} (h : Fin H) (v : Vec d) :
    headBlockProject h (headBlockInject h v) = v := by
  ext j
  simp [headBlockProject, headBlockInject]

/-- A block injection preserves the real inner product. -/
theorem headBlockInject_inner {H d : ℕ} (h : Fin H) (x y : Vec d) :
    ⟪headBlockInject h x, headBlockInject h y⟫_ℝ = ⟪x, y⟫_ℝ := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  change (∑ k : Fin (H * d), _) = ∑ j : Fin d, _
  rw [← (finProdFinEquiv (m := H) (n := d)).sum_comp]
  simp only [headBlockInject, LinearMap.coe_mk, AddHom.coe_mk, WithLp.ofLp_toLp,
    finProdFinEquiv_symm_apply]
  rw [Fintype.sum_prod_type]
  simp

@[simp] theorem headBlockProject_concat {H d : ℕ} (h : Fin H)
    (v : Fin H → Vec d) : headBlockProject h (headBlockConcat v) = v h := by
  ext j
  simp [headBlockProject, headBlockConcat]

/-- Reading an injected block against a concatenated vector reads only that block. -/
theorem headBlockConcat_inner_inject {H d : ℕ} (v : Fin H → Vec d)
    (h : Fin H) (x : Vec d) :
    ⟪headBlockConcat v, headBlockInject h x⟫_ℝ = ⟪v h, x⟫_ℝ := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  change (∑ k : Fin (H * d), _) = ∑ j : Fin d, _
  rw [← (finProdFinEquiv (m := H) (n := d)).sum_comp]
  simp only [headBlockConcat, headBlockInject, WithLp.ofLp_toLp, LinearMap.coe_mk,
    AddHom.coe_mk, finProdFinEquiv_symm_apply]
  rw [Fintype.sum_prod_type]
  simp

/-! ## The literal shared-embedding model -/

namespace SharedHeadFamily

end SharedHeadFamily

/-! ## Concatenating a head-local family -/

@[simp] theorem shareHeadEmbeddings_x_project {n d H : ℕ} (Hs : HeadFamily n d H)
    (h : Fin H) (bits : Fin n → Bool) (p : SeqPos n) :
    headBlockProject h ((shareHeadEmbeddings Hs).head h |>.x bits p) =
      (Hs h).x bits p := by
  simp [Head.x, SharedHeadFamily.head, shareHeadEmbeddings]

@[simp] theorem shareHeadEmbeddings_WQ {n d H : ℕ} (Hs : HeadFamily n d H)
    (h : Fin H) (bits : Fin n → Bool) (p : SeqPos n) :
    ((shareHeadEmbeddings Hs).head h).WQ
        (((shareHeadEmbeddings Hs).head h).x bits p) =
      headBlockInject h ((Hs h).WQ ((Hs h).x bits p)) := by
  change headBlockLift h (Hs h).WQ (((shareHeadEmbeddings Hs).head h).x bits p) = _
  simp only [headBlockLift, LinearMap.comp_apply]
  rw [shareHeadEmbeddings_x_project]

@[simp] theorem shareHeadEmbeddings_WK {n d H : ℕ} (Hs : HeadFamily n d H)
    (h : Fin H) (bits : Fin n → Bool) (p : SeqPos n) :
    ((shareHeadEmbeddings Hs).head h).WK
        (((shareHeadEmbeddings Hs).head h).x bits p) =
      headBlockInject h ((Hs h).WK ((Hs h).x bits p)) := by
  change headBlockLift h (Hs h).WK (((shareHeadEmbeddings Hs).head h).x bits p) = _
  simp only [headBlockLift, LinearMap.comp_apply]
  rw [shareHeadEmbeddings_x_project]

@[simp] theorem shareHeadEmbeddings_WV {n d H : ℕ} (Hs : HeadFamily n d H)
    (h : Fin H) (bits : Fin n → Bool) (p : SeqPos n) :
    ((shareHeadEmbeddings Hs).head h).WV
        (((shareHeadEmbeddings Hs).head h).x bits p) =
      headBlockInject h ((Hs h).WV ((Hs h).x bits p)) := by
  change headBlockLift h (Hs h).WV (((shareHeadEmbeddings Hs).head h).x bits p) = _
  simp only [headBlockLift, LinearMap.comp_apply]
  rw [shareHeadEmbeddings_x_project]

@[simp] theorem shareHeadEmbeddings_sigma {n d H : ℕ} (Hs : HeadFamily n d H)
    (h : Fin H) (bits : Fin n → Bool) (p : SeqPos n) :
    ((shareHeadEmbeddings Hs).head h).sigma bits p = (Hs h).sigma bits p := by
  simp [Head.sigma, headBlockInject_inner]

@[simp] theorem shareHeadEmbeddings_value {n d H : ℕ} (Hs : HeadFamily n d H)
    (h : Fin H) (bits : Fin n → Bool) (p : SeqPos n) :
    ((shareHeadEmbeddings Hs).head h).value bits p =
      headBlockInject h ((Hs h).value bits p) := by
  simp [Head.value]

@[simp] theorem shareHeadEmbeddings_denominator {n d H : ℕ} (Hs : HeadFamily n d H)
    (h : Fin H) (bits : Fin n → Bool) :
    ((shareHeadEmbeddings Hs).head h).denominator bits =
      (Hs h).denominator bits := by
  simp [Head.denominator]

@[simp] theorem shareHeadEmbeddings_numerator {n d H : ℕ} (Hs : HeadFamily n d H)
    (h : Fin H) (bits : Fin n → Bool) :
    ((shareHeadEmbeddings Hs).head h).numerator bits =
      headBlockInject h ((Hs h).numerator bits) := by
  simp [Head.numerator]

@[simp] theorem shareHeadEmbeddings_attnUpdate {n d H : ℕ} (Hs : HeadFamily n d H)
    (h : Fin H) (bits : Fin n → Bool) :
    ((shareHeadEmbeddings Hs).head h).attnUpdate bits =
      headBlockInject h ((Hs h).attnUpdate bits) := by
  simp [Head.attnUpdate]

/-- The widened shared model has exactly the same scalar readout as the original
head-local model. The old readout vector is repeated in every output block. -/
theorem shareHeadEmbeddings_readout {n d H : ℕ} (Hs : HeadFamily n d H) (w : Vec d)
    (bits : Fin n → Bool) :
    ⟪headBlockConcat (fun _ : Fin H => w), (shareHeadEmbeddings Hs).attnUpdate bits⟫_ℝ =
      ⟪w, headFamilyAttnUpdate Hs bits⟫_ℝ := by
  rw [show (shareHeadEmbeddings Hs).attnUpdate bits =
      ∑ h, ((shareHeadEmbeddings Hs).head h).attnUpdate bits from rfl]
  rw [show headFamilyAttnUpdate Hs bits = ∑ h, (Hs h).attnUpdate bits from rfl]
  rw [inner_sum, inner_sum]
  exact Finset.sum_congr rfl (fun h _ => by
    rw [shareHeadEmbeddings_attnUpdate, headBlockConcat_inner_inject])

/-! ## Head-count expressivity equivalence -/

/-- Every head-local model becomes a shared-embedding model after widening from
`d` to `H * d`, without changing its head count or Boolean predicate. -/
theorem computableWithSharedHeadsN_of_reducedComputableWithHeads
    {n H : ℕ} {f : (Fin n → Bool) → Bool}
    (hf : reducedComputableWithHeads n H f) : computableWithSharedHeadsN n H f := by
  obtain ⟨d, Hs, w, τ, hsep⟩ := hf
  refine ⟨H * d, shareHeadEmbeddings Hs, headBlockConcat (fun _ : Fin H => w), τ, ?_⟩
  intro bits
  rw [shareHeadEmbeddings_readout]
  exact hsep bits

/-- A shared-embedding family is, after forgetting the sharing invariant, an
ordinary head family of the same width and head count. -/
theorem reducedComputableWithHeads_of_computableWithSharedHeadsN
    {n H : ℕ} {f : (Fin n → Bool) → Bool}
    (hf : computableWithSharedHeadsN n H f) : reducedComputableWithHeads n H f := by
  obtain ⟨d, M, hM⟩ := hf
  exact ⟨d, M.toHeadFamily, hM⟩

/-- Head-local embeddings and a literal shared embedding have identical
head-count expressivity when model width is unrestricted. -/
theorem reducedComputableWithHeads_iff_computableWithSharedHeadsN
    (n H : ℕ) (f : (Fin n → Bool) → Bool) :
    reducedComputableWithHeads n H f ↔ computableWithSharedHeadsN n H f :=
  ⟨computableWithSharedHeadsN_of_reducedComputableWithHeads,
    reducedComputableWithHeads_of_computableWithSharedHeadsN⟩

/-- The least head count is identical in the head-local and literal
shared-embedding models. -/
theorem SharedHStar_eq_ReducedHStar (n : ℕ) (f : (Fin n → Bool) → Bool) :
    SharedHStar n f = ReducedHStar n f := by
  classical
  unfold SharedHStar ReducedHStar
  by_cases hLocal : ∃ k, reducedComputableWithHeads n k f
  · have hShared : ∃ k, computableWithSharedHeadsN n k f :=
      hLocal.imp fun k => computableWithSharedHeadsN_of_reducedComputableWithHeads
    rw [dif_pos hShared, dif_pos hLocal]
    refine le_antisymm ?_ ?_
    · exact Nat.find_min' hShared
        (computableWithSharedHeadsN_of_reducedComputableWithHeads (Nat.find_spec hLocal))
    · exact Nat.find_min' hLocal
        (reducedComputableWithHeads_of_computableWithSharedHeadsN (Nat.find_spec hShared))
  · have hShared : ¬ ∃ k, computableWithSharedHeadsN n k f := by
      rintro ⟨k, hk⟩
      exact hLocal ⟨k, reducedComputableWithHeads_of_computableWithSharedHeadsN hk⟩
    rw [dif_neg hShared, dif_neg hLocal]

end Xorformer

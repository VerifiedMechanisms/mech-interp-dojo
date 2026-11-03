import Xorformer.Definitions.Prelude
import Xorformer.Definitions.Model.Input
import MechInterp.Definitions.Architecture.Softmax

set_option linter.style.header false

/-!
# Generalized `n`-bit one-layer attention model.

This module holds the definitions of this part of the development. Their proofs are in
`Xorformer.Theorems.Model.Head`.

This file lifts the 2-bit XOR setup to inputs `Fin n → Bool` with a
dedicated query token. It also proves a reusable checkerboard
restriction theorem: if, after fixing all but two coordinates, a target
function exhibits the 2-bit checkerboard pattern, then one head cannot
compute it. As a first application, `n`-bit parity requires at least two
heads whenever `n ≥ 2`.
-/

namespace Xorformer

open MechInterp
open scoped InnerProductSpace

/-- Generic linear-readout computability over an arbitrary finite input
    domain. -/
def computesPred {α : Type*} (f : α → Bool) (g : α → Vec d) : Prop :=
  ∃ (w : Vec d) (τ : ℝ), ∀ a : α, ⟪w, g a⟫_ℝ > τ ↔ f a = true

/-- The real-inner-product map `inner w : Vec d → ℝ` packaged as a
linear functional so it can be passed to segment-separation theorems. -/
noncomputable def innerLeftLin {d : ℕ} (w : Vec d) : Vec d →ₗ[ℝ] ℝ where
  toFun v := ⟪w, v⟫_ℝ
  map_add' x y := inner_add_right w x y
  map_smul' c x := by
    simp [inner_smul_right, smul_eq_mul]

/-- Parameters of a single attention head over `n` input bits plus a
    query token. -/
structure Head (n d : ℕ) where
  tokenEmbed : Fin 3 → Vec d
  posEmbed   : SeqPos n → Vec d
  WQ : Vec d →ₗ[ℝ] Vec d
  WK : Vec d →ₗ[ℝ] Vec d
  WV : Vec d →ₗ[ℝ] Vec d

namespace Head

variable {n d : ℕ}

/-- Embedded vector at a sequence position. -/
noncomputable def x (H : Head n d) (bits : Fin n → Bool) (p : SeqPos n) : Vec d :=
  H.tokenEmbed (seqTok bits p) + H.posEmbed p

/-- Unnormalized attention weights to the query token. -/
noncomputable def sigma (H : Head n d) (bits : Fin n → Bool) (p : SeqPos n) : ℝ :=
  Real.exp ⟪H.WK (H.x bits p), H.WQ (H.x bits none)⟫_ℝ

/-- Value vector at position `p`. -/
noncomputable def value (H : Head n d) (bits : Fin n → Bool) (p : SeqPos n) : Vec d :=
  H.WV (H.x bits p)

/-- Attention numerator at the query token. -/
noncomputable def numerator (H : Head n d) (bits : Fin n → Bool) : Vec d :=
  ∑ p, H.sigma bits p • H.value bits p

/-- Attention denominator at the query token. -/
noncomputable def denominator (H : Head n d) (bits : Fin n → Bool) : ℝ :=
  ∑ p, H.sigma bits p

/-- One-head attention update at the query token. -/
noncomputable def attnUpdate (H : Head n d) (bits : Fin n → Bool) : Vec d :=
  (H.denominator bits)⁻¹ • H.numerator bits

/-- Full residual stream at the query token. -/
noncomputable def residual (H : Head n d) (bits : Fin n → Bool) : Vec d :=
  H.x bits none + H.attnUpdate bits

/-- Restrict an `n`-bit input to a 2-dimensional affine subcube by
    varying coordinates `i` and `j` and keeping the remaining bits fixed
    by `base`. -/
def restrictBits (base : Fin n → Bool) (i j : Fin n) (ab : Bool × Bool) :
    Fin n → Bool :=
  fun k => if k = i then ab.1 else if k = j then ab.2 else base k

/-- The restricted attention-update map on the chosen 2-bit subcube. -/
noncomputable def restrictedUpdate
    (H : Head n d) (base : Fin n → Bool) (i j : Fin n) :
    Bool × Bool → Vec d :=
  fun ab => H.attnUpdate (restrictBits base i j ab)

/-- The intersection point of the diagonal and off-diagonal segments on
    a 2-bit restriction. -/
noncomputable def restrictedMidpoint
    (H : Head n d) (base : Fin n → Bool) (i j : Fin n) : Vec d :=
  (H.denominator (restrictBits base i j (false, false))
      + H.denominator (restrictBits base i j (true, true)))⁻¹ •
    (H.numerator (restrictBits base i j (false, false))
      + H.numerator (restrictBits base i j (true, true)))

end Head

/-- A family of `H` heads over `n` input bits. -/
abbrev HeadFamily (n d H : ℕ) : Type := Fin H → Head n d

/-- Summed multi-head attention update for the generalized model. -/
noncomputable def headFamilyAttnUpdate {n d H : ℕ} (Hs : HeadFamily n d H) :
    (Fin n → Bool) → Vec d :=
  fun bits => ∑ h, (Hs h).attnUpdate bits

/-- `n`-bit head computability with `H` heads. -/
def reducedComputableWithHeads (n H : ℕ) (f : (Fin n → Bool) → Bool) : Prop :=
  ∃ d, ∃ Hs : HeadFamily n d H, computesPred f (headFamilyAttnUpdate Hs)

/-- Exact head complexity in the generalized `n`-bit model. -/
def reducedExactHeadComplexity (n : ℕ) (f : (Fin n → Bool) → Bool) (k : ℕ) : Prop :=
  reducedComputableWithHeads n k f ∧ ∀ h < k, ¬ reducedComputableWithHeads n h f

/-- Head complexity on `n`-bit Boolean functions. -/
noncomputable def ReducedHStar (n : ℕ) (f : (Fin n → Bool) → Bool) : ℕ :=
  by
    classical
    exact if h : ∃ k, reducedComputableWithHeads n k f then Nat.find h else 0

def firstIndex {n : ℕ} (hn : 2 ≤ n) : Fin n :=
  ⟨0, Nat.lt_of_lt_of_le (by decide : 0 < 2) hn⟩

def secondIndex {n : ℕ} (hn : 2 ≤ n) : Fin n :=
  ⟨1, by omega⟩

end Xorformer

import Xorformer.Definitions.Prelude
import Mathlib.Data.Fintype.Option
import Xorformer.Definitions.Examples.OneHead

set_option linter.style.header false

/-!
# Theorem 2: two attention heads suffice to compute XOR.

This module holds the definitions of this part of the development. Their proofs are in
`Xorformer.Theorems.Examples.TwoHeads`.

We give construct two `Head 2 3` terms. Both heads use the standard token
embeddings `e_0`, `e_1`, `e_=` and no positional embeddings. The first head
attends to token `0` and writes in the `e_0` direction; the second attends to
token `1` and writes in the `e_1` direction. Their sum places the four
attention outputs into a configuration where the linear probe `e_0 + e_1`
separates the XOR-positive inputs from the XOR-negative inputs.
-/

namespace Xorformer

open MechInterp
open scoped InnerProductSpace

/-- Outer product of two vectors as a linear map: `(u v^T)(w) = ⟪v, w⟫ u`. -/
noncomputable def outerProduct {n : ℕ} (u v : Vec n) : Vec n →ₗ[ℝ] Vec n where
  toFun w := ⟪v, w⟫_ℝ • u
  map_add' x y := by
    simp only [inner_add_right, add_smul]
  map_smul' c x := by
    simp only [inner_smul_right, RingHom.id_apply, smul_smul]

/-- The standard token embedding for the construction:
    `e_0 = (1,0,0)`, `e_1 = (0,1,0)`, `e_= = (0,0,1)`. -/
noncomputable def stdTokenEmbed : Fin 3 → Vec 3 := fun i => EuclideanSpace.single i 1

/-- **Head 0**: attends to token `0`, writes in the `e_0` direction. -/
noncomputable def head0 : Head 2 3 where
  tokenEmbed := stdTokenEmbed
  posEmbed := fun _ => 0
  WQ := LinearMap.id
  WK := outerProduct (EuclideanSpace.single 2 1) (EuclideanSpace.single 0 1)
  WV := outerProduct (EuclideanSpace.single 0 1) (EuclideanSpace.single 0 1)

/-- **Head 1**: attends to token `1`, writes in the `e_1` direction. -/
noncomputable def head1 : Head 2 3 where
  tokenEmbed := stdTokenEmbed
  posEmbed := fun _ => 0
  WQ := LinearMap.id
  WK := outerProduct (EuclideanSpace.single 2 1) (EuclideanSpace.single 1 1)
  WV := outerProduct (EuclideanSpace.single 1 1) (EuclideanSpace.single 1 1)

/-- The combined two-head attention update used in the `computesXor` target. -/
noncomputable def twoHeadUpdate (bits : Fin 2 → Bool) : Vec 3 :=
  head0.attnUpdate bits + head1.attnUpdate bits

/-- The scalar read from `head1` on mixed inputs. -/
noncomputable def head1LowScore : ℝ :=
  Real.exp 1 / (Real.exp 1 + 2)

/-- The scalar read from `head1` on the `(true, true)` input. -/
noncomputable def head1HighScore : ℝ :=
  2 * Real.exp 1 / (2 * Real.exp 1 + 1)

/-- The probe reading the value channel written by `head1`. -/
noncomputable def head1Probe : Vec 3 :=
  EuclideanSpace.single (1 : Fin 3) 1

/-- The probe score on XOR-negative inputs in the two-head construction. -/
noncomputable def twoHeadLowScore : ℝ :=
  2 * Real.exp 1 / (2 * Real.exp 1 + 1)

/-- The probe score on XOR-positive inputs in the two-head construction. -/
noncomputable def twoHeadHighScore : ℝ :=
  2 * Real.exp 1 / (Real.exp 1 + 2)

/-- The probe used by both the XOR and XNOR endpoint examples. -/
noncomputable def twoProbe : Vec 3 :=
  EuclideanSpace.single (0 : Fin 3) 1 + EuclideanSpace.single (1 : Fin 3) 1

end Xorformer

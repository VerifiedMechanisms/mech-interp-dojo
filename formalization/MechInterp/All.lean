import MechInterp.Definitions.Algebra.Affine
import MechInterp.Definitions.Algebra.Blocks
import MechInterp.Definitions.Algebra.Rank
import MechInterp.Definitions.Algebra.Spaces
import MechInterp.Definitions.Architecture.Attention
import MechInterp.Definitions.Architecture.Embedding
import MechInterp.Definitions.Architecture.Mask
import MechInterp.Definitions.Architecture.MultiHead
import MechInterp.Definitions.Architecture.Pattern
import MechInterp.Definitions.Architecture.Score
import MechInterp.Definitions.Architecture.Softmax
import MechInterp.Definitions.Interpretability.Data
import MechInterp.Definitions.Math.ConvexSeparation
import MechInterp.Definitions.Math.Polynomial
import MechInterp.Theorems.Algebra.Affine
import MechInterp.Theorems.Algebra.Blocks
import MechInterp.Theorems.Algebra.Rank
import MechInterp.Theorems.Algebra.Spaces
import MechInterp.Theorems.Architecture.Attention
import MechInterp.Theorems.Architecture.Embedding
import MechInterp.Theorems.Architecture.Mask
import MechInterp.Theorems.Architecture.Pattern
import MechInterp.Theorems.Architecture.Score
import MechInterp.Theorems.Architecture.Softmax
import MechInterp.Theorems.Interpretability.Data
import MechInterp.Theorems.Math.ConvexSeparation
import MechInterp.Theorems.Math.Normalizers
import MechInterp.Theorems.Math.PartialFraction
import MechInterp.Theorems.Math.Square

set_option linter.style.header false

/-!
# MechInterp

Umbrella module: imports every MechInterp module, so `lake build MechInterp` (the library root
named in `lakefile.toml`) builds the whole library. Definitions and theorems are documented in
`MechInterp/README.md`.
-/

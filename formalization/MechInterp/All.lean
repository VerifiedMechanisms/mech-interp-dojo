/-
Copyright (c) 2026 Malhar A. Patel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Malhar A. Patel
-/
-- Supporting mathematics
import MechInterp.Math.BoolSquare
import MechInterp.Math.ConvexSeparation
import MechInterp.Math.Normalizers
import MechInterp.Math.PartialFraction
-- Coordinate spaces and linear algebra
import MechInterp.Algebra.Affine
import MechInterp.Algebra.Blocks
import MechInterp.Algebra.Rank
import MechInterp.Algebra.Spaces
-- Finite probability distributions
import MechInterp.Data.FinDist
-- Transformer architecture
import MechInterp.Architecture.Attention
import MechInterp.Architecture.Embedding
import MechInterp.Architecture.Mask
import MechInterp.Architecture.MultiHead
import MechInterp.Architecture.Pattern
import MechInterp.Architecture.Score
import MechInterp.Architecture.Softmax

/-!
# MechInterp

The umbrella module of the library: `import MechInterp.All` brings in every module. The library
root named in `lakefile.toml` is this module, and `MechInterp/README.md` explains the mathematics
and the Lean declarations in dependency order.

Each topic lives in a single module that holds its definitions together with the theorems about
them:

* `MechInterp.Math`: convex separation, positive normalizers, the Boolean square, and partial
  fractions.
* `MechInterp.Algebra`: coordinate spaces and streams, affine maps, block decompositions, and
  rank.
* `MechInterp.Data`: finite probability distributions over datasets.
* `MechInterp.Architecture`: embeddings, masks, score rules, attention patterns, softmax and
  hardmax, attention heads, and multi-head attention.
-/

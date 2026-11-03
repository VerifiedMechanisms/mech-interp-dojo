import Xorformer.Definitions.Prelude
import Xorformer.Definitions.Polynomial.SymmetricLowerBound
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.EquivFin

set_option linter.style.header false

/-!
# Phase 3b: univariate reduction of a symmetric polynomial on the cube.

This module holds the definitions of this part of the development. Their proofs are in
`Xorformer.Theorems.Polynomial.UnivariateReduction`.

A symmetric polynomial `P : MvPolynomial (Fin n) ℝ` of total degree `≤ H`,
evaluated on the Boolean cube, is a univariate polynomial of degree `≤ H` in the
Hamming weight. Concretely we build `p : ℝ[X]` with `p.natDegree ≤ H` and
`p.eval (hammingWeight x) = eval (cubePoint x) P` for every `x`.

The route (no fundamental theorem of symmetric polynomials needed):
* on the cube each monomial is the indicator that its support lies in the
  ones-set, so `eval (cubePoint x) P = ∑_{d} coeff d · [supp d ⊆ S]` with
  `S` the ones-set (`eval_cube_eq_subset_sum`);
* grouping exponent vectors by their support `A`, the aggregated coefficient
  `supportCoeffSum P A` depends only on `A.card` for symmetric `P`
  (`supportCoeffSum_const`, proved by a coordinate permutation);
* hence `eval = ∑_j β_j · C(|S|, j)` with `β_j` the common value, and
  `C(k, j) = descPochhammer ℝ j / j!` is a degree-`j` polynomial in `k`.

Combined with `signChanges_le_natDegree` (Phase 3c) this yields the L12 lower
bound `signChanges n F ≤ H` whenever `symmetricFn F` is computable with `H`
heads (`signChanges_le_of_reducedComputableWithHeads`).
-/

namespace Xorformer

open MechInterp
open MvPolynomial Finset
open scoped BigOperators

variable {n : ℕ}

/-! ## Evaluation on the Boolean cube as a subset-indicator sum -/

/-- The set of coordinates set to `true`. -/
def onesSet (x : Fin n → Bool) : Finset (Fin n) := univ.filter (fun i => x i = true)

/-! ## A permutation sending one set onto another of the same size -/

/-! ## Aggregated coefficients by support set -/

variable (P : MvPolynomial (Fin n) ℝ)

/-- Sum of coefficients of monomials with a given support set. -/
def supportCoeffSum (A : Finset (Fin n)) : ℝ :=
  ∑ d ∈ P.support.filter (fun d => d.support = A), P.coeff d

/-- The common value of `supportCoeffSum` on all `j`-element sets (junk `0` if none exist). -/
noncomputable def betaCoeff (j : ℕ) : ℝ :=
  if h : ∃ A : Finset (Fin n), A.card = j then supportCoeffSum P h.choose else 0

/-! ## The univariate binomial polynomial `k ↦ C(k, j)` -/

/-- The polynomial whose value at `k` is `C(k, j)`, of degree `j`. -/
noncomputable def binomPoly (j : ℕ) : Polynomial ℝ :=
  ((Nat.factorial j : ℝ)⁻¹) • descPochhammer ℝ j

/-! ## The reduction identity -/

/-! ## L12 lower bound -/

end Xorformer

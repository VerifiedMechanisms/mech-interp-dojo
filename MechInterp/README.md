# MechInterp: a Lean foundation for mechanistic interpretability

`MechInterp` is a Lean 4 / Mathlib library of general definitions and theorems for reasoning about transformer components. It covers vector spaces indexed by finite types, block decompositions, low-rank factorizations, embeddings, attention masks, score rules (including RoPE and ALiBi), attention patterns, softmax and hardmax, attention heads, and multi-head attention. It also includes the mathematical facts these rest on (convex separation, partial fractions) and finite probability distributions for averaging over datasets.

This README explains, in dependency order, **the mathematics that is formalized** and **how each piece is expressed in Lean**. Each section begins with the definitions and ends with the theorems proved about them. The XORFormer head-complexity formalization in [`../xorformer`](../xorformer) is built on this library.

## Contents

1. [Status and how to build](#1-status-and-how-to-build)
2. [Conventions](#2-conventions)
3. [Vector spaces, coordinates, and streams](#3-vector-spaces-coordinates-and-streams)
4. [Affine maps](#4-affine-maps)
5. [Block decompositions](#5-block-decompositions)
6. [Rank, low-rank factorization, and Frobenius norms](#6-rank-low-rank-factorization-and-frobenius-norms)
7. [Supporting mathematics](#7-supporting-mathematics)
8. [Finite probability distributions](#8-finite-probability-distributions)
9. [Token encoders and embeddings](#9-token-encoders-and-embeddings)
10. [Attention masks](#10-attention-masks)
11. [Score rules: dot products, ALiBi, and RoPE](#11-score-rules-dot-products-alibi-and-rope)
12. [Attention patterns and value mixing](#12-attention-patterns-and-value-mixing)
13. [Softmax, hardmax, and raw weight rules](#13-softmax-hardmax-and-raw-weight-rules)
14. [Attention heads](#14-attention-heads)
15. [Multi-head attention](#15-multi-head-attention)
16. [What is not yet formalized](#16-what-is-not-yet-formalized)
17. [Module index](#17-module-index)

---

## 1. Status and how to build

The library has 16 topic modules plus the umbrella module `All.lean` (about 3,000 lines). **All of them build** without errors, warnings, `sorry`, or project axioms. Every theorem described below is machine-checked.

The library root is the umbrella module `MechInterp/All.lean` (`MechInterp.All`), which imports every topic module. Build it from `formalization/`:

```bash
cd formalization
lake build MechInterp    # just this library
lake build               # every library: HeadComplexity, MechInterp, Xorformer
```

The lakefile's `globs = ["MechInterp.+"]` builds every module under `MechInterp/` even if `All.lean` does not import it. When you add a module, also add its import to `MechInterp/All.lean` so that `import MechInterp.All` brings in the whole library.

[§16](#16-what-is-not-yet-formalized) lists what the library does not cover yet.

## 2. Conventions

### 2.1 One module per topic

Each topic is a single module that holds its definitions together with the theorems about them. Within a module, a definition is usually followed directly by its basic lemmas, and the main results come after. The modules are grouped into four directories:

| Directory | Contents |
| --- | --- |
| `Math/` | model-independent mathematics: convex separation, positive normalizers, the Boolean square, partial fractions |
| `Algebra/` | coordinate spaces and streams, affine maps, block decompositions, rank |
| `Data/` | finite probability distributions over datasets |
| `Architecture/` | embeddings, masks, score rules, attention patterns, softmax and hardmax, attention heads, multi-head attention |

Every module starts with a copyright header and a module docstring that lists its main definitions and main results, and every definition, structure field, and theorem has a docstring. Long proofs carry comments that mark their steps.

A structure may carry proof fields that certify it is well formed. For example, an attention pattern carries the proof that its rows sum to one, and the softmax pattern rule uses the theorems of `Math/Normalizers.lean` to prove that its normalizers are positive.

### 2.2 Namespace and notation

Everything lives in the namespace `MechInterp`. The table maps mathematical notation to its Lean counterpart.

| Mathematics | Lean |
| --- | --- |
| $\mathbb{R}^{\iota}$ for a finite type $\iota$ | `RVec ι` |
| $\mathbb{R}^{d}$ | `Vec d` |
| coordinate $x_i$ | `x i` |
| inner product $\langle x, y\rangle$ | `⟪x, y⟫_ℝ` |
| standard basis vector $\delta_i$ | `RVec.oneHot i` |
| a residual stream $X = (X_p)_{p \in P}$, $X_p \in V$ | `X : Stream P V` (a function `P → V`) |
| linear map $V \to W$ | `V →ₗ[ℝ] W` |
| affine map $V \to W$ | `V →ᵃ[ℝ] W` |
| linear isometry $V \to W$ | `V →ₗᵢ[ℝ] W` |
| finite sum $\sum_{i}$ | `∑ i, …` |

Positions, tokens, heads, and coordinates are indexed by arbitrary finite types (`[Fintype ι]`), not only by $\lbrace 0, \dots, d-1\rbrace$. Concatenating blocks therefore never needs index arithmetic.

---

## 3. Vector spaces, coordinates, and streams

**Module:** [`Algebra/Spaces.lean`](Algebra/Spaces.lean)

### 3.1 Definitions

**Euclidean spaces.** For a finite type $\iota$, $\mathbb{R}^{\iota}$ is the space of real vectors with one coordinate per element of $\iota$, carrying the standard inner product

```math
\langle x, y\rangle = \sum_{i\in\iota} x_i\, y_i .
```

```lean
abbrev RVec (ι : Type*) := EuclideanSpace ℝ ι   -- Mathlib's ℓ² space on ι
abbrev Vec (d : ℕ) := RVec (Fin d)              -- the usual ℝᵈ
abbrev Stream (P V : Type*) := P → V            -- one vector per position
```

A **stream** over positions $P$ with values in $V$ is a family $X = (X_p)_{p\in P}$. It models the residual stream of a transformer, with one vector per token position.

**Coordinate constructions** (namespace `RVec`):

| Mathematics | Lean | Meaning |
| --- | --- | --- |
| $x$ with $x_i = f(i)$ | `ofFun f` | vector with prescribed coordinates |
| $\delta_i$, with $(\delta_i)_j = [j = i]$ | `oneHot i` | standard basis (one-hot) vector |
| $\mathbf{1}$ | `ones` | all-ones vector |
| $(x \odot y)_i = x_i y_i$ | `hadamard x y` | coordinatewise product |
| $(\sigma(x))_i = \sigma(x_i)$ | `map σ x` | coordinatewise function |
| $\lVert x\rVert_0 = \lvert\lbrace i : x_i \neq 0\rbrace\rvert$ | `l0 x` | number of nonzero coordinates |
| $x \mapsto \sum_i x_i e_i$ | `linearOfFun e` | the linear map with $\delta_i \mapsto e_i$ |

**Reindexing along a map** $e : \kappa \to \iota$:

```math
(R_e\, w)_k = w_{e(k)} \quad(\texttt{restrictAlong } e : \mathbb{R}^{\iota}\to\mathbb{R}^{\kappa}),
\qquad
E_e\, v = \sum_{k\in\kappa} v_k\, \delta_{e(k)} \quad(\texttt{extendAlong } e : \mathbb{R}^{\kappa}\to\mathbb{R}^{\iota}).
```

When $e$ is injective, $E_e$ is extension by zero: it copies $v_k$ to coordinate $e(k)$ and puts $0$ everywhere else. All the block maps of [§5](#5-block-decompositions) are built from these two maps.

**Stream operations.** `Stream.update X p v` replaces the vector at position $p$, and `Stream.mapPos f X` applies $f$ at every position.

### 3.2 Theorems

| Statement | Lean |
| --- | --- |
| $\langle x, y\rangle = \sum_i x_i y_i$ | `RVec.inner_eq_sum` |
| $\lVert x\rVert^2 = \sum_i x_i^2$ | `RVec.norm_sq_eq_sum` |
| $(\delta_i)_j = [j = i]$ | `RVec.oneHot_apply` |
| $\langle \delta_i, x\rangle = x_i = \langle x, \delta_i\rangle$ | `RVec.inner_oneHot_left`, `RVec.inner_oneHot_right` |
| $\sum_i x_i \delta_i = x$ | `RVec.sum_smul_oneHot` |
| $(\texttt{linearOfFun } e)(\delta_i) = e_i$ | `RVec.linearOfFun_oneHot` |
| every linear $f : \mathbb{R}^{\iota}\to V$ equals `linearOfFun` $(i \mapsto f(\delta_i))$ | `RVec.linearMap_eq_linearOfFun` |
| $f(x) = \sum_i x_i f(\delta_i)$ | `RVec.linearMap_apply_eq_sum` |
| $(E_e v)_i = \sum _{k : e(k) = i} v_k$ | `RVec.extendAlong_apply` |
| for injective $e$: $(E_e v)_{e(k)} = v_k$, and $(E_e v)_i = 0$ off the range | `RVec.extendAlong_apply_self`, `RVec.extendAlong_apply_of_forall_ne` |
| adjointness: $\langle E_e v, w\rangle = \langle v, R_e w\rangle$ | `RVec.inner_extendAlong_left` |
| for injective $e$: $R_e E_e = \mathrm{id}$ | `RVec.restrictAlong_extendAlong` |
| for injective $e$: $\langle E_e v, E_e w\rangle = \langle v, w\rangle$ | `RVec.inner_extendAlong` |

The last theorem follows from the two before it: $\langle E_e v, E_e w\rangle = \langle v, R_e E_e w\rangle = \langle v, w\rangle$.

---

## 4. Affine maps

**Module:** [`Algebra/Affine.lean`](Algebra/Affine.lean)

### 4.1 Definitions

Learned projections in real transformers have biases, so they are **affine** maps $f(x) = Lx + b$. Lean uses Mathlib's `V →ᵃ[ℝ] W`, whose linear part is `f.linear`.

```lean
def affineOf (L : V →ₗ[ℝ] W) (b : W) : V →ᵃ[ℝ] W   -- x ↦ L x + b
def IsBiasFree (f : V →ᵃ[ℝ] W) : Prop := f 0 = 0
def bias (f : V →ᵃ[ℝ] W) : W := f 0
```

### 4.2 Theorems

| Statement | Lean |
| --- | --- |
| $\texttt{affineOf}(L,b)(x) = Lx + b$, with linear part $L$ | `affineOf_apply`, `affineOf_linear` |
| every affine map decomposes as $f(x) = f_{\mathrm{lin}}(x) + f(0)$ | `affine_apply_eq_linear_add_bias` |
| $\texttt{affineOf}(f_{\mathrm{lin}}, f(0)) = f$ | `affineOf_linear_bias` |
| if $f(0) = 0$ then $f = f_{\mathrm{lin}}$ | `IsBiasFree.apply_eq` |
| $\texttt{affineOf}(L, 0)$ and linear maps are bias-free | `isBiasFree_affineOf_zero`, `isBiasFree_toAffineMap` |
| $f(a x + (1-a) y) = a f(x) + (1-a) f(y)$ | `affine_map_combo` |

The decomposition comes from the defining property of an affine map, $f(x + 0) = f_{\mathrm{lin}}(x) + f(0)$.

---

## 5. Block decompositions

**Module:** [`Algebra/Blocks.lean`](Algebra/Blocks.lean)

Concatenated spaces occur everywhere in transformers: multi-head outputs are concatenated, and residual streams are split into subspaces. Here a concatenated space is indexed by a sum, product, or sigma type. A block map is then restriction or extension along the injective index map that picks out the block.

### 5.1 Definitions

For an injective $e : \kappa \to \iota$ (namespace `Block`):

```lean
def restrict (e : κ → ι) : RVec ι →ₗ[ℝ] RVec κ                                  -- R_e
def extend (e : κ → ι) (he : Function.Injective e) : RVec κ →ₗᵢ[ℝ] RVec ι      -- E_e, as an isometry
```

`extend` is packaged as a linear **isometry**. Its certificate is the inner-product identity `RVec.inner_extendAlong` from [§3.2](#32-theorems).

Three families of blocks are built from these two maps:

| Block structure | Index type | Maps | Meaning |
| --- | --- | --- | --- |
| heterogeneous blocks, block $h$ of width $\lvert\iota_h\rvert$ | $\Sigma_h \iota_h$ | `inj h`, `proj h`, `concat v` | $\mathbb{R}^{\Sigma_h \iota_h} = \bigoplus_h \mathbb{R}^{\iota_h}$ |
| uniform blocks of width $\lvert\kappa\rvert$ | $H \times \kappa$ | `injProd h`, `projProd h`, `concatProd v` | $\mathbb{R}^{H\times\kappa} = \bigoplus_{h\in H}\mathbb{R}^{\kappa}$ |
| zero padding | $\iota \oplus \kappa$ | `pad ι κ`, `unpad ι κ` | $\mathbb{R}^{\iota} \hookrightarrow \mathbb{R}^{\iota\oplus\kappa}$ |

Concretely, $\mathrm{inj}_h = E _{\langle h,\cdot\rangle}$ and $\mathrm{proj}_h = R _{\langle h,\cdot\rangle}$. The map $\mathrm{concat}(v)$ has coordinates $\mathrm{concat}(v) _{\langle h, j\rangle} = (v_h)_j$. Similarly $\mathrm{pad} = E _{\mathrm{inl}}$ and $\mathrm{unpad} = R _{\mathrm{inl}}$.

### 5.2 Theorems

General restriction and extension:

| Statement | Lean |
| --- | --- |
| $R_e E_e = \mathrm{id}$ | `Block.restrict_extend` |
| $\langle E_e v, w\rangle = \langle v, R_e w\rangle$ (and the mirror form) | `Block.inner_extend_left`, `Block.inner_extend_right` |
| $\langle E_e v, E_e w\rangle = \langle v, w\rangle$ | `Block.inner_extend` |
| if $e$ and $e'$ have disjoint ranges, then $R_{e'} E_e = 0$ | `Block.restrict_extend_of_disjoint` |

Sigma blocks, for $h' \neq h$:

```math
\mathrm{proj}_h \mathrm{inj}_h = \mathrm{id},\quad
\mathrm{proj}_{h'}\mathrm{inj}_h = 0,\quad
\langle \mathrm{inj}_h v, w\rangle = \langle v, \mathrm{proj}_h w\rangle,\quad
\langle \mathrm{inj}_h v, \mathrm{inj}_h w\rangle = \langle v, w\rangle,
```

```math
\mathrm{proj}_h\mathrm{concat}(v) = v_h,\quad
\langle \mathrm{concat}(v), \mathrm{inj}_h x\rangle = \langle v_h, x\rangle,\quad
\mathrm{concat}(v) = \sum_h \mathrm{inj}_h v_h .
```

These are `proj_inj`, `proj_inj_of_ne`, `inner_inj_left`, `inner_inj`, `proj_concat`, `inner_concat_inj`, and `concat_eq_sum`. The product-block versions carry the same names with the `Prod` suffix (`projProd_injProd`, `projProd_injProd_of_ne`, `inner_injProd_left`, `inner_injProd`, `projProd_concatProd`, `inner_concatProd_injProd`). The padding versions are `unpad_pad`, `inner_pad_left`, `inner_pad`, `pad_apply_inl`, and `pad_apply_inr`.

---

## 6. Rank, low-rank factorization, and Frobenius norms

**Module:** [`Algebra/Rank.lean`](Algebra/Rank.lean)

### 6.1 Motivation

An attention head with query/key width $r$ computes scores through the bilinear form $B(u,v) = \langle W_Q u, W_K v\rangle$, where $W_Q, W_K : V \to \mathbb{R}^r$. Its value path $W_O W_V$ factors through $\mathbb{R}^{r'}$, where $r'$ is the value width. These factorization constraints are what a head's dimensions impose. The theorems below show that they are exactly rank bounds.

### 6.2 Definitions

For real vector spaces $V$ and $W$:

```math
\mathrm{rank}(M) = \dim \mathrm{range}(M)\quad(\texttt{linRank}),\qquad
\mathrm{rank}(B) = \mathrm{rank}\big(u \mapsto B(u,\cdot)\big)\quad(\texttt{bilinRank}).
```

Here a bilinear form is a linear map `V →ₗ[ℝ] W →ₗ[ℝ] ℝ` into functionals on $W$, and its rank is the rank of that map.

```math
\texttt{QKRealizable}(B, r) :\iff \exists\, Q : V \to \mathbb{R}^r,\ K : W \to \mathbb{R}^r \text{ linear},\ \forall u, v,\ B(u, v) = \langle Q u, K v\rangle,
```

```math
\texttt{OVRealizable}(M, r) :\iff \exists\, W_v : V\to\mathbb{R}^r,\ O:\mathbb{R}^r \to W \text{ linear},\ M = O \circ W_v .
```

For linear maps between Euclidean spaces, the Frobenius norm uses the matrix entries $(f\delta_i)_k$, and the **composition score** of Elhage et al. measures how much of $M$'s input space is fed by $N$'s output:

```math
\lVert f\rVert_F^2 = \sum_{i}\sum_{k} \big((f\,\delta_i)_k\big)^2,\qquad
\mathrm{comp}(M, N) = \frac{\lVert M N\rVert_F}{\lVert M\rVert_F\,\lVert N\rVert_F}.
```

In Lean these are `frobeniusNormSq`, `frobeniusNorm`, and `compositionScore`.

### 6.3 Theorems

**OV rank theorem** (`ovRealizable_iff`). If $V$ is finite-dimensional, then

```math
\texttt{OVRealizable}(M, r) \iff \mathrm{rank}(M) \le r .
```

- **Proof of (⇒),** `linRank_le_of_ovRealizable`, which needs no finite-dimensionality. If $M = O W_v$, then $\mathrm{range}(M) = O(\mathrm{range}\ W_v)$, so its dimension is at most $\dim\mathrm{range}\ W_v \le \dim \mathbb{R}^r = r$.
- **Proof of (⇐),** `ovRealizable_of_linRank_le`.
  - Choose a basis $b_1, \dots, b_k$ of $\mathrm{range}(M)$, with $k \le r$, and write $Mv = \sum_{i\le k} c_i(v) b_i$ with linear coordinate functionals $c_i$.
  - Set $W_v(v) = (c_1(v), \dots, c_k(v), 0, \dots, 0) \in \mathbb{R}^r$, and let $O$ send $\delta_j \mapsto b_j$ for $j \le k$ and $\delta_j \mapsto 0$ otherwise.
  - Then $O W_v = M$.

**QK rank theorem** (`qkRealizable_iff`). If $V$ is finite-dimensional, then

```math
\texttt{QKRealizable}(B, r) \iff \mathrm{rank}(B) \le r .
```

*Proof.*

- **(⇒)** $B$ factors as $u \mapsto \langle Qu, K\cdot\rangle$ through $\mathbb{R}^r$, so the OV bound applies.
- **(⇐)** The OV theorem gives $B = O \circ Q$ with $O : \mathbb{R}^r \to W^{\ast}$. Define $K v = \big(O(\delta_j)(v)\big)_{j}$. Then $\langle Qu, Kv\rangle = \sum_j (Qu)_j O(\delta_j)(v) = O(Qu)(v) = B(u, v)$.

**Frobenius norms.** $\lVert f\rVert_F^2 \ge 0$, $\lVert f\rVert_F \ge 0$, $\lVert 0\rVert_F = 0$, and $(\lVert f\rVert_F)^2 = \lVert f\rVert_F^2$. These are `frobeniusNormSq_nonneg`, `frobeniusNorm_nonneg`, `frobeniusNorm_zero`, and `frobeniusNorm_sq`.

---

## 7. Supporting mathematics

These modules hold model-independent facts that the attention theory and the XORFormer results use.

### 7.1 Linear-threshold separability and convex hulls

**Module:** [`Math/ConvexSeparation.lean`](Math/ConvexSeparation.lean)

**Definition.** In a real inner product space $V$, sets $S^{+}$ and $S^{-}$ are **linear-threshold separable** if

```math
\exists\, w \in V,\ \tau\in\mathbb{R}:\qquad \langle w, s\rangle > \tau \ \ (s\in S^{+}),\qquad \langle w, s\rangle \le \tau\ \ (s \in S^{-}).
```

The inequality is strict on the positive side and weak on the negative side, matching the classifier convention "$f(x)$ is true exactly when the score is $\gt 0$": a score of exactly zero counts as false. In Lean this is `LinThresholdSeparable Spos Sneg`.

**Theorems.**

- **Convex combinations** (`convex_combo_le`, `lt_convex_combo`). If $a, b \ge 0$ and $a + b = 1$, then $x, y \le \tau$ implies $a x + b y \le \tau$, and $x, y \gt \tau$ implies $a x + b y \gt \tau$.
- **Segment-crossing obstruction** (`segment_cross_not_separable`). Let $L$ be a linear functional on a real vector space with $L(p), L(q) \le \tau \lt L(r), L(s)$. Then the segments $[p,q]$ and $[r,s]$ cannot share a point. *Proof:* a common point $P$ would satisfy both $L(P) \le \tau$ and $L(P) \gt \tau$, by the two convex-combination facts. This is the geometric core of the classical fact that one head cannot compute XOR.
- **Separation passes to hulls** (`LinThresholdSeparable.hulls`). The half-spaces $\lbrace\langle w,\cdot\rangle \gt \tau\rbrace$ and $\lbrace\langle w,\cdot\rangle \le \tau\rbrace$ are convex, so separating $S^{\pm}$ separates $\mathrm{conv}\ S^{\pm}$. Consequently separable sets have disjoint convex hulls (`LinThresholdSeparable.disjoint_convexHull`).
- **Finite separability theorem** (`linThresholdSeparable_iff_disjoint_convexHull`). In a finite-dimensional real inner product space, finite sets $S^{+}$ and $S^{-}$ are linear-threshold separable if and only if $\mathrm{conv}\ S^{+} \cap \mathrm{conv}\ S^{-} = \varnothing$.
  *Proof of (⇐).*
  - The convex hull of a finite set is compact, hence closed.
  - Mathlib's geometric Hahn–Banach theorem (`geometric_hahn_banach_compact_closed`) gives a continuous functional $\varphi$ and reals $u \lt v$ with $\varphi \lt u$ on $\mathrm{conv}\ S^{-}$ and $\varphi \gt v$ on $\mathrm{conv}\ S^{+}$.
  - By the Riesz representation (`InnerProductSpace.toDual`), $\varphi = \langle w, \cdot\rangle$ for some $w$. Take $\tau = u$.

### 7.2 Positive normalizers

**Module:** [`Math/Normalizers.lean`](Math/Normalizers.lean)

- A finite sum of strictly positive reals over a nonempty index set is strictly positive (`positiveNormalizer_pos`, `positiveNormalizer_pos_of_nonempty`). This certifies that softmax denominators are positive.
- A two-term weighted average can be rewritten as $\frac{a}{a+b}u + \frac{b}{a+b}v = (a+b)^{-1}(a u + b v)$ (`twoTermWeightedAverage_eq_inv_smul_sum`).

### 7.3 Functions on the Boolean square

**Module:** [`Math/BoolSquare.lean`](Math/BoolSquare.lean)

For $f : \lbrace 0,1\rbrace^2 \to A$ with $A$ an abelian group (`boolSquare_antipode_iff_additive_split`):

```math
f(0,0) + f(1,1) = f(0,1) + f(1,0)
\iff
\exists\, \mathrm{row}, \mathrm{col}, c:\ f(a, b) = \mathrm{row}(a) + \mathrm{col}(b) + c .
```

*Proof of (⇒):* take $\mathrm{row}(a) = f(a, 0)$, $\mathrm{col}(b) = f(0, b)$, and $c = -f(0,0)$, then check the four corners. The two directions are also available separately as `boolSquare_additive_split_of_antipode` and `boolSquare_antipode_of_additive_split`. These identities are the "antipode" and "additive decomposition" statements of the XORFormer theorems 1 and 2.

### 7.4 Real partial fractions

**Module:** [`Math/PartialFraction.lean`](Math/PartialFraction.lean)

**Definitions.** For shifts $a_1, \dots, a_K \in \mathbb{R}$:

```math
Q = \prod_{h=1}^{K} (X + a_h)\quad(\texttt{shiftProd}),\qquad
L_h = \prod_{j \ne h} (X + a_j)\quad(\texttt{shiftProdErase}).
```

`eval_shiftProd` and `eval_shiftProdErase` evaluate them pointwise.

**Theorem** (`real_partial_fraction_poly`, with the evaluated form `real_partial_fraction`). If the $a_h$ are distinct and $\deg P \le K$, then there are $A$ and $b_1, \dots, b_K$ with

```math
P = A\, Q + \sum_{h=1}^{K} b_h\, L_h .
```

Dividing by $Q(k) \neq 0$ gives the partial-fraction decomposition $P(k)/Q(k) = A + \sum_h b_h/(k + a_h)$. Each term $b_h/(k + a_h)$ is what a single attention head can realize along a Hamming-weight axis.

*Proof.*

- Choose the coefficients:
  - $A$ is the coefficient of $X^K$ in $P$;
  - $b_h = P(-a_h)\big/\prod_{j\ne h}(a_j - a_h)$, which is well defined because the shifts are distinct.
- The difference $P - (AQ + \sum_h b_h L_h)$ has degree below $K$, since the $X^K$ coefficients cancel.
- It vanishes at the $K$ distinct points $-a_h$, so it is the zero polynomial. When $K = 0$, $P$ is constant and the identity is immediate.

---

## 8. Finite probability distributions

**Module:** [`Data/FinDist.lean`](Data/FinDist.lean)

Interpretability measurements average over prompt datasets. This includes the mean activation used in mean ablation and the average effect of a patch. The library models such data with finitely supported distributions whose weights are real numbers. Mathlib's `PMF` uses extended nonnegative reals instead, which make expectations of vector-valued functions awkward.

### 8.1 Definitions

A **finite distribution** on $\alpha$ is a finitely supported weight function $\mu : \alpha \to \mathbb{R}$ with $\mu(a) \ge 0$ and $\sum_a \mu(a) = 1$:

```lean
structure FinDist (α : Type*) where
  w : α →₀ ℝ                         -- finitely supported weights
  nonneg : ∀ a, 0 ≤ w a
  sum_one : w.sum (fun _ r => r) = 1
```

| Mathematics | Lean |
| --- | --- |
| $\mathbb{E}_{a\sim\mu}[g(a)] = \sum _{a} \mu(a) g(a)$, for $g$ valued in any real vector space | `μ.expect g` |
| $\Pr_{a\sim\mu}[p(a)] = \mathbb{E}_{a\sim\mu}[\mathbf{1} _{p(a)}]$ | `μ.prob p` |
| point mass $\delta_a$ | `FinDist.pure a` |
| pushforward $(f_{\ast}\mu)(b) = \sum_{f(a) = b}\mu(a)$ | `FinDist.map f μ` |
| uniform distribution on a nonempty finite set $s$ (weight $1/\lvert s\rvert$ each) | `FinDist.uniform s hs` |
| conversion to Mathlib's `PMF` | `μ.toPMF` |

Each constructor proves its own nonnegativity and normalization.

### 8.2 Theorems

Linearity, normalization, and monotonicity of expectation:

```math
\mathbb{E}[g + g'] = \mathbb{E}[g] + \mathbb{E}[g'],\quad
\mathbb{E}[c\,g] = c\,\mathbb{E}[g],\quad
\mathbb{E}[-g] = -\mathbb{E}[g],\quad
\mathbb{E}[g - g'] = \mathbb{E}[g] - \mathbb{E}[g'],\quad
\mathbb{E}[c] = c,
```

```math
\mathbb{E}\Big[\sum_{i\in s} g_i\Big] = \sum_{i\in s}\mathbb{E}[g_i],\qquad
\mathbb{E}_{f_{*}\mu}[g] = \mathbb{E}_{\mu}[g\circ f],\qquad
\mathbb{E}_{\delta_a}[g] = g(a),\qquad
\mathbb{E}_{\mathrm{unif}(s)}[g] = \frac{1}{\lvert s\rvert}\sum_{a\in s} g(a).
```

These are `expect_add`, `expect_smul`, `expect_neg`, `expect_sub`, `expect_const`, `expect_finsetSum`, `expect_map`, `expect_pure`, and `expect_uniform`.

For real-valued functions:

- $g \le g'$ pointwise implies $\mathbb{E}[g] \le \mathbb{E}[g']$ (`expect_mono`), and with it `expect_nonneg` and `expect_le_of_le`.
- Probabilities lie in $[0,1]$ (`prob_nonneg`, `prob_le_one`), are monotone in the event (`prob_mono`), and equal one for events that always hold (`prob_of_forall`).
- `toPMF_apply` gives the `PMF` weight of each point.

---

## 9. Token encoders and embeddings

**Module:** [`Architecture/Embedding.lean`](Architecture/Embedding.lean)

### 9.1 Definitions

A **token encoder** maps a task input to a token at each position, $\mathrm{enc} : \mathrm{In} \to (P \to T)$. In Lean, `Encoder In P T := In → P → T`.

The token embedding and the positional embedding are **linear maps out of one-hot spaces**:

```math
W_E : \mathbb{R}^{T} \to V,\qquad W_P : \mathbb{R}^{P} \to V,\qquad e_t = W_E\,\delta_t,\qquad p_i = W_P\,\delta_i .
```

The **additive embedding** of a token sequence $\mathrm{tok} : P \to T$ is the stream

```math
X_i = e_{\mathrm{tok}(i)} + p_i .
```

Treating embeddings as linear maps, rather than as lookup functions $T \to V$, makes "full circuits" such as $W_U W_O W_V W_E$ ordinary compositions of linear maps.

```lean
structure AdditiveEmbedding (T P V : Type*) [AddCommGroup V] [Module ℝ V] where
  WE : RVec T →ₗ[ℝ] V
  WP : RVec P →ₗ[ℝ] V
```

The accessors are `tokenVec` ($e_t$), `posVec` ($p_i$), `embed tok` (the stream $X$), and `embedInput enc x = embed (enc x)`. Two constructors are provided:

- `ofFunctions e p` builds the embedding from lists of vectors, using `linearOfFun`.
- `tokenOnly e` has no positional information ($p_i = 0$).

### 9.2 Theorems

- `embed_apply`: $X_i = e_{\mathrm{tok}(i)} + p_i$.
- `tokenVec_ofFunctions`, `posVec_ofFunctions`: the embedding built from vectors $e$ and $p$ returns exactly those vectors.
- `posVec_tokenOnly`: a token-only embedding has zero positional vectors.
- **Relabeling equivariance** (`embed_tokenOnly_comp`): without positional information, relabeling positions by $\pi$ relabels the stream, $\mathrm{embed}(\mathrm{tok}\circ \pi) = \mathrm{embed}(\mathrm{tok}) \circ \pi$.

---

## 10. Attention masks

**Module:** [`Architecture/Mask.lean`](Architecture/Mask.lean)

### 10.1 Definitions

A **mask** is a decidable relation $M \subseteq P_{\mathrm{dst}} \times P_{\mathrm{src}}$, saying which source positions $j$ a destination position $i$ may attend to:

```lean
structure Mask (Pdst Psrc : Type*) where
  allowed : Pdst → Psrc → Prop
  [dec : ∀ i j, Decidable (allowed i j)]
```

Properties of a mask:

- **Well formed** (`WellFormed`): every row allows something, $\forall i\ \exists j,\ M(i,j)$. This is the condition that makes softmax normalizers positive.
- **Contains the diagonal** (`ContainsDiag`, for $P_{\mathrm{dst}} = P_{\mathrm{src}}$): $\forall i,\ M(i,i)$.
- `allowedSet M i` is the finite set $\lbrace j : M(i, j)\rbrace$.

Standard masks:

| Mask | Rule $M(i,j)$ | Lean |
| --- | --- | --- |
| full | always | `Mask.full` |
| causal | $\mathrm{ord}(j) \le \mathrm{ord}(i)$ | `Mask.causal ord` |
| local window of width $w$ | $\mathrm{ord}(j)\le\mathrm{ord}(i) \lt \mathrm{ord}(j) + w$ | `Mask.window ord w` |
| prefix LM | ($i$ and $j$ both in the prefix) or $\mathrm{ord}(j)\le\mathrm{ord}(i)$ | `Mask.prefixLM ord isPrefix` |
| intersection | $M(i,j) \wedge N(i,j)$ | `M.inter N` |

Causality always refers to an **explicit order** $\mathrm{ord} : P \to \mathbb{N}$, never to an incidental order on the position type.

### 10.2 Theorems

- A mask containing the diagonal is well formed (`wellFormed_of_containsDiag`).
- The following contain the diagonal: full, causal, window with $w \gt 0$, prefix LM, and the intersection of two diagonal-containing masks (`full_containsDiag`, `causal_containsDiag`, `window_containsDiag`, `prefixLM_containsDiag`, `inter_containsDiag`).
- Hence causal masks and positive-width windows are well formed (`causal_wellFormed`, `window_wellFormed`).
- The full mask over a nonempty source type is well formed (`full_wellFormed`).
- `mem_allowedSet` and `causal_allowed` unfold membership.
- `window_le_causal` shows a window mask only allows what the causal mask allows.

---

## 11. Score rules: dot products, ALiBi, and RoPE

**Module:** [`Architecture/Score.lean`](Architecture/Score.lean)

### 11.1 Definitions

Given queries $q_i$ and keys $k_j$ in a query/key space $K$, a **score rule** computes

```math
s_{ij} = c\,\langle R_i\, q_i,\ R'_j\, k_j\rangle + b_{ij}.
```

Here $c$ is a scale, $R_i$ and $R'_j$ are position-dependent linear isometries of $K$, and $b _{ij}$ is a positional score bias.

```lean
structure ScoreRule (Pdst Psrc K : Type*) [NormedAddCommGroup K] [InnerProductSpace ℝ K] where
  scale : ℝ
  qRot : Pdst → K →ₗᵢ[ℝ] K
  kRot : Psrc → K →ₗᵢ[ℝ] K
  bias : Pdst → Psrc → ℝ
-- σ.score i j q k = σ.scale * ⟪σ.qRot i q, σ.kRot j k⟫_ℝ + σ.bias i j
```

| Rule | Parameters | Lean |
| --- | --- | --- |
| dot product | $R = R' = \mathrm{id}$, $b = 0$; for example $c = 1/\sqrt{\dim K}$ | `ScoreRule.standard c` |
| ALiBi | standard scores plus $b_{ij} = -m(\mathrm{ord}(i) - \mathrm{ord}(j))$ | `ScoreRule.alibi ord m c` |
| RoPE | rotations by position-dependent angles (below) | `ScoreRule.rope posQ posK θ c` |

`withBias` replaces the bias of a rule. The predicate `PositionFree` says the rotations and the bias do not depend on position; `KeyRotationFree` says only that the key rotations do not.

**RoPE.** Take $K = \mathbb{R}^{m \times 2}$, which is $m$ planes with coordinates $(x_{k,0}, x_{k,1})$. The **plane rotation** with angles $\varphi$ (`planeRotation φ`) rotates plane $k$ by $\varphi_k$:

```math
\begin{pmatrix} x_{k,0} \\ x_{k,1} \end{pmatrix}
\longmapsto
\begin{pmatrix} \cos\varphi_k & -\sin\varphi_k \\ \sin\varphi_k & \cos\varphi_k\end{pmatrix}
\begin{pmatrix} x_{k,0} \\ x_{k,1} \end{pmatrix}.
```

Its isometry certificate is $\cos^2 + \sin^2 = 1$ in each plane. RoPE rotates the query at position $i$ by angles $\mathrm{pos}_Q(i)\theta_k$ and the key at position $j$ by angles $\mathrm{pos}_K(j)\theta_k$, with zero bias.

### 11.2 Theorems

- `score_standard`: standard scores are $c\langle q, k\rangle$. `standard_positionFree`: they are position-free.
- `alibi_bias_eq_of_offset_eq`: ALiBi biases depend only on the offset $\mathrm{ord}(i) - \mathrm{ord}(j)$.
- **RoPE relativity** (`inner_planeRotation_planeRotation`). Writing $R_\varphi$ for `planeRotation φ`, rotating by $a$ and by $b$ is the same as rotating only the key by $b - a$: $\langle R_a q,\ R_b k\rangle = \langle q,\ R_{b-a} k\rangle$.
  *Proof:* expand both sides plane by plane and use $\cos(b-a) = \cos b\cos a + \sin b \sin a$ and $\sin(b - a) = \sin b\cos a - \cos b \sin a$.
- Consequently (`score_rope`), RoPE scores are $s_{ij} = c\big\langle q,\ R_{(\mathrm{pos}_K(j) - \mathrm{pos}_Q(i))\theta} k\big\rangle$.
  They depend on positions only through the relative offset $\mathrm{pos}_K(j) - \mathrm{pos}_Q(i)$ (`score_rope_eq_of_offset_eq`).

---

## 12. Attention patterns and value mixing

**Module:** [`Architecture/Pattern.lean`](Architecture/Pattern.lean)

### 12.1 Definitions

An **attention pattern** is a row-stochastic matrix $A \in \mathbb{R}^{P_{\mathrm{dst}}\times P_{\mathrm{src}}}$:

```math
A_{ij} \ge 0,\qquad \sum_{j} A_{ij} = 1 .
```

```lean
structure AttnPattern (Pdst Psrc : Type*) [Fintype Psrc] where
  A : Pdst → Psrc → ℝ
  nonneg : ∀ i j, 0 ≤ A i j
  row_sum : ∀ i, ∑ j, A i j = 1
```

Because the row sums are part of the structure, a pattern cannot be built without proving that its rows are probability distributions.

**Value mixing.** For any weights $A$ (not necessarily stochastic) and values $v_j$ in a vector space,

```math
(\mathrm{mix}(A, v))_i = \sum_j A_{ij}\, v_j \qquad(\texttt{mix A v}).
```

Operations on patterns:

- **Support** (`SupportedOn A M`): $A_{ij} = 0$ whenever $\neg M(i,j)$.
- **Composition** (`A.comp B`): the matrix product $(AB)_{ik} = \sum_j A _{ij}B _{jk}$, which is again row-stochastic.
- **Point pattern** (`point f`): $A_{ij} = [j = f(i)]$.
- **Uniform pattern** (`uniform`): $A_{ij} = 1/\lvert P_{\mathrm{src}}\rvert$.

**Pattern rules.** A pattern rule for a mask $M$ turns any score matrix into a pattern supported on $M$:

```lean
structure PatternRule (Pdst Psrc : Type*) [Fintype Psrc] (M : Mask Pdst Psrc) where
  toPattern : (Pdst → Psrc → ℝ) → AttnPattern Pdst Psrc
  supported : ∀ s, (toPattern s).SupportedOn M
```

A rule may have these properties:

- **Row-shift invariant** (`RowShiftInvariant`): adding a constant $c_i$ to every score in row $i$ does not change the pattern.
- **Row-local** (`RowLocal`): row $i$ of the pattern depends only on the allowed scores $\lbrace s_{ij} : M(i,j)\rbrace$ of row $i$.

A **weight rule** (`WeightRule`) produces raw weights that need not be normalized, as in linear or sigmoid attention.

### 12.2 Theorems

| Statement | Lean |
| --- | --- |
| patterns are equal when their matrices are | `AttnPattern.ext` |
| formulas for composition and point patterns | `AttnPattern.comp_A`, `AttnPattern.point_A` |
| every entry is at most one | `AttnPattern.le_one` |
| $\mathrm{mix}$ is linear in the values | `mix_add`, `mix_smul`, `mix_zero` |
| linear maps commute with mixing: $L(\sum_j A_{ij} v_j) = \sum_j A_{ij} L v_j$ | `map_mix` |
| a stochastic pattern preserves constants: $\sum_j A_{ij} c = c$ | `mix_const` |
| composition is iterated mixing: $\mathrm{mix}(AB, v) = \mathrm{mix}(A, \mathrm{mix}(B, v))$ | `mix_comp` |
| **convex hull:** if $A$ is supported on $M$, then $\sum_j A_{ij} v_j \in \mathrm{conv}\lbrace v_j : M(i,j)\rbrace$ | `mix_mem_convexHull` |
| without a mask: $\sum_j A_{ij} v_j \in \mathrm{conv}\lbrace v_j\rbrace$ | `mix_mem_convexHull_range` |

The convex-hull theorem says an attention head can only average the values it is allowed to see. Combined with the separation theorem of [§7.1](#71-linear-threshold-separability-and-convex-hulls), it gives the geometric obstructions for single heads.

---

## 13. Softmax, hardmax, and raw weight rules

**Module:** [`Architecture/Softmax.lean`](Architecture/Softmax.lean)

### 13.1 Definitions

**Softmax over a whole index type** (`softmax`, `softmaxDenom`):

```math
\mathrm{softmax}(s)_i = \frac{e^{s_i}}{\sum_j e^{s_j}} .
```

**Masked softmax at inverse temperature $\beta$** (`maskedSoftmax M β s`, with normalizer `maskedDenom M β s i`):

```math
Z_i = \sum_{j : M(i,j)} e^{\beta s_{ij}},\qquad
A_{ij} = \begin{cases} e^{\beta s_{ij}}/Z_i & M(i,j),\\ 0 & \text{otherwise.}\end{cases}
```

`softmaxRule β hM` packages masked softmax as a `PatternRule`. Its argument `hM : M.WellFormed` is what proves $Z_i \gt 0$, and hence that the rows sum to one. Lean's division by zero returns zero, so without this certificate an empty row would silently produce a "pattern" whose row sums to zero.

**Hardmax** (averaging hard attention). Let $\mathrm{Arg}_i = \lbrace j : M(i,j),\ s _{ij} \ge s _{ij'}\ \text{for all allowed } j'\rbrace$ be the set of allowed maximizers of row $i$ (`argSet`). Then

```math
\mathrm{hardmax}(s)_{ij} = \frac{[\, j \in \mathrm{Arg}_i\,]}{\lvert\mathrm{Arg}_i\rvert}.
```

`hardmaxRule hM` is the corresponding pattern rule. Well-formedness guarantees $\mathrm{Arg}_i \ne \varnothing$, because a nonempty finite row has a maximum.

**Raw weight rules:**

- linear attention (`linearWeights M`): $w_{ij} = [M(i,j)] s_{ij}$;
- sigmoid attention (`sigmoidWeights M β`): $w_{ij} = [M(i,j)]\sigma(\beta s_{ij})$, with Mathlib's `Real.sigmoid`.

### 13.2 Theorems

**Softmax over a type.**

- If the index type is nonempty: $\sum_j e^{s_j} \gt 0$, every weight is positive, and the weights sum to one (`softmaxDenom_pos`, `softmax_pos`, `softmax_nonneg`, `softmax_sum_one`).
- Softmax is invariant under adding a constant: $\mathrm{softmax}(s + c) = \mathrm{softmax}(s)$ (`softmax_add_const`).

**Masked softmax.**

| Statement | Lean |
| --- | --- |
| in a well-formed mask, every row has an allowed source and $Z_i \gt 0$ | `allowedSet_nonempty`, `maskedDenom_pos` |
| formula on allowed entries, zero on disallowed ones, positive on allowed ones | `maskedSoftmax_of_allowed`, `maskedSoftmax_of_not_allowed`, `maskedSoftmax_pos` |
| with the full mask and $\beta = 1$, masked softmax is softmax over the type | `maskedSoftmax_full` |
| masked softmax is softmax over the subtype of allowed sources, applied to $\beta s$ | `maskedSoftmax_eq_softmax_subtype` |
| **row-shift invariance:** $s_{ij} \mapsto s_{ij} + c_i$ leaves $A$ unchanged | `maskedSoftmax_add_row`, `softmaxRule_rowShiftInvariant` |
| **row locality:** row $i$ depends only on the allowed scores of row $i$ | `maskedDenom_congr`, `maskedSoftmax_congr`, `softmaxRule_rowLocal` |
| **monotonicity:** for $\beta \ge 0$, raising one allowed logit $s_{ij}$ while keeping the others raises $A_{ij}$ | `maskedSoftmax_mono_logit` |

*Proof of monotonicity.* Write $Z_i = e_j + R$, where $e_j = e^{\beta s_{ij}}$ and $R$ is the sum over the other allowed sources. Raising $s_{ij}$ changes $e_j$ to some $e'_j \ge e_j$ and leaves $R \ge 0$ unchanged. Then

```math
\frac{e_j}{e_j + R} \le \frac{e'_j}{e'_j + R} \iff e_j R \le e'_j R .
```

**Hardmax.**

- The argmax set is nonempty and consists of allowed sources (`argSet_nonempty`, `argSet_subset_allowedSet`, `mem_argSet`).
- It is unchanged by row shifts and depends only on the allowed scores (`argSet_add_row`, `argSet_congr`).
- Hence the hardmax rule is row-shift invariant and row-local (`hardmax_add_row`, `hardmaxRule_rowShiftInvariant`, `hardmaxRule_rowLocal`).

**Temperature limit** (`tendsto_maskedSoftmax_hardmax`). For a well-formed mask,

```math
\lim_{\beta\to\infty} \mathrm{maskedSoftmax}_\beta(s)_{ij} = \mathrm{hardmax}(s)_{ij} .
```

*Proof.*

- Let $m = \max_{j\ \text{allowed}} s_{ij}$, and divide the numerator and denominator by $e^{\beta m}$. This gives $A_{ij} = \frac{[M(i,j)] e^{\beta(s_{ij} - m)}}{\sum_{k\ \text{allowed}} e^{\beta(s_{ik} - m)}}$.
- For each allowed $k$, the term $e^{\beta(s_{ik} - m)}$ equals $1$ when $k$ attains the maximum, and tends to $0$ as $\beta \to \infty$ when $s_{ik} \lt m$.
- So the numerator tends to $[j \in \mathrm{Arg}_i]$ and the denominator tends to $\lvert \mathrm{Arg}_i\rvert \gt 0$. Their ratio tends to the hardmax weight.

---

## 14. Attention heads

**Module:** [`Architecture/Attention.lean`](Architecture/Attention.lean)

### 14.1 Definitions

An attention head has **affine** query, key, and value projections and a **linear** output projection. The residual space is $V$, the query/key space is $K$, and the value space is $U$:

```lean
structure AttentionHead (V K U : Type*) [...] where
  WQ : V →ᵃ[ℝ] K
  WK : V →ᵃ[ℝ] K
  WV : V →ᵃ[ℝ] U
  WO : U →ₗ[ℝ] V
```

Fix a score rule $\sigma$, a mask $M$, and a pattern rule $\rho$ for $M$. For a destination stream $X$ and a source stream $Y$ (self-attention is the case $X = Y$, cross-attention the case $X \ne Y$), the head computes

```math
\begin{aligned}
q_i &= W_Q X_i, \qquad k_j = W_K Y_j, \qquad v_j = W_V Y_j,\\
s_{ij} &= \sigma.\mathrm{score}(i, j, q_i, k_j), \qquad A = \rho(s),\\
z_i &= \sum_j A_{ij}\, v_j, \qquad y_i = W_O\, z_i .
\end{aligned}
```

Every intermediate quantity is a named definition, because interpretability questions often concern these quantities rather than only the output.

| Quantity | Lean |
| --- | --- |
| $q$, $k$, $v$ | `h.queries X`, `h.keys Y`, `h.values Y` |
| $s$ | `h.scores σ X Y` |
| $A$ | `h.pattern σ ρ X Y` |
| $z$ under the live pattern | `h.z σ ρ X Y` |
| $y$ under the live pattern | `h.result σ ρ X Y` |
| $z$, $y$ under a *supplied* weight matrix $A$ | `h.mixWith A Y`, `h.resultWith A Y` |
| $y$ under raw weights from a weight rule | `h.resultWeights σ w X Y` |
| the OV map $W_O \circ (W_V)_{\mathrm{lin}}$ | `h.WOV` |
| $W_Q$, $W_K$, $W_V$ all bias-free | `h.BiasFree` |

`resultWith` takes the pattern as an argument. This is what "freezing" an attention pattern means mathematically: once $A$ is fixed, the head is an affine function of its input, while the live head (`result`) is not.

`PatternRule.PermEquivariant ρ π` states that relabeling positions by a permutation $\pi$ relabels the pattern:

```math
\rho\big((s_{\pi i, \pi j})_{ij}\big)_{ij} = \rho(s)_{\pi i, \pi j}.
```

### 14.2 What the definitions guarantee

The definitions already carry the structure the theorems use:

- every pattern produced by a rule is row-stochastic;
- every pattern is supported on its mask;
- the softmax rule's denominators are certified positive.

### 14.3 Theorems

| Statement | Lean |
| --- | --- |
| $y_i = \sum_j A_{ij} W_O W_V Y_j$, that is, $W_O$ commutes with mixing | `resultWith_apply`, `resultWith_eq_mix`, `result_eq_resultWith` |
| for a fixed pattern and bias-free $W_V$, the output is linear in $Y$ | `resultWith_add`, `resultWith_smul` |
| **value bias passes through:** for a stochastic $A$, $y_i = \sum_j A_{ij} W_{OV} Y_j + W_O b_V$ | `resultWith_pattern` |
| **key bias is irrelevant:** shifting every key by $\delta$ leaves the pattern and output of a row-shift-invariant rule unchanged, if keys are not rotated position-dependently | `pattern_eq_of_key_shift`, `result_eq_of_key_shift` |
| mixed values lie in the convex hull of the allowed values | `z_mem_convexHull` |
| **permutation equivariance:** with a position-free score rule and a permutation-equivariant pattern rule, $\mathrm{result}(X\circ\pi) = \mathrm{result}(X)\circ\pi$ | `AttentionHead.result_perm` |
| full-mask softmax is permutation equivariant | `softmaxRule_full_permEquivariant` |
| **causal locality:** if $M(i,j) \Rightarrow \mathrm{ord}(j) \le \mathrm{ord}(i)$ and the rule is row-local, then $y_i$ depends only on $\lbrace X_j : \mathrm{ord}(j) \le \mathrm{ord}(i)\rbrace$ | `AttentionHead.result_eq_of_agree_before` |

Proof ideas:

- **Key bias.** Shifting keys by $\delta$ adds $c\langle R_i q_i, R\delta\rangle$ to every score in row $i$. This term does not depend on $j$, so a row-shift-invariant rule ignores it. The output then agrees because the two heads share $W_V$ and $W_O$ and now share the pattern.
- **Value bias.** Since $\sum_j A_{ij} = 1$, the bias contributes $\sum_j A_{ij} W_O b_V = W_O b_V$.
- **Causal locality.** Row $i$ of the scores involves only the allowed $j$, all of which have $\mathrm{ord}(j) \le \mathrm{ord}(i)$. Disallowed entries of $A$ are zero.

---

## 15. Multi-head attention

**Module:** [`Architecture/MultiHead.lean`](Architecture/MultiHead.lean) (definitions only; there are no theorems about multi-head layers yet)

A multi-head layer has a finite head type and, for each head $h$, a query/key width $d_K(h)$ and a value width $d_V(h)$. Heads may have different widths. Each head comes with its own score rule; the mask, the pattern rule, and an output bias $b_O$ are shared:

```lean
structure MultiHead (Pdst Psrc V : Type*) [Fintype Psrc] [AddCommGroup V] [Module ℝ V] where
  Head : Type
  [fin : Fintype Head]
  [deq : DecidableEq Head]
  dK dV : Head → ℕ
  heads : (h : Head) → AttentionHead V (Vec (dK h)) (Vec (dV h))
  score : (h : Head) → ScoreRule Pdst Psrc (Vec (dK h))
  mask : Mask Pdst Psrc
  rule : PatternRule Pdst Psrc mask
  bO : V
```

**All heads read the same pre-update stream** (`eval`, with `evalSelf` for $X = Y$):

```math
\mathrm{MHA}(X, Y)_i = b_O + \sum_{h} y^{(h)}_i(X, Y).
```

Per-head views are `pattern h`, `z h`, and `headResult h`.

**Frozen and edited evaluation** (`evalOver pat edit`). Each head may have its pattern replaced by a supplied pattern (`pat h = some A`), and its output passed through an edit function (`edit h = some g`):

```math
\mathrm{MHA}^{\mathrm{over}}(X,Y)_i = b_O + \sum_h g_h\big(W_O^{(h)} \textstyle\sum_j \tilde A^{(h)}_{ij}\, W_V^{(h)} Y_j\big)_i,
\qquad \tilde A^{(h)} = \begin{cases} A & \text{if supplied,}\\ \text{live pattern} & \text{otherwise.}\end{cases}
```

This is the semantics behind frozen attention patterns, head ablation, and head patching.

**Concatenated view.** Concatenate the heads' mixed values into $z^{\mathrm{cat}}_i \in \mathbb{R}^{\Sigma_h \mathrm{Fin} d_V(h)}$ (`zCat`), and define

```math
W_O^{\mathrm{cat}} = \sum_h W_O^{(h)} \circ \mathrm{proj}_h \qquad(\texttt{WOcat}).
```

Then $W_O^{\mathrm{cat}} z^{\mathrm{cat}}_i = \sum_h W_O^{(h)} z^{(h)}_i$, which matches the concatenated $W_O$ matrix of the standard presentation. This identity follows from `Block.proj_concat` but is not yet stated as a theorem.

`MultiHead.uniform` builds a layer in which every head has the same widths. XORFormer uses it.

---

## 16. What is not yet formalized

The library does not yet formalize the following:

- **Architecture:**
  - theorems for multi-head attention;
  - MLPs and gated MLPs;
  - LayerNorm and RMSNorm as scaled affine maps;
  - residual components and residual networks;
  - pre-norm, post-norm, and parallel blocks, and transformer stacks;
  - readouts and language-model interfaces;
  - parameter spaces and reparameterization symmetries;
  - width padding and conjugation.
- **Semantics:** causal models, node and edge interventions, compilation of transformers into causal models, frozen semantics, path expansion, direct logit attribution, attribution patching, and integrated gradients.
- **Interpretability:** metrics, probes and decodability, subspace interventions, sparse dictionaries and replacement models, superposition, circuits and faithfulness, QK/OV circuit views, and causal abstraction.
- **Expressivity:** model classes, decision rules, realization, minimal resources, and simulation.
- **Claims, worked examples, and tooling:** formal interpretability claims, worked examples, and validation scripts.

Closest to finishing: theorems about `MultiHead`, such as $W_O^{\mathrm{cat}} z^{\mathrm{cat}}_i = \sum_h W_O^{(h)} z^{(h)}_i$.

## 17. Module index

Modules in dependency order. The last column lists the MechInterp modules each one imports; everything else comes from Mathlib.

| # | Topic | Module | Imports from MechInterp |
| --- | --- | --- | --- |
| 1 | Positive normalizers | [`Math/Normalizers.lean`](Math/Normalizers.lean) | — |
| 2 | Convex separation | [`Math/ConvexSeparation.lean`](Math/ConvexSeparation.lean) | — |
| 3 | Partial fractions | [`Math/PartialFraction.lean`](Math/PartialFraction.lean) | — |
| 4 | Boolean square | [`Math/BoolSquare.lean`](Math/BoolSquare.lean) | — |
| 5 | Spaces and streams | [`Algebra/Spaces.lean`](Algebra/Spaces.lean) | — |
| 6 | Affine maps | [`Algebra/Affine.lean`](Algebra/Affine.lean) | — |
| 7 | Block maps | [`Algebra/Blocks.lean`](Algebra/Blocks.lean) | `Algebra/Spaces` |
| 8 | Rank and factorization | [`Algebra/Rank.lean`](Algebra/Rank.lean) | `Algebra/Spaces` |
| 9 | Finite distributions | [`Data/FinDist.lean`](Data/FinDist.lean) | — |
| 10 | Embeddings | [`Architecture/Embedding.lean`](Architecture/Embedding.lean) | `Algebra/Spaces` |
| 11 | Masks | [`Architecture/Mask.lean`](Architecture/Mask.lean) | — |
| 12 | Score rules | [`Architecture/Score.lean`](Architecture/Score.lean) | `Algebra/Spaces` |
| 13 | Patterns | [`Architecture/Pattern.lean`](Architecture/Pattern.lean) | `Architecture/Mask` |
| 14 | Softmax and hardmax | [`Architecture/Softmax.lean`](Architecture/Softmax.lean) | `Architecture/Pattern`, `Math/Normalizers` |
| 15 | Attention heads | [`Architecture/Attention.lean`](Architecture/Attention.lean) | `Algebra/Affine`, `Architecture/Score`, `Architecture/Softmax` |
| 16 | Multi-head attention | [`Architecture/MultiHead.lean`](Architecture/MultiHead.lean) | `Algebra/Blocks`, `Architecture/Attention` |
| — | Umbrella | [`All.lean`](All.lean) | every module above |

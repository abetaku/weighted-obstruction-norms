# Weighted Obstruction Norms for Finite Marginal Complexes

[English](README.md) | [日本語](README_ja.md)

Takuya Abe

When reconciling partial observations into a consistent whole, the existence of a solution and the existence of a solution within a prescribed bound are different questions. This paper uses weighted norms to quantify the size of the correction needed to resolve a cohomological obstruction by enlarging the support of the state space.

| Paper | PDF | TeX |
| --- | --- | --- |
| Japanese | [Read](paper/weighted_obstruction_norms_ja.pdf) | [Source](paper/weighted_obstruction_norms_ja.tex) |
| English | [Read](paper/weighted_obstruction_norms_en.pdf) | [Source](paper/weighted_obstruction_norms_en.tex) |

## Abstract

We construct an augmented Čech complex from the marginalization of local signed measures associated with a finite collection of observations and a prescribed support. When a nonzero cohomology class exists on that support, mixing in a small amount of a full-support probability law restores the existence of a primitive, but its minimum weighted norm diverges. For a fixed nonzero class, we show that this minimum is **exactly proportional to the reciprocal of the mixing parameter** for all sufficiently small positive parameters.

The coefficient defines a norm on the obstruction space. Its unit ball is a centrally symmetric polytope: the image, under the connecting homomorphism, of the intersection of the relative cocycle space with a weighted coordinate box. The norm is independent of the list generating the observation family and is nonincreasing under support enlargement and observation restriction. We also establish isometric comparison with the order-complex presentation in degrees zero and one, exact computations for binary examples, and a limiting formula for nonaffine weights with a common vanishing scale.

## What does the theory measure?

Consider three variables that cannot be observed jointly, but can be observed in pairs. On overlaps, marginalization provides consistency conditions for comparing observations. Restricting the global states to a specified set can create local data or corrections that cannot be realized within that set.

Now assign small positive probabilities to previously excluded states. Even if the linear equations become solvable, the required corrections may have to be carried by rare states, making the ratio of correction to probability large. The theory measures the burden that remains even after optimizing this ratio.

More precisely, let $`A`$ be a set of observed variables, $`a`$ an observed state, $`x_A(a)`$ a local signed measure, and $`q_A(a)`$ a positive reference marginal probability. Define

```math
m_A(a)=\frac{x_A(a)}{q_A(a)}
```

The weighted norm is the maximum of $`|m_A(a)|`$ over the relevant observation components and states. Thus, a norm bound of one means that $`|x_A(a)|\le q_A(a)`$ in each component.

In degree zero, the problem concerns extending consistent local data to a global signed measure. In degree one, it concerns correcting a prescribed local inconsistency. Because signed measures are allowed, these conditions differ from the existence of a nonnegative probability distribution.

## Main result

Let $`E`$ be the full state space and $`S\subseteq E`$ the set of originally allowed states. Let $`q_0`$ be a probability law that is positive on $`S`$ and zero outside it, and let $`q_1`$ be a reference law that is positive on every state of $`E`$. For a mixing parameter $`0<\varepsilon\le1`$, define

```math
q_\varepsilon=(1-\varepsilon)q_0+\varepsilon q_1
```

Write $`C_S`$ for the marginal complex associated with support $`S`$, $`\delta`$ for its differential, and $`c`$ for a fixed cocycle of degree $`p\ge0`$. The equation $`\delta c=0`$ expresses consistency, while the cohomology class $`[c]`$ records the obstruction to finding a primitive of $`c`$ on the original support. If $`j`$ denotes extension by zero outside the support, the minimum cost of a primitive $`x`$ on the full state space is

```math
\Gamma_\varepsilon(c)
=\min_{\delta x=jc}\|x\|_{q_\varepsilon,p-1}
```

Here $`\|x\|_{q_\varepsilon,p-1}`$ is the weighted maximum norm in degree $`p-1`$; in degree $`-1`$, it is the norm on signed measures on the full state space.

**If $`[c]\ne0`$, then for all sufficiently small positive $`\varepsilon`$,**

```math
\Gamma_\varepsilon(c)=\frac{N([c])}{\varepsilon}.
```

The obstruction norm $`N`$ is determined by the support, the observation family, and the reference law $`q_1`$. This is an exact equality, not an approximation. The range of mixing parameters for which it holds depends on the data. When $`[c]=0`$, this divergence does not occur: the minimum cost converges to the minimum on the original support.

| Result | Interpretation |
| --- | --- |
| Exact reciprocal law | Identifies the coefficient governing the divergence of the cost of resolving a fixed nonzero obstruction |
| Relative cohomology description | Expresses the minimum cost of resolving an obstruction through newly available coordinates as a quotient norm induced by the connecting homomorphism |
| Invariance under generating lists | Lists generating the same downward-closed observation family yield isometrically identified obstruction spaces |
| Comparison under support enlargement and observation restriction | The obstruction norm does not increase under the induced cohomology maps |
| Extension to a common vanishing scale | Describes the limit of the rescaled minimum when the new-coordinate weights vanish at a common scale |

## Binary examples

The paper gives explicit computations for variables taking values $`-1`$ or $`1`$. In both examples, the original law is uniform on the states where all variables agree, and the reference law is uniform on the full state space.

- **Two variables observed separately (degree zero):** For the local datum specified in the paper, the minimum primitive norm is $`2/\varepsilon`$ for every $`0<\varepsilon\le1`$. The obstruction space is one-dimensional, and the specified class has norm $`2`$.
- **Three variables observed in pairs (degree one):** For the prescribed inconsistency in the paper, the minimum correction norm is the following for every $`0<\varepsilon\le1`$.

```math
\Gamma_\varepsilon(c)=\max\left\lbrace 1,\frac{2}{3\varepsilon}\right\rbrace.
```

In the second example, the linear equations have a solution for every positive mixing parameter, however small. Yet **a correction of norm at most one exists if and only if $`\varepsilon\ge2/3`$**. This illustrates the distinction between solvability and realizability within a prescribed bound.

## Scope and context

The paper connects finite-dimensional cohomology, relative complexes, and quotient norms with marginal problems carrying support constraints and probability weights. Its focus is to measure the cost of resolving an obstruction, alongside detecting its existence, in a way that permits comparison when observations or supports change.

The setting consists of finite state spaces and real signed measures. The resulting norm is not identified with a contextuality measure. Isometric comparison with the order-complex presentation is established in degrees zero and one; isometry in degrees two and higher, and the analysis of unequal coordinate vanishing scales, remain questions for further study.

## Code and verification records

Lean code corresponding to the paper and its verification records are included. See the [formalization scope](docs/FORMALIZATION_STATUS.md), [manuscript coverage table](audit/paper_coverage.json), and [verification record](audit/verification.json). These records describe an earlier execution; Lean was not rerun as part of this README update.

| Location | Contents |
| --- | --- |
| [paper/](paper/) | Japanese and English manuscripts in PDF and TeX |
| [WeightedObstructionNorms/](WeightedObstructionNorms/) | Lean proof code |
| [audit/](audit/) | Manuscript correspondence, build and axiom-audit records, and reproduction environment |
| [scripts/](scripts/) | Verification and packaging scripts |
| [docs/](docs/) | Formalization documentation, collaboration rules, and revision and import history |

To rerun verification from the repository root, use an environment with Python 3 and elan, the toolchain manager for Lean 4.19.0. The mathlib version is pinned in the configuration files.

```sh
lake exe cache get
python3 scripts/verify.py
```

The verification script updates the current audit files. Checking the encoded propositions and confirming their semantic correspondence with the manuscript are distinct tasks. Implementation details are described in the [Lean technical documentation](docs/LEAN.md) (in Japanese).

## License

Copyright © 2026 Takuya Abe

The works in this repository are provided under **Apache License 2.0**, except as specified below. Third-party material, dependencies, and material with separate stated terms remain subject to their respective terms.

| Material | Applicable license |
| --- | --- |
| Manuscript PDFs and TeX files in `paper/`, `README.md`, `README_ja.md`, and Markdown documents in `docs/` (including historical documents) | **CC BY 4.0 (Attribution 4.0 International)** — [Summary](https://creativecommons.org/licenses/by/4.0/) · [Legal code](https://creativecommons.org/licenses/by/4.0/legalcode.en) |
| All other project files, including Lean code, scripts, configuration files, `AGENTS.md`, and audit material in `audit/` | **Apache License 2.0** — [Full text](LICENSE) |

The manuscripts and documentation may be copied, redistributed, translated, adapted, and used commercially under the terms of CC BY 4.0, including appropriate attribution, a link to the license, and an indication of changes. Code and other material may be used, modified, and redistributed under Apache License 2.0, including its requirements to retain license and copyright notices and indicate changes.

When using this work in research or teaching, please consider citing the paper title, author, repository URL, and the version or commit used. This citation request does not impose additional restrictions on the licenses.

## Research and verification status

This work is personal mathematical research and has not undergone peer review. See the [formalization coverage](docs/FORMALIZATION_STATUS.md) and [verification record](audit/verification.json) for the scope of Lean verification and its correspondence with the manuscript.

Lean verification concerns the propositions encoded in the code. It does not automatically guarantee semantic correspondence with the entire manuscript, novelty, or suitability for a particular use. The material and code are provided as is; warranty disclaimers and limitations of liability are governed by the respective licenses. Reports of errors and suggestions for improvement are welcome.

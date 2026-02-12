# First Proof — AI Challenge

Attempting the [1st Proof](https://1stproof.org/) research-level mathematics challenge.
Paper: [arXiv:2602.05192](https://arxiv.org/abs/2602.05192)

## Deadline

**February 13, 2026 — 11:59pm Pacific Time** (solutions released after this)

## Status Tracker

| # | Problem | Domain | Status | Difficulty Est. |
|---|---------|--------|--------|-----------------|
| 1 | [Φ⁴₃ measure equivalence](problems/P01_stochastic_phi4/) | Stochastic Analysis | 🟢 Draft complete | ⭐⭐⭐⭐⭐ |
| 2 | [Rankin–Selberg integrals](problems/P02_representation_rankin_selberg/) | Representation Theory | ⬜ Not started | ⭐⭐⭐⭐⭐ |
| 3 | [Markov chain / Macdonald](problems/P03_combinatorics_markov_macdonald/) | Algebraic Combinatorics | ⬜ Not started | ⭐⭐⭐⭐ |
| 4 | [Free convolution inequality](problems/P04_spectral_free_convolution/) | Spectral / Free Probability | ⬜ Not started | ⭐⭐⭐⭐ |
| 5 | [Slice filtration](problems/P05_topology_slice_filtration/) | Algebraic Topology | 🟢 Draft complete | ⭐⭐⭐⭐⭐ |
| 6 | [ε-light subsets](problems/P06_spectral_epsilon_light/) | Spectral Graph Theory | 🟡 Partial results | ⭐⭐⭐ |
| 7 | [Lattice acyclicity](problems/P07_lattices_acyclicity/) | Lattices in Lie Groups | ⬜ Not started | ⭐⭐⭐⭐ |
| 8 | [Lagrangian smoothing](problems/P08_symplectic_lagrangian_smoothing/) | Symplectic Geometry | ⬜ Not started | ⭐⭐⭐⭐⭐ |
| 9 | [Quadrilinear tensors](problems/P09_tensor_quadrilinear/) | Tensor / Algebraic Geometry | ⬜ Not started | ⭐⭐⭐⭐ |
| 10 | [PCG for CP with RKHS](problems/P10_numerical_cp_rkhs/) | Numerical Linear Algebra | 🟢 Draft complete | ⭐⭐⭐ |

### Legend

- ⬜ Not started
- 🟡 In progress
- 🟢 Draft complete
- ✅ Polished / submitted

## Suggested Priority Order

Based on tractability for AI (more concrete/computational → more abstract/conceptual):

1. **P10** — Numerical LA: concrete algorithmic question, well-defined answer format
2. **P06** — ε-light subsets: clean combinatorial/spectral problem
3. **P04** — Free convolution inequality: concrete inequality to prove
4. **P07** — Lattice acyclicity: yes/no question with topological tools
5. **P01** — Φ⁴₃ measure: yes/no, but deep stochastic PDE theory
6. **P03** — Markov/Macdonald: constructive, but specialized combinatorics
7. **P09** — Quadrilinear tensors: algebraic geometry, existence proof
8. **P02** — Rankin–Selberg: deep number theory / automorphic forms
9. **P05** — Slice filtration: highly specialized equivariant homotopy theory
10. **P08** — Lagrangian smoothing: cutting-edge symplectic topology

## Project Structure

```
First Proof/
├── README.md                       ← You are here
├── First Proof.md                  ← Original notes
├── First_Proof.tex                 ← LaTeX source of paper
├── problems/
│   ├── P01–P10 folders, each with:
│   │   ├── problem.md              ← Problem statement
│   │   ├── approach.md             ← Strategy & key ideas
│   │   ├── proof.md                ← Working proof draft
│   │   ├── references.md           ← Relevant papers
│   │   └── transcript.md           ← AI interaction log
├── shared/
│   ├── notation.md                 ← Common notation
│   └── references.md               ← Shared bibliography
└── submissions/                    ← Final polished proofs
```

## Rules of Engagement (from 1st Proof)

- AI must produce proofs **autonomously** — no human mathematical input
- Proofs must meet **publication-level rigor and scholarship**
- Citations must include **precise statement numbers** from peer-reviewed journals or arXiv
- Share transcripts and results with **#1stProof**

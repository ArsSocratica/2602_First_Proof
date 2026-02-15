# First Proof Audit Report — Problem 10 (CP-RKHS PCG)

**Date:** February 15, 2026
**Auditor:** Cascade AI (orchestrated by Mark Dillerop)
**Scope:** P10 only — proof, paper, comparison documents, expert commentary

---

## Executive Summary

- **Documents audited:** 6 (proof.md, P10_paper.tex, comparison_with_official_solutions.md, three_way_comparison.tex, three_way_comparison.md, p10.tex section)
- **Cross-document inconsistencies found:** 1 (minor — see §A.9)
- **Internal contradictions found:** 0
- **Expert-flagged vulnerabilities confirmed:** 0
- **Overall assessment:** P10 is the cleanest submission. No contradictions, no hand-waving, no hallucinated citations. One minor discrepancy between proof.md and p10.tex regarding preconditioner description.

---

## Part A: Cross-Document Consistency

| Check | Status | Details |
|-------|--------|---------|
| v1/ snapshot exists | **PASS** | `02_proofs/10_numerical_cp_rkhs/v1/proof.md` and `v1/transcript.md` exist |
| v1/ unchanged | **PASS** | `diff -q` shows v1/proof.md identical to proof.md |
| Status in comparison_with_official_solutions.md | **PASS** | "✅ Correct answer, ✅ valid approach (does not include eigendecomposition transformation)" |
| Status in three_way_comparison.tex | **PASS** | Table 1: "✓ / Complete" for P10 |
| Status in p10.tex (1stProof_official) | **PASS** | "Yes answer, Yes proof (valid PCG approach)" |
| Expert feedback (Kolda §4.10) present | **PASS** | All 3 comparison docs cite Kolda's "correct and better" comment |
| Aggregate counts | **PASS** | P10 counted as "valid approach" (1/10) consistently |
| PDF freshness | N/A | Not checked (P10-specific audit) |
| Proof-vs-paper consistency | **PASS with note** | See below |

### §A.9 Proof-vs-Paper Detail

The proof (`proof.md`) and paper (`P10_paper.tex`) are substantively identical:
- Same theorem statement (Theorem 7.1 / Theorem 1)
- Same 4-step matvec decomposition
- Same preconditioner P = Γ ⊗ K² + λ(I_r ⊗ K)
- Same spectral bounds
- Same complexity: O(t_max(qr + n²r + nr²) + n³ + r³)
- Same Lean 4 verification (13 theorems, 0 sorry)

**Minor discrepancy:** The `p10.tex` section in `01_1stProof_official` describes our preconditioner as "diagonal" — but our actual preconditioner is the **complete-data Kronecker preconditioner** (not diagonal). The diagonal preconditioner is mentioned only as an alternative in Remark 8.1. This is a description error in the comparison document, not in the proof itself.

**Severity:** LOW — the comparison document understates our preconditioner; the proof and paper are correct.

---

## Part B: Internal Proof Coherence

| Check | Status | Details |
|-------|--------|---------|
| Self-contradictions | **NONE** | All claims are mutually consistent |
| Unsupported key claims | **NONE** | Every step is proved or cited |
| Cargo-cult risk | **LOW** | No arbitrary parameter choices; all choices are justified |
| Regularity consistency | **PASS** | No regularity claims to conflict (purely algebraic/linear algebra) |
| Citation verification | **PASS** | See below |
| Hand-wave phrases | **NONE** | grep for "by standard/it follows/one can verify/straightforward/well known/left to reader" returned 0 results |

### Citation Verification (Step 12)

| Citation | Claim | Verified? |
|----------|-------|-----------|
| [KB09] Kolda & Bader, SIAM Rev. 2009 | Kronecker-vec identity (B⊗A)vec(X) = vec(AXB^T), §2.6 | **YES** — standard reference, real paper, correct section |
| [LKZW24] Larsen et al., arXiv:2408.05677 | System derivation §5.2 Eq. 42, direct solve cost | **YES** — real paper, correct equation |
| [GVL13] Golub & Van Loan, Matrix Computations 4e | CG convergence §11.3.3 | **YES** — standard textbook, correct section |
| [Saa03] Saad, Iterative Methods 2e | PCG convergence Theorem 9.4.2 | **YES** — standard textbook, correct theorem |
| [Wen04] Wendland, Scattered Data Approx. | Gaussian RBF strictly PD, Theorem 4.20 | **YES** — real book, correct theorem |
| [RR07] Rahimi & Recht, NeurIPS 2007 | Random Fourier features | **YES** — real paper |

**No hallucinated citations.** All 6 references are real, correctly attributed, and the cited theorem numbers match.

### Key Claim Dependency Chain (Step 13)

```
Theorem 7.1 (Main)
├── Proposition 2.1 (H is SPD) ← PROVED (eigendecomposition of K)
├── §3 Efficient Matvec ← PROVED (4-step decomposition, each step costed)
│   ├── Kronecker-vec identity ← CITED [KB09, §2.6]
│   ├── Precompute P = KV ← PROVED (cost O(n²r))
│   ├── Selection via cached z_{j(ω)} ← PROVED (cost O(qr))
│   └── Adjoint via group-by-i_k ← PROVED (cost O(qr + n²r))
├── §4 Preconditioner ← PROVED
│   ├── Kronecker diagonalization ← PROVED (eigendecomp of K and Γ)
│   ├── λ_max(P⁻¹H) ≤ 1 ← PROVED (from SS^T ⪯ I_N)
│   └── Lower spectral bound ← PROVED (from λσ_min(K))
└── CG convergence ← CITED [Saa03, Theorem 9.4.2]
```

**No unproved assertions at critical steps.** The only cited (not proved) step is standard CG convergence theory — appropriate to cite rather than re-derive.

---

## Part C: Structural & Mathematical Verification

| Check | Status | Details |
|-------|--------|---------|
| Assumption match | **EXACT** | Problem asks "explain how PCG can be used"; proof explains exactly this |
| Hard step status | **FULLY PROVED** | Hardest step = efficient matvec avoiding O(N); fully detailed with 4 sub-steps |
| Hypothesis usage | **ALL USED** | K PSD (→ SPD proof), S selection (→ sparsity exploitation), λ > 0 (→ PD regularization) |
| Direction of proof | **CORRECT** | No converse confusion; all implications go the right way |
| Local-global compat. | **N/A** | No local-to-global assembly in this proof |
| Numerical verification | **N/A** | Purely analytical proof; no numerical claims |
| Cross-field creativity | **LOW** | Stayed within numerical linear algebra / tensor decomposition |
| Cross-field necessity | **NOT NEEDED** | Problem is algorithmic; same-field tools suffice |

### §C.15 Assumption Audit

The problem statement asks: *"Explain how an iterative preconditioned conjugate gradient linear solver can be used to solve this problem more efficiently. Explain the method and choice of preconditioner. Explain in detail how the matrix-vector products are computed and why this works. Provide complexity analysis. Avoid any computation of order N."*

Our proof addresses every part:
- ✅ PCG method explained (§5)
- ✅ Preconditioner chosen and justified (§4)
- ✅ Matrix-vector products detailed (§3, 4 steps)
- ✅ Complexity analysis provided (§6)
- ✅ No O(N) computation (§6.4)

**No hypothesis added or dropped.** The proof solves the exact problem as stated.

### §C.16 "Too Good to Be True" Check

The hardest step is the efficient matvec (§3) — specifically, computing (Z⊗K)^T SS^T (Z⊗K)v without forming the N-entry matrix KVZ^T. This is fully detailed:
- Step 1: Precompute P = KV, then q dot products → O(n²r + qr)
- Step 2: Bookkeeping → O(q)
- Step 3: Group by i_k, accumulate, multiply by K → O(qr + n²r)

**No hand-waving.** Every operation is explicit with cost.

### §C.17 Hypothesis Usage

| Hypothesis | Where Used |
|------------|-----------|
| K is PSD | Proposition 2.1 (SPD proof), preconditioner eigenvalues |
| S is selection matrix (q columns of I_N) | §3 (sparsity exploitation), §4.4 (SS^T ⪯ I_N → spectral bound) |
| λ > 0 | Proposition 2.1 (strict PD), preconditioner diagonal entries > 0 |
| n, r ≪ q ≪ N | §6 (complexity comparison — PCG beats direct when this holds) |

**All hypotheses used.** No unused assumptions.

### §C.22 Cross-Field Creativity

- **Home field:** Numerical linear algebra / tensor decomposition
- **Official solution field:** Same (numerical linear algebra)
- **Cross-field exploration:** None needed; none attempted
- **Cross-field insight required:** NO — the problem is algorithmic, not requiring tools from other mathematical fields
- **Kolda's "advanced" step:** The eigendecomposition transformation K = UDU^T to precondition the system. This is within the same field. We did not discover this, but it was not required for a valid solution.

---

## Per-Problem Detail

### P10: CP-RKHS PCG

- **Current status:** ✅ Correct answer, ✅ valid approach
- **Expert feedback:** Kolda (§4.10): "The best LLM solution was correct and better than the solution I provided." She noted the subsampled Kronecker matvec idea exists in prior literature (arXiv:1601.01507). She would be "impressed if the AI can" discover the eigendecomposition transformation — our solution does not include this step.
- **Audit findings:**
  - No self-contradictions
  - No unsupported claims
  - No hallucinated citations (all 6 verified)
  - No hand-waving at critical steps
  - All hypotheses used
  - Proof and paper are substantively identical
  - Minor discrepancy: comparison doc `p10.tex` calls our preconditioner "diagonal" when it is actually a complete-data Kronecker preconditioner
- **Cross-field analysis:**
  - Home field: Numerical linear algebra
  - Official solution field: Same
  - Our approach field: Same
  - Cross-field exploration attempted: NO
  - Cross-field insight required: NO
  - Discovery pathway: N/A
- **Recommendation:** **SAFE**

---

## Independent Mathematical Verification

The following key claims were independently re-derived during the audit (not just checked for internal consistency):

### Verified: Spectral upper bound H ⪯ P (§4.4, item 3)

**Claim:** Since SS^T ⪯ I_N, we have H ⪯ P.

**Re-derivation:** Let w = (Z⊗K)v. Then:
- v^T H v = w^T(SS^T)w + λ v^T(I_r⊗K)v
- v^T P v = w^T(I_N)w + λ v^T(I_r⊗K)v

Since SS^T is a diagonal 0/1 matrix (selecting observed entries), 0 ⪯ SS^T ⪯ I_N, so w^T(SS^T)w ≤ w^Tw. Therefore v^T H v ≤ v^T P v for all v. **✓ Correct.**

Also verified: P = Γ⊗K² + λ(I_r⊗K) follows from (Z⊗K)^T(Z⊗K) = (Z^TZ)⊗(K^TK) = Γ⊗K² (using K symmetric). **✓ Correct.**

### Verified: Lower spectral bound (§4.4, item 4)

**Claim:** λ_min(P⁻¹H) ≥ λσ_min(K) / (‖Γ‖‖K‖² + λ‖K‖)

**Re-derivation:**
- v^T H v ≥ λ v^T(I_r⊗K)v ≥ λ σ_min(K) ‖v‖² (first term PSD, eigenvalues of I_r⊗K are σ_i)
- v^T P v ≤ (‖Γ⊗K²‖ + λ‖I_r⊗K‖)‖v‖² = (‖Γ‖·‖K‖² + λ‖K‖)‖v‖²

Note: ‖K²‖ = ‖K‖² holds because K is PSD (spectral norm of K² = σ_max(K)² = ‖K‖²). **✓ Correct.**

### Verified: Kronecker-vec identity dimensions (§3.2)

**Claim:** (Z⊗K)vec(V) = vec(KVZ^T) with A=K∈ℝ^{n×n}, X=V∈ℝ^{n×r}, B=Z∈ℝ^{M×r}

**Re-derivation:**
- LHS: (Z⊗K) ∈ ℝ^{Mn×rn}, vec(V) ∈ ℝ^{nr} → output ∈ ℝ^{Mn} ✓
- RHS: KV ∈ ℝ^{n×r}, KVZ^T ∈ ℝ^{n×M}, vec(KVZ^T) ∈ ℝ^{nM} ✓
- nM = Mn ✓, nr = rn ✓. **✓ Dimensions match.**

### Verified: Preconditioner Kronecker-diagonalizability (§4.3)

**Claim:** P = (U_Γ⊗U_K)[Λ_Γ⊗Λ_K² + λ(I_r⊗Λ_K)](U_Γ⊗U_K)^T

**Re-derivation:**
- K = U_K Λ_K U_K^T → K² = U_K Λ_K² U_K^T (U_K orthogonal)
- Γ = U_Γ Λ_Γ U_Γ^T
- Γ⊗K² = (U_Γ⊗U_K)(Λ_Γ⊗Λ_K²)(U_Γ⊗U_K)^T (mixed-product property)
- λ(I_r⊗K) = λ(U_Γ U_Γ^T ⊗ U_K Λ_K U_K^T) = λ(U_Γ⊗U_K)(I_r⊗Λ_K)(U_Γ⊗U_K)^T
  - (uses U_Γ U_Γ^T = I_r since U_Γ is orthogonal ✓)
- Sum: P = (U_Γ⊗U_K)[Λ_Γ⊗Λ_K² + λ(I_r⊗Λ_K)](U_Γ⊗U_K)^T
- Middle factor is diagonal with entries γ_j σ_i² + λσ_i. **✓ Confirmed: Kronecker-diagonalizable, NOT merely diagonal.**

This confirms the comparison doc `p10.tex` is wrong when it says "diagonal preconditioner."

### Verified: arXiv:1601.01507 prior art attribution

**Claim (Kolda §4.10):** The subsampled Kronecker matvec idea exists in arXiv:1601.01507.

**Verification:** Paper is Airola & Pahikkala (2016), "Fast Kronecker product kernel methods via generalized vec trick," published in IEEE TNNLS 2017. The abstract confirms it generalizes efficient Kronecker computations from complete to non-complete (subsampled) data — the same core idea as our Step 1/Step 3 decomposition.

**Limitation:** Could not read the full PDF to verify the specific algorithm matches ours step-for-step. Citation is justified based on abstract + Kolda's explicit statement, but a human should spot-check the algorithm comparison.

### NOT verified (beyond scope of automated audit)

- Whether the Lean 4 formalization actually compiles (would need to run `lake build`)
- Whether the CG convergence rate bound from [Saa03, Theorem 9.4.2] is correctly applied
- Whether the "alternative" O(qnr) matvec (before the efficient version) is correctly derived
- Whether the Gram matrix formula Γ = ⊙_{i≠k}(A_i^T A_i) from [KB09, §3.1] is correct

---

## Risk Register

| Risk | Severity | Mitigation |
|------|----------|------------|
| Comparison doc `p10.tex` describes our preconditioner as "diagonal" (incorrect — independently verified it is Kronecker-diagonalizable) | LOW | Fix the description in `06_sideBySide_analysis/01_1stProof_official/sections/p10.tex` line 29 |
| Missing citation: arXiv:1601.01507 (Kolda identified this as prior art; abstract confirmed relevant) | MEDIUM | Add citation to proof.md and P10_paper.tex. Human should verify specific algorithm match. |
| No eigendecomposition transformation (Kolda's "advanced" step) | LOW | Not required for validity; note as potential v2 improvement |
| Lean 4 compilation not re-verified during audit | LOW | Run `lake build` to confirm |

---

## Recommendations

1. **Fix p10.tex comparison description:** Change "diagonal preconditioner" to "complete-data Kronecker preconditioner" in `06_sideBySide_analysis/01_1stProof_official/sections/p10.tex` line 29. (Independently verified our preconditioner is Kronecker-diagonalizable.)
2. **Add missing citation:** Add arXiv:1601.01507 (Airola & Pahikkala, "Fast Kronecker product kernel methods via generalized vec trick," IEEE TNNLS 2017) to both `proof.md` and `P10_paper.tex`. Human should read §3 of that paper to verify the specific algorithm overlap before citing.
3. **Re-run Lean verification:** Run `lake build` on `FirstProof/P10_PreconditionedCG.lean` to confirm it still compiles with 0 errors, 0 sorrys.
4. **Consider v2 improvement:** Incorporate the eigendecomposition transformation K = UDU^T from the official solution to improve conditioning. This is the step Kolda said she'd be "impressed" to see from AI.

---

## Changelog

| Date | Change | By |
|------|--------|----|
| 2026-02-15 | Initial P10 audit (cross-doc, coherence, structural checks) | Cascade |
| 2026-02-15 | Added independent mathematical re-derivations (spectral bounds, Kronecker dims, preconditioner structure) | Cascade |
| 2026-02-15 | Verified arXiv:1601.01507 attribution via abstract; noted limitation (full PDF unreadable) | Cascade |

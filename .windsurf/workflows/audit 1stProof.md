---
description: Audit consistency of all proof documents, papers, and comparison files
---

<!-- 
  AUDIT STRUCTURE:
    Part A (Steps 1-9):   Cross-document consistency
    Part B (Steps 10-14): Internal proof coherence  
    Part C (Steps 15-22): Structural & mathematical verification
    Step 23:              Generate formal audit report
    
  ORIGIN: Part B added after P01 failure — Gubinelli found Section 7 correctly stated
  the variance of :u³: diverges while Section 6 claimed :u³: is O(1).
  Part C added to catch the broader class of AI proof failure modes identified in
  the official commentary (FirstProofSolutionsCommentsPDF.md §4).
-->

# First Proof Audit Workflow

Run this workflow to perform a comprehensive audit of all proof documents.
The audit produces a formal report saved to `06_sideBySide_analysis/audit_report.md`.

**Before starting:** Read `01_problems/FirstProofSolutionsCommentsPDF.md` §4 (lines 235–391)
to understand the expert-flagged failure modes for each problem.

---

# Part A: Cross-Document Consistency

## 1. Check v1/ snapshots exist

Verify that `v1/` frozen originals exist for all 10 problems in both `02_proofs/` and `04_papers/`.

```
ls 02_proofs/*/v1/proof.md
ls 04_papers/v1/P*.tex
```

// turbo

## 2. Check for uncommitted changes

```
git status --short
```

// turbo

## 3. Verify P01–P10 status consistency across comparison documents

Read the results table from each of these files and confirm the P01–P10 proof statuses match:

- `01_problems/comparison_with_official_solutions.md` — main results table (§3)
- `06_sideBySide_analysis/01_1stProof_official/comparison_paper.tex` — Table 1
- `06_sideBySide_analysis/02_OpenAI/three_way_comparison.tex` — Table 1 ("Our answer / proof" column)
- `06_sideBySide_analysis/02_OpenAI/three_way_comparison.md` — §3.1 table

For each problem, verify:
- Answer match column is consistent
- Proof status column is consistent
- Any expert feedback (Hairer, Gubinelli, Liu, Kolda, etc.) is reflected in ALL documents

## 4. Verify aggregate counts

Check that the following counts are consistent across all documents:
- Complete proofs: should be **5/10** (P02, P03, P05, P08, P09)
- Valid approach: **1/10** (P10)
- Correct answer, incorrect proof: **1/10** (P01)
- Incomplete: **2/10** (P04, P06)
- Wrong case / divergent: **1/10** (P07)

Search for stale counts:

```
grep -rn "6/10\|6 of ten\|six of ten" 01_problems/ 06_sideBySide_analysis/ --include="*.md" --include="*.tex"
```

// turbo

## 5. Verify PDFs are up to date

Check that `.pdf` files are newer than their `.tex` sources:

```
for tex in 06_sideBySide_analysis/01_1stProof_official/comparison_paper.tex 06_sideBySide_analysis/02_OpenAI/three_way_comparison.tex; do
  pdf="${tex%.tex}.pdf"
  if [ "$tex" -nt "$pdf" ]; then
    echo "STALE PDF: $pdf is older than $tex"
  else
    echo "OK: $pdf is up to date"
  fi
done
```

// turbo

## 6. Check for stale P01 status

P01 is the most-edited section. Verify no stale "Complete" status remains:

```
grep -rn "P01.*Complete\|complete proofs for P01\|Φ⁴₃.*Complete" 01_problems/ 06_sideBySide_analysis/ --include="*.md" --include="*.tex"
```

// turbo

## 7. Verify expert feedback is present in all documents

Check that Hairer and Gubinelli feedback appears in all P01 sections:

```
grep -l "Hairer.*incorrect\|cargo.cult\|Gubinelli" 01_problems/comparison_with_official_solutions.md 06_sideBySide_analysis/01_1stProof_official/sections/p01.tex 06_sideBySide_analysis/02_OpenAI/three_way_comparison.tex 06_sideBySide_analysis/02_OpenAI/three_way_comparison.md
```

// turbo

All 4 files should appear. If any are missing, the feedback has not been propagated.

## 8. Check v1/ originals are unchanged

Verify that `v1/` snapshots have not been accidentally modified:

```
for dir in 02_proofs/*/; do
  for f in "${dir}v1/"*.md; do
    base=$(basename "$f")
    if ! diff -q "$f" "${dir}${base}" > /dev/null 2>&1; then
      echo "DIVERGED: $f vs ${dir}${base} (expected if updates were made)"
    else
      echo "UNCHANGED: ${dir}${base}"
    fi
  done
done
```

## 9. Proof-vs-Paper consistency

For each problem, compare the theorem statement and key claims between the raw proof
(`02_proofs/XX/proof.md`) and the polished paper (`04_papers/PXX_paper.tex`).

For each problem:
1. Read the main theorem statement from both files
2. Check: are they identical in substance? (Wording may differ, but mathematical content must match)
3. Check: does the paper claim anything stronger or weaker than the proof?
4. Flag any discrepancies

---

# Part B: Internal Proof Coherence

These checks detect contradictions WITHIN a single proof — the failure mode Gubinelli caught in P01,
where the AI generated both a correct fact and an incorrect claim in different sections without
noticing the contradiction.

For each proof, check for:
1. **Self-contradictions**: Does any later section contradict an earlier claim?
2. **Unsupported key claims**: Is any critical step asserted without proof or citation?
3. **Cargo-cult patterns**: Are specific technical choices (formulas, parameters) treated as essential
   when they may be convenience choices? (The P01 pattern: treating ε_n = exp(-e^n) as essential.)
4. **Regularity mismatches**: Are objects claimed to have regularity properties inconsistent with
   their definition? (The P01 pattern: claiming a distribution is O(1).)

## 10. Per-proof coherence check

For each proof file in `02_proofs/*/proof.md`, read the full proof and perform the checks above.
Do ONE problem at a time, starting with the highest-risk problems.

**Priority order** (based on expert flags from `01_problems/FirstProofSolutionsCommentsPDF.md` §4):

### 10a. P08 (HIGH — Abouzaid §4.8)
Abouzaid found that ALL LLM proofs failed on edge-vertex compatibility in the global gluing step.
Specific errors: (1) asserting disjoint neighborhoods of edges and vertices, (2) local vertex moves
invalidating edge geometry.

Read `02_proofs/08_symplectic_lagrangian_smoothing/proof.md` and check:
- Does Step 4 (Global Assembly / Proposition 2) properly justify that vertex and edge smoothings
  are compatible in their overlap regions?
- Does the proof assert disjoint neighborhoods without justification?
- Does the generating function framework actually avoid the coordinate compatibility issue,
  or does it just hide it?
- Are the different cotangent bundle identifications (T*Π₀^(v) vs T*Π₀^(e)) reconciled?

### 10b. P02 (MEDIUM — Nelson §4.2)
Nelson found LLMs used a false "Howe-vector existence result" with wrong support conditions
that contradict the central character.

Read `02_proofs/02_representation_rankin_selberg/proof.md` and check:
- Does our proof use Howe vectors? If so, does it claim support properties that contradict
  the central character?
- Our proof uses JPSS nondegeneracy + inertial class counting — verify this is genuinely
  independent of the Howe vector approach.

### 10c. P05 (LOW — Blumberg §4.5)
Blumberg found LLMs were "breezy about what is required" in the O-stable category and
used "geometric objects" without defining them. Also: hallucinated citations.

Read `02_proofs/05_topology_slice_filtration/proof.md` and check:
- Are all terms defined before use?
- Are all cited lemmas real? (Check for hallucinated references.)
- Does the Lean 4 formalization (0 sorry) cover the claims made in the proof?

### 10d. P07 (MEDIUM — Weinberger §4.7)
Weinberger flagged two false claims common in LLM proofs:
1. A false lemma about Lefschetz numbers (counterexample: R¹ with translation)
2. "Multiplicativity of Euler characteristic in finite covers" — false for infinite complexes

Read `02_proofs/07_lattices_acyclicity/proof.md` and check:
- Does our proof use any Lefschetz number argument? (Should be NO.)
- Does our Euler characteristic argument (Step 2, Lemma 2) apply Wall's rational χ only to
  finite CW complexes? (Should be YES — Γ'\G/K is a closed manifold.)
- Weinberger says Fowler's theorem kills ALL proofs using finite complex + Poincaré duality.
  Does our δ≠0 case (Step 5) fall into this trap? (Should be: we correctly identify this as
  open, not claimed as proved.)

## 11. Regularity consistency check

For each proof, extract all claims about the regularity/boundedness/growth of mathematical objects
and verify they are mutually consistent. This is the specific check that would have caught the P01 error.

For each proof file:
1. List every claim of the form "X is O(...)" or "X is bounded" or "X converges" or "X diverges"
   or "X is in [some function space]"
2. Check: do any two claims about the same object contradict each other?
3. Check: are regularity claims consistent with the definition of the object?

## 12. Citation verification

For each proof, verify that:
- All cited theorems/lemmas exist in the referenced source
- No citations are hallucinated (Blumberg §4.5 found LLMs confabulating entire papers)
- Theorem statements match what the cited source actually proves

Spot-check at least 3 citations per proof by searching for the paper title or author.

## 13. Key claim dependency chain

For each proof, trace the logical dependency chain:
1. What is the main theorem?
2. What are the key lemmas it depends on?
3. For each key lemma: is it proved, cited, or asserted without proof?
4. If asserted: flag as potential cargo-cult claim (the P01 pattern)

## 14. Part B summary

For each problem, record:
- **Self-contradictions found**: list any
- **Unsupported key claims**: list any
- **Cargo-cult risk**: HIGH / MEDIUM / LOW
- **Regularity consistency**: PASS / FAIL
- **Citation verification**: PASS / FAIL / SPOT-CHECK-ONLY

---

# Part C: Structural & Mathematical Verification

These checks catch broader failure modes identified across all 10 expert commentaries.

## 15. Assumption audit (CRITICAL)

**Why:** AI proofs often silently solve a different or weaker problem than the one stated.
Nelson (§4.2) caught LLMs constructing W depending on π (wrong — universality requires
independence). Williams (§4.3) caught LLMs changing the problem to a non-interpolation version.

For each problem:
1. Read the exact problem statement from `01_problems/` (or the original challenge)
2. Read the theorem statement in `02_proofs/XX/proof.md`
3. Check: does the proof solve the EXACT problem as stated?
4. Check: are any hypotheses added that aren't in the original problem?
5. Check: are any hypotheses dropped or weakened?
6. Flag any discrepancy as: WEAKER / STRONGER / DIFFERENT PROBLEM

## 16. "Too good to be true" check (CRITICAL)

**Why:** Srivastava (§4.4) noted the LLM "asserted that the proof can be finished via the
residue calculus without giving details." AI proofs often hand-wave at the hardest step.

For each proof:
1. Identify the single hardest step — the one that would take a human expert the most effort
2. Is this step fully proved with all details?
3. Does it contain any of these red-flag phrases?
   - "by standard arguments"
   - "it follows that"
   - "one can verify"
   - "a straightforward computation shows"
   - "it is well known that"
   - "the details are left to the reader"
4. If the hard step is hand-waved: flag as HIGH RISK

```
grep -rn "by standard\|it follows that\|one can verify\|straightforward\|well known\|left to the reader" 02_proofs/*/proof.md
```

// turbo

## 17. Hypothesis usage check

**Why:** Srivastava (§4.4) noted the LLM proof "does not exploit the fact that ⊞_n preserves
real roots, which must be used since the inequality is not true for arbitrary polynomials."
If a proof never uses a key hypothesis, either the result is more general (good) or the proof
is wrong (bad).

For each proof:
1. List all hypotheses of the main theorem
2. For each hypothesis: where in the proof is it used?
3. If a hypothesis is NEVER used: flag as SUSPICIOUS
   - If the result is known to be false without that hypothesis: flag as LIKELY FLAWED

## 18. Converse/contrapositive confusion check

**Why:** Weinberger (§4.7) found a false lemma where the direction of implication was wrong.
AI systems sometimes prove the converse of what's needed.

For each key lemma in each proof:
1. What does the lemma claim? (A ⟹ B)
2. How is the lemma used in the main proof? (Does it need A ⟹ B or B ⟹ A?)
3. Does the proof of the lemma actually establish the correct direction?

## 19. Local-to-global compatibility check

**Why:** Abouzaid (§4.8) found that LLM proofs fail on compatibility of local choices.
This is a general pattern: AI proofs make local constructions without checking global consistency.

For each proof that involves local-to-global assembly (especially P05, P08):
1. What local choices are made? (e.g., coordinate charts, base planes, generating functions)
2. How many degrees of freedom do these choices have?
3. Does the proof verify compatibility on ALL overlaps?
4. Are transition maps explicitly constructed or just asserted to exist?

## 20. Cross-proof consistency check

**Why:** The 10 proofs were written across different sessions with different AI models.
Shared mathematical objects should be used consistently.

Check:
- Do P04 and P07 both reference L²-Betti numbers? If so, are definitions consistent?
- Do P01 and P05 both reference spectral sequences? If so, are conventions consistent?
- Are there any shared references cited in multiple proofs with conflicting theorem statements?

## 21. Numerical verification audit

**Why:** We ran 900k+ numerical tests for P04 and extensive tests for P06. Numerical tests
can miss edge cases.

For proofs with numerical verification (P04, P06):
1. Do the test parameters cover the boundary of the domain?
2. Are degenerate cases tested? (e.g., n=1, ε→0, empty graphs)
3. Is the numerical tolerance appropriate for the claim?
4. Could floating-point errors mask a counterexample?

## 22. Cross-field creativity audit

**Why:** Cross-field tool discovery is the #1 failure mode we identified. P04 required hyperbolic
polynomial theory from real algebraic geometry applied to information theory. P06 required BSS
barrier functions from spectral sparsification. P07 required surgery theory with symmetric
signatures and the Novikov conjecture. In each case, the AI stayed within the "home field" of
the problem and never found the cross-field tool that unlocked the solution.

For each problem:
1. **What field does the problem live in?** (e.g., P04: finite free probability / information theory)
2. **What field does the official solution draw from?** (e.g., P04: real algebraic geometry —
   Bauschke–Güler–Lewis–Sendov theorem on hyperbolic polynomial convexity)
3. **Did our proof attempt any cross-field exploration?** Check the proof and transcript for:
   - References to papers/tools outside the problem's home field
   - Explicit statements like "we considered X but it didn't apply"
   - Evidence of searching for connections to other areas
4. **Did our proof stay entirely within one field?** If YES: flag as SINGLE-FIELD
5. **Was the cross-field insight findable?** Could the AI have reasonably discovered it by:
   - Following citation chains from the problem statement
   - Searching for the key mathematical objects in other contexts
   - Recognizing structural analogies (e.g., "this looks like a convexity problem")

**Known cross-field gaps** (from official commentary):

| Problem | Home Field | Cross-Field Tool (Official) | Our Approach | Gap? |
|---------|-----------|---------------------------|-------------|------|
| P01 | Stochastic PDE / Φ⁴₃ | (same field — regularity theory) | Cargo-cult reproduction | YES — regularity blindness |
| P02 | Automorphic forms | (same field — Godement-Jacquet) | JPSS + inertial classes | NO — valid alternative |
| P03 | Combinatorics / Macdonald | (same field — multiline queues) | Hecke recursion | NO — valid alternative |
| P04 | Finite free probability | Real algebraic geometry (hyperbolic polynomials) | Cumulant decomposition | YES — never found BGLS |
| P05 | Equivariant homotopy | (same field — Hill-Yarnall) | Same approach | NO |
| P06 | Spectral graph theory | Spectral sparsification (BSS barriers) | Multi-bin greedy | YES — never found BSS |
| P07 | Lattice topology | Surgery theory (symmetric signatures, Novikov) | Euler characteristic only | YES — never found surgery |
| P08 | Symplectic geometry | (same field — conormal fibrations) | Generating functions | PARTIAL — different but valid |
| P09 | Algebraic geometry / tensors | (same field — flattenings) | Plücker equations | NO — valid alternative |
| P10 | Numerical linear algebra | (same field — Kronecker structure) | Subsampled Kronecker | NO |

For each problem, assess:
- **Cross-field creativity**: HIGH (explored multiple fields) / MEDIUM (some exploration) / LOW (stayed in home field)
- **Cross-field necessity**: Was a cross-field insight REQUIRED for a complete proof, or was an
  in-field approach sufficient?
- **Discovery pathway**: If a cross-field tool was needed, what search strategy could have found it?

## 23. Part C summary

For each problem, record:
- **Assumption match**: EXACT / WEAKER / STRONGER / DIFFERENT
- **Hard step status**: FULLY PROVED / HAND-WAVED / CITED
- **Hypothesis usage**: ALL USED / UNUSED: [list]
- **Direction of proof**: CORRECT / SUSPICIOUS
- **Local-global compatibility**: N/A / VERIFIED / ASSERTED
- **Numerical verification**: N/A / ADEQUATE / GAPS: [list]
- **Cross-field creativity**: HIGH / MEDIUM / LOW
- **Cross-field necessity**: REQUIRED / HELPFUL / NOT NEEDED

---

# Step 24: Generate Audit Report

After completing all checks, create a formal audit report at:
`06_sideBySide_analysis/audit_report.md`

The report MUST follow this exact template:

```markdown
# First Proof Audit Report

**Date:** [date]
**Auditor:** Cascade AI (orchestrated by Mark Dillerop)
**Scope:** All 10 First Proof submissions — proofs, papers, and comparison documents

---

## Executive Summary

- **Documents audited:** [count]
- **Cross-document inconsistencies found:** [count]
- **Internal contradictions found:** [count]
- **Expert-flagged vulnerabilities confirmed:** [count]
- **Overall assessment:** [summary sentence]

---

## Part A: Cross-Document Consistency

| Check | Status | Details |
|-------|--------|---------|
| v1/ snapshots | PASS/FAIL | |
| Uncommitted changes | PASS/FAIL | |
| Status table consistency | PASS/FAIL | |
| Aggregate counts | PASS/FAIL | |
| PDFs up to date | PASS/FAIL | |
| P01 stale status | PASS/FAIL | |
| Expert feedback propagation | PASS/FAIL | |
| v1/ originals unchanged | PASS/FAIL | |
| Proof-vs-paper consistency | PASS/FAIL | |

---

## Part B: Internal Proof Coherence

| Problem | Self-Contradictions | Unsupported Claims | Cargo-Cult Risk | Regularity | Citations |
|---------|--------------------|--------------------|-----------------|------------|-----------|
| P01 | [list or NONE] | [list or NONE] | HIGH/MED/LOW | PASS/FAIL | PASS/FAIL |
| P02 | | | | | |
| ... | | | | | |
| P10 | | | | | |

---

## Part C: Structural Verification

| Problem | Assumption Match | Hard Step | Hypotheses Used | Direction | Local-Global | Numerical | Cross-Field |
|---------|-----------------|-----------|-----------------|-----------|-------------|-----------|-------------|
| P01 | EXACT/WEAKER/... | PROVED/WAVED | ALL/UNUSED:... | OK/SUSP | N/A/OK/... | N/A/OK/... | LOW/MED/HIGH |
| P02 | | | | | | | |
| ... | | | | | | | |
| P10 | | | | | | | |

---

## Per-Problem Detail

### P01: Φ⁴₃ Measure Shift
- **Current status:** Correct answer, incorrect proof
- **Expert feedback:** Hairer (regularity error), Gubinelli (wrong mechanism, self-contradiction, cargo-cult)
- **Audit findings:** [detailed findings]
- **Cross-field analysis:**
  - Home field: [field]
  - Official solution field: [field]
  - Our approach field: [field]
  - Cross-field exploration attempted: YES/NO — [details]
  - Cross-field insight required: YES/NO
  - Discovery pathway (if missed): [how could the AI have found it?]
- **Recommendation:** [SAFE / NEEDS EXPERT REVIEW / LIKELY FLAWED]

### P02: Rankin–Selberg
[repeat for each problem, including cross-field analysis]

...

### P10: CP-RKHS PCG
[repeat for each problem, including cross-field analysis]

---

## Cross-Field Discovery Summary

This section summarizes the AI's ability to find tools from adjacent mathematical fields.

| Problem | Home Field | Tool Needed From | Found? | Proof Complete? |
|---------|-----------|-----------------|--------|----------------|
| P01 | Stochastic PDE | (same — regularity) | NO | NO |
| P02 | Automorphic forms | (same) | YES | YES |
| P03 | Combinatorics | (same) | YES | YES |
| P04 | Finite free probability | Real algebraic geometry | NO | NO |
| P05 | Equivariant homotopy | (same) | YES | YES |
| P06 | Spectral graph theory | Spectral sparsification | NO | NO |
| P07 | Lattice topology | Surgery theory | NO | NO |
| P08 | Symplectic geometry | (same) | YES | YES |
| P09 | Algebraic geometry | (same) | YES | YES |
| P10 | Numerical linear algebra | (same) | YES | YES |

**Pattern:** [Summarize — e.g., "All 4 incomplete/incorrect proofs required cross-field insights
that the AI failed to discover. All 6 complete proofs used tools from the problem's home field."]

**Implication for v2 updates:** [Which proofs could be improved by incorporating cross-field tools?
What search strategies should be tried?]

---

## Risk Register

| Risk | Problem(s) | Severity | Mitigation |
|------|-----------|----------|------------|
| [description] | P0X | HIGH/MED/LOW | [action needed] |

---

## Recommendations

1. [Numbered list of concrete actions]

---

## Changelog

| Date | Change | By |
|------|--------|----|
| [date] | Initial audit | Cascade |
```

Save this report to `06_sideBySide_analysis/audit_report.md`.
If the file already exists, update it rather than overwriting — append a new entry to the Changelog.

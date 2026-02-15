---
description: Audit consistency of all proof documents, papers, and comparison files
---

# Audit Workflow

Run this workflow to check that all documents across the First Proof project are internally consistent and up to date.

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

## 6. Check for internal contradictions in P01

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

## 9. Summary

Report:
- Number of problems with v1/ snapshots
- Number of uncommitted changes
- Any stale PDFs
- Any inconsistent statuses across documents
- Any missing expert feedback propagation
- Which proofs have diverged from their v1/ originals (i.e., have been updated)

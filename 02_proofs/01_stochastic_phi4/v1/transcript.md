# Problem 1 — AI Interaction Transcript

## Session Log

*Record of AI interactions for this problem, as requested by the 1st Proof organizers.*

---

### Session 1 — 2025-02-10 (Cascade)

**Goal:** Kickoff for P01. Populate references, develop approach, begin proof draft.

**Key discovery:** The initial kickoff document hypothesized the answer is YES (equivalence). Web research revealed this is **wrong** — the answer is **NO** (mutual singularity).

**Evidence:**
1. **Hairer's 2022 note** "Φ⁴₃ is orthogonal to GFF" (hairer.org/Phi4.pdf) proves Φ⁴₃ ⊥ GFF and also implies singularity under smooth shifts.
2. **Hairer-Kusuoka-Nagoji (arXiv:2409.10037)** "Singularity of solutions to singular SPDEs" — the formal paper version, published September 2024.
3. **MathOverflow Q481553** — Hairer comments (Dec 5, 2024): "The argument given there should work up to shifts in $C^{1,\alpha}$ for some (arbitrary) $\alpha > 0$."
4. **MathOverflow Q485884** — Hairer answers (Jan 12, 2026) explaining the proof mechanism: the separating set is $A_\psi = \{\Phi : \lim_{n\to\infty} e^{-3n/4}\langle \Phi_n^3 - 3ae^{e^n}\Phi_n - 9be^n\Phi, \psi\rangle = 0\}$. Under GFF, the Wick cube vanishes after scaling but the $9be^n\Phi$ term gives divergent $e^{n/4}\langle\Phi,\psi\rangle$.

**Proof strategy for the shift question ($\mu \perp T_\psi^* \mu$):**
- Use Hairer's set $A_\psi$ (with test function = shift function $\psi$).
- $\mu(A_\psi) = 1$ by Hairer-Kusuoka-Nagoji.
- $(T_\psi^* \mu)(A_\psi) = 0$: Under the shifted measure, $\Phi = \tilde{\Phi} + \psi$ with $\tilde{\Phi} \sim \mu$. The functional acquires an additional deterministic divergent term $-9be^{n/4}\|\psi\|_{L^2}^2 \to -\infty$, while all other terms are controlled.

**Files updated:**
- `references.md` — 18 references including the key paper arXiv:2409.10037
- `approach.md` — Full approach with answer NO, Hairer's construction, detailed proof strategy
- `proof.md` — Draft proof in two parts (Part A: $\mu \perp \mu_0$ via Hairer; Part B: $\mu \perp T_\psi^*\mu$ via shift computation)
- `transcript.md` — This log

**Remaining work:**
1. Verify growth rate estimates for cross terms in Part B (need moment bounds on $\tilde{\Phi}_n^2$ under $\mu$)
2. Determine if citing arXiv:2409.10037 suffices or if a self-contained argument is needed
3. Clean up the proof draft (currently contains working/scratch computations)
4. Consider Lean formalization (likely limited to abstract measure-theoretic shell)

---

### Session 2 — 2025-02-10 (Cascade)

**Goal:** Address three remaining items from Session 1.

**Task 1: Sharpen the variance estimate — RESOLVED**

The previous proof had an imprecise "UV matching" claim: that the two-point function of $\Phi_n^2$ under $\mu$ matches the GFF at leading order. This was replaced with a rigorous argument using the **Barashkov-Gubinelli decomposition** (arXiv:2004.01513, Theorem 1.1):

- Under $\mu$, the field decomposes as $\Phi = Z + v^*$ where $Z$ is a genuine GFF and $v^* \in C^{1/2-\kappa}$ is a smoother random drift.
- The Wick square term $\langle \psi_n :\!Z_n^2\!:, \psi\rangle$ is a purely Gaussian computation (involves only $Z$, not $v^*$).
- Its variance $\geq c \cdot e^{e^n}$ diverges super-exponentially.
- The drift $v^*$ contributes only lower-order terms ($v^*_n$ is bounded since $v^* \in C^{1/2-\kappa}$).
- The Girsanov density relating $\text{Law}(Z+v^*)$ to $\mu$ is a.s. positive and finite, so probability-0/1 events are preserved.

This eliminates the need for any "UV matching" citation — the variance estimate is now self-contained.

**Task 2: Submission format — RESOLVED**

Read the 1st Proof rules at 1stproof.org. Key finding:
> "Citations should include precise statement numbers and should either be to articles published in peer-reviewed journals or to arXiv preprints."

Our proof cites:
1. arXiv:2409.10037, Theorem 1.1 (Hairer-Kusuoka-Nagoji) — for $\mu(A_\psi) = 1$
2. arXiv:2004.01513, Theorem 1.1 (Barashkov-Gubinelli) — for the decomposition $\Phi = Z + v^*$

Both are valid citations per the rules. Part B is self-contained modulo these two theorems.

**Task 3: Lean formalization — COMPLETED**

Wrote `FirstProof/P01_StochasticPhi4.lean` with:
- Abstract `mutuallySingular_of_separating_set` theorem (the measure-theoretic shell)
- Axiomatized: `DistSpace`, `Phi43Measure`, `shiftMap`, `separatingSet`
- Axiomatized analytic inputs: `mu_separatingSet_compl` and `shifted_separatingSet`
- Derived: `phi43_shift_mutuallySingular` from the axioms

**Additional work:**
- Polished Part A of proof.md: removed working/scratch passages, presented clean version with correct super-exponential scaling from the start.
- Updated approach.md with submission format findings and Lean formalization status.

**Files updated:**
- `proof.md` — Polished Part A, rewrote Part B with Barashkov-Gubinelli decomposition, updated Summary/Status/Remaining Work
- `approach.md` — Added Submission Format and Lean Formalization sections
- `references.md` — No changes needed (already had all references)
- `transcript.md` — This log
- `FirstProof/P01_StochasticPhi4.lean` — Full Lean formalization of measure-theoretic shell

**Remaining work:**
1. Verify the Borel-Cantelli step in Part B (passage from non-convergence in probability to a.s. divergence)
2. Final polish of proof.md for submission quality

---

### Session 3 — 2025-02-10 (Cascade)

**Goal:** Close the Borel-Cantelli gap in Part B.

**Diagnosis of the gap:**
The previous proof said "Borel-Cantelli gives $\limsup |F_n| = \infty$ a.s." without justification. Two issues:
1. Non-convergence in probability ≠ a.s. non-convergence
2. Second Borel-Cantelli requires independence; first Borel-Cantelli requires summability

**Four options considered:**
- **Option A (chosen):** Carbery-Wright anti-concentration + first BC lemma. Clean, rigorous, adds one peer-reviewed citation.
- **Option B:** Conditional on $v^*$, same summability needed.
- **Option C:** Use deterministic term $-9be^{n/4}\|\psi\|^2$ directly — but $X_n$ dominates it, same issue.
- **Option D:** Weaken conclusion — same summability needed anyway.

**Implementation (Option A):**
1. $X_n = 3e^{-3n/4}\langle \psi_n :\!Z_n^2\!:, \psi\rangle$ is a degree-2 polynomial in Gaussians.
2. Carbery-Wright (JAMS 2001, Thm 8): $\mathbb{P}(|X_n| \leq t) \leq C_2(t/\sigma_n)^{1/2}$.
3. If $|F_n(\tilde{\Phi}+\psi)| \leq 1$, then $|X_n| \leq t_n := 2 + 9b\|\psi\|^2 e^{n/4}$.
4. $\mathbb{P}(|X_n| \leq t_n) \leq C' \exp(-e^n/4 + n/2)$ — super-exponentially summable.
5. First BC lemma: $|X_n| > t_n$ eventually a.s., so $|F_n| > 1$ eventually a.s.

**Files updated:**
- `proof.md` — Rewrote "Completing the argument" with rigorous 4-step Carbery-Wright + BC proof; updated Key Citations and Remaining Work
- `references.md` — Added Carbery-Wright (ref 15), renumbered subsequent entries (now 19 total)
- `transcript.md` — This log

**Status:** The proof is now **mathematically complete**. All gaps closed. Remaining work is editorial only.

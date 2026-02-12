# Problem 2 — AI Interaction Transcript

## Session Log

*Record of AI interactions for this problem, as requested by the 1st Proof organizers.*

### Session 1 — 2025-02-10

**Goal:** Initial attack on P02 (Rankin–Selberg universal test vectors).

**Work completed:**

1. **References populated** — 17 key references organized by topic: core Rankin–Selberg theory (JPSS), Whittaker/Kirillov models and newforms (Casselman–Shalika, BZ, Popa), Nelson's subconvexity program, and additional relevant papers.

2. **$n = 1$ case solved** — Worked out $\mathrm{GL}_2 \times \mathrm{GL}_1$ explicitly:
   - The $u_Q$-twist reduces to an additive character twist $\psi^{-1}(Q g_{nn})$ (Lemma 1).
   - Choosing $\phi = \mathbf{1}_{\mathfrak{o}^\times}$ in the Kirillov model makes the integral a Gauss sum, independent of $s$.
   - Gauss sum nonvanishing gives the result for all characters $\chi$.

3. **General proof developed** — Three-part argument for arbitrary $n$:
   - **Part I (Algebraic):** $u_Q$-twist formula: $W(\mathrm{diag}(g,1) u_Q) = \psi^{-1}(Qg_{nn}) W(\mathrm{diag}(g,1))$.
   - **Part II (Analytic):** Choose $W$ with Kirillov function supported on a single $N_n$-double coset $N_n \varpi^{-N} K_n$. This makes $\Psi(s) = q^{nN(s-1/2)} \cdot C$, a monomial in $q^{-s}$.
   - **Part III (Representation-theoretic):** The constant $C = \ell(V)$ is nonzero for some $V$ by the JPSS nondegeneracy of the Rankin–Selberg pairing.

4. **Approach document developed** — Detailed strategy with the $n=1$ warmup, general strategy via Kirillov model, and key structural insights about the $u_Q$ translation.

**Key insight:** The $u_Q$ translation is equivalent to inserting an additive character twist $\psi^{-1}(Qg_{nn})$. Choosing $W$ with single-determinant-level Kirillov support eliminates the $s$-dependence entirely, reducing the problem to a nonvanishing statement that follows from JPSS.

**Identified gap:** The proof of Lemma 2 (nonvanishing for fixed $W'$) relies on the nondegeneracy of the Rankin–Selberg pairing for a fixed first argument. This is a standard but nontrivial consequence of JPSS theory. A fully self-contained proof would need to verify this more carefully, possibly using the multiplicity-one theorem for $\mathrm{GL}_{n+1} \times \mathrm{GL}_n$.

**Status:** Proof draft complete with one identified gap (Section 4.4). The answer is YES.

### Session 2 — 2025-02-10 (continued)

**Goal:** Close the gap in Lemma 2 (nonvanishing for fixed $W'$) and consolidate the proof.

**Work completed:**

1. **Explored multiple approaches to Lemma 2:**
   - **Frobenius reciprocity:** Pairing $\langle \Phi', V \rangle$ factors through $T: \mathrm{c\text{-}ind}_{N_n}^{\mathrm{GL}_n}(\psi^{-1}) \to \tilde{\pi}$ (Whittaker quotient). Nonvanishing iff $\Phi' \notin \ker T$.
   - **Multiplicity one (AGRS):** $\dim \mathrm{Hom}_{\mathrm{GL}_n}(\Pi|_{\mathrm{GL}_n} \otimes \pi, \mathbb{C}) \leq 1$ gives uniqueness of the RS bilinear form. Kernel is $\mathrm{GL}_n$-invariant but not $\mathrm{GL}_{n+1}$-invariant.
   - **$K_n$-representation theory (self-contained):** Reduced to finite-dimensional linear algebra — evaluation image $\mathcal{E}$ cannot lie in hyperplane $H$ because $K_n$-translates of the defining functional span the full dual.

2. **Consolidated proof of Lemma 2** with two clean arguments:
   - Argument 1 via Frobenius reciprocity (conceptual)
   - Argument 2 via $K_n$-representation theory (self-contained, elementary)

3. **Cleaned up proof.md** — removed exploratory dead ends, kept only the strongest arguments. Final structure:
   - Part I: $u_Q$-twist formula (Lemma 1)
   - Part II: $n=1$ case via Gauss sums
   - Part III: General case (Sections 3.1–3.7)
   - Part IV: Verification and remarks

**Key technical insight for Lemma 2:** The evaluation image $\mathcal{E} = \{(V(\varpi^{-N}\bar{k}))_{\bar{k}}\}$ is $K_n$-stable and nonzero. The hyperplane $H$ defined by $f(\bar{k}) = \psi^{-1}(\varpi^{-(c+N)}\bar{k}_{nn})$ is NOT $K_n$-stable (right translates introduce dependence on other matrix entries). So $\bigcap_h R(h)H = \{0\}$, forcing $\mathcal{E} \not\subset H$.

**Remaining concerns:**
- Step 3 of Argument 2 (translates span the full dual) needs verification that the $K_n$-orbit of $f$ truly generates all of $(\mathbb{C}^{K_n/K_1(\mathfrak{p}^M)})^*$. This is plausible but not fully rigorous — it relies on the claim that elementary matrix translates spread dependence to all entries.
- The proof is strongest for the $n=1$ case (fully rigorous via Gauss sums). For general $n$, the argument is convincing but has this one soft spot.

**Status:** Proof draft substantially complete. Answer is **YES**. The gap in Lemma 2 has been addressed with two complementary arguments, though the self-contained argument (Argument 2) could benefit from a more detailed verification of Step 3.

### Session 3 — 2025-02-11

**Goal:** Harden the proof — close all identified gaps, verify all matrix computations, make every step rigorous.

**Work completed:**

1. **Argument 1 of Lemma 2 completely rewritten** — now a self-contained, rigorous proof:
   - Step 1: Left radical $\mathrm{Rad}_L$ of the RS bilinear form is $\mathrm{GL}_n$-stable (proved via substitution $g \mapsto gh^{-1}$).
   - Step 2: $\mathrm{Rad}_L$ is proper (by JPSS).
   - Step 3: $W^Q \notin \mathrm{Rad}_L$ — proved via BZ filtration layer analysis. Key insight: $\Phi' = \psi^{-1}(Qg_{nn})\Phi_0$ is supported on the open double coset $N_n\varpi^{-N}K_n$ (top BZ layer), and the Whittaker quotient $T$ is injective on this layer, so $\Phi' \notin \ker T$.

2. **Argument 2 of Lemma 2 corrected** — identified and fixed a critical error:
   - **Bug found:** Step 4 claimed right multiplication by permutation matrices permutes rows — WRONG, it permutes columns. The $K_n$-translates of $f$ only span functions of the $n$-th row, not all functions on $S$.
   - **Fix:** Steps 1–3 (Fourier analysis on the $n$-th row) are fully rigorous and give the marginal vanishing constraint ($*$). Step 4 now honestly defers to Argument 1's BZ layer analysis for the final step.
   - **Special case $n=1$:** Argument 2 is fully self-contained (the $n$-th row IS the full matrix).

3. **§3.3 clarified** — clean statement that the monomial strategy eliminates the "$\forall s$" condition.

4. **§3.4 tightened** — precise BZ theorem citation ([BZ77, Theorem 5.21]), explicit description of the mirabolic subgroup $P_{n+1}$, and verification that $\Phi_0$ exists (open double coset + conductor compatibility).

5. **§3.5 expanded** — explicit verification of:
   - Well-definedness of $g_{nn}$ on $N_n \backslash \mathrm{GL}_n$ (upper-triangular unipotent preserves $(n,n)$-entry).
   - Iwasawa decomposition on the support: $\psi^{-1}(n)$ and $\psi(n)$ factors cancel, $g_{nn} = \varpi^{-N}k_{nn}$.

6. **Lemma 1 verified** — full matrix computation confirming the conjugation identity and that only the $(n, n+1)$ superdiagonal entry contributes to $\psi^{-1}$.

7. **§4.2 expanded** — explicit remark that $N \geq 0$ is unconstrained (BZ surjectivity works for any $N$, Fourier argument only needs $M \geq c+N$).

8. **§4.4 updated** — accurate description of both arguments' scope and relationship.

**Issues found and resolved:**
- **CRITICAL:** Argument 2, Step 4 had a row/column confusion with permutation matrices. Right multiplication permutes columns, not rows. Fixed by restructuring the argument.
- **MEDIUM:** Argument 1 was previously circular (deferred to Argument 2). Now self-contained via left-radical + BZ layer analysis.
- **LOW:** §3.3 had confused discussion of monomials vs Laurent polynomials. Cleaned up.

**Remaining concerns:** None identified. Argument 1 is the primary complete proof. Argument 2 provides complementary Fourier-analytic insight and is fully self-contained for $n = 1$.

**Status:** Proof hardened. Answer is **YES**. All identified gaps closed.

### Session 4 — 2025-02-11

**Goal:** Final review of proof.md — discovered and fixed a critical circularity in Argument 1.

**Critical issue found:** The previous Argument 1 (Session 3) claimed "$\Phi' \notin \ker T$" by appealing to the BZ filtration — specifically, that "$T$ is injective on the top BZ layer" and "$\ker T$ consists of functions on lower strata." This was **circular**: the map $T: \mathrm{c\text{-}ind}_{N_n}^{\mathrm{GL}_n}(\psi^{-1}) \to \tilde{\pi}$ has $\ker T = \mathrm{Rad}_L(\pi)$ (the left radical), and showing $\Phi' \notin \ker T$ is equivalent to the conclusion $\ell(V) \neq 0$ for some $V$. The BZ filtration of $\Pi|_{P_{n+1}}$ does NOT imply injectivity of $T$ on the top layer of $\mathrm{c\text{-}ind}$.

**Fix (complete rewrite of Argument 1):** Replaced with a clean existential argument:
1. $\mathrm{Rad}_L(\pi)$ is a proper subspace (by JPSS).
2. The bad locus $\mathcal{B}_\pi = \Pi(u_Q)^{-1} \mathrm{Rad}_L(\pi)$ is proper.
3. **Key new observation:** $\mathcal{B}_\pi$ depends only on the **inertial equivalence class** $[\pi]$ (orbit under unramified twists). Proof: unramified twist $\pi' = \pi \otimes |\det|^s$ gives $V'(g) = V(g)|\det g|^s$, so $\Psi_{\mathrm{std}}(s_0, W', V') = \Psi_{\mathrm{std}}(s_0+s, W', V)$, hence $\mathrm{Rad}_L(\pi') = \mathrm{Rad}_L(\pi)$. Also, conductor is unchanged by unramified twists.
4. The inertial classes are **countable** (discrete supercuspidal support data).
5. A $\mathbb{C}$-vector space $\neq$ countable union of proper subspaces.
6. **Subtlety:** the initial version incorrectly claimed the set of isomorphism classes is countable (it's not — continuous parameters make it uncountable). The inertial class reduction is essential.

**§3.7 universality argument also rewritten:**
- Need single-coset $W$ (for monomial structure) that avoids all $\mathcal{B}_{[\pi]}$.
- Define $\mathcal{S}_N$ = single-coset vectors supported on $N_n \varpi^{-N} K_n$ (infinite-dimensional).
- Show $\mathcal{S}_N \cap \mathcal{B}_{[\pi]}$ is proper for each $[\pi]$: if $\mathcal{S}_N \subset \mathcal{B}_{[\pi]}$, then $\ell_W(V) = 0$ for all smooth $\phi$ on $K_n$ and all $V$, forcing $V(\varpi^{-N} k) = 0$ for all $k$, contradicting Whittaker separation.
- Countable union of proper subspaces of $\mathcal{S}_N$ cannot exhaust $\mathcal{S}_N$.

**Other updates:**
- §4.4 notes updated to reflect final proof structure.
- Argument 2 unchanged (still provides Fourier reduction, self-contained for $n=1$).

**Status:** Proof complete. The circularity is fully resolved. Answer is **YES**.

### Session 5 — 2025-02-11

**Goal:** Address all 6 issues from Claude Opus 4.6 extended review.

**Review summary:** Opus confirmed the proof is mathematically sound. Argument 1 + §3.7 is a complete, correct proof. Six presentational issues identified.

**Fixes implemented:**

1. **Issue 1 (HIGH — missing problem statement):** Added full problem statement at the top of proof.md, including the definition of $u_Q := I_{n+1} + Q E_{n,n+1}$, the integral, and the universality requirement. Also added explicit note that $Q$ depends on $\pi$ through the conductor.

2. **Issue 2 (HIGH — §3.7 approximation argument):** Replaced informal "$\phi \to \delta_e$" with exact point evaluation: since $V(\varpi^{-N} k)$ and $\psi^{-1}(\varpi^{-(c+N)} k_{nn})$ are locally constant, there exists a congruence subgroup $K'$ making both right-$K'$-invariant. Taking $\Phi_W(\varpi^{-N} k) = \mathrm{vol}(K')^{-1} \cdot \mathbf{1}_{K'}(k)$ gives exact evaluation $\ell_W(V) = \psi^{-1}(\varpi^{-(c+N)}) V(\varpi^{-N})$.

3. **Issue 3 (MEDIUM — $\mathfrak{o}^\times$ spanning):** Added parenthetical: "$a$ ranges over $\mathfrak{o}^\times$, but $\mathfrak{o}^\times$ generates $\mathfrak{o}/\mathfrak{p}^M$ additively since $1 \in \mathfrak{o}^\times$ and $\mathfrak{o}^\times + \mathfrak{o}^\times = \mathfrak{o}$."

4. **Issue 4 (MEDIUM — Argument 2 labeling):** Relabeled as "supplementary; self-contained for $n = 1$, partial for $n \geq 2$."

5. **Issue 5 (MEDIUM — $Q$ depends on $\pi$):** Already addressed by the new problem statement (Issue 1).

6. **Issue 6 (LOW — countable union citation):** Added "[La02, Ch. III, Exercise 17]" citation and alternative Gaussian measure-zero argument. Added Lang's *Algebra* to references.md as reference 18.

**No mathematical changes.** All fixes are presentational.

**Status:** Proof at submission quality. Answer is **YES**.

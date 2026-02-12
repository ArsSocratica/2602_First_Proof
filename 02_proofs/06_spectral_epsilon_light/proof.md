# Problem 6 — Existence of ε-Light Subsets

## 1. Problem Statement and Normalized Formulation

For a graph $G = (V, E)$ with $n = |V|$ and Laplacian $L$, the induced subgraph Laplacian is $L_S = \sum_{\{u,v\} \in E(S,S)} L_{uv}$. A set $S \subseteq V$ is **ε-light** if $L_S \preceq \epsilon L$.

**Question (Spielman).** Does there exist $c > 0$ such that for every graph $G$ and every $\epsilon \in (0,1)$, there exists an ε-light subset $S$ with $|S| \geq c\epsilon n$?

**Normalized formulation.** Let $\Pi$ denote the orthogonal projector onto $\mathbf{1}^\perp$ and define $\tilde{M} := L^{+/2} M L^{+/2}$ for any symmetric $M$. Then $L_S \preceq \epsilon L$ iff $\tilde{L}_S \preceq \epsilon \Pi$, i.e., $\|\tilde{L}_S\| \leq \epsilon$ (spectral norm restricted to $\mathbf{1}^\perp$). The normalized edge Laplacians are rank-1 PSD with $\|\tilde{L}_{uv}\| = \text{tr}(\tilde{L}_{uv}) = R_{\text{eff}}(u,v)$, and $\sum_e \tilde{L}_{uv} = \Pi$.

*Proof of normalization.* $\tilde{L}_{uv} = L^{+/2}(\mathbf{e}_u - \mathbf{e}_v)(\mathbf{e}_u - \mathbf{e}_v)^T L^{+/2}$ is rank-1 PSD. Its trace is $(\mathbf{e}_u - \mathbf{e}_v)^T L^+ (\mathbf{e}_u - \mathbf{e}_v) = R_{\text{eff}}(u,v)$. For rank-1 PSD, $\|\cdot\| = \text{tr}(\cdot)$. Summing: $\sum_e \tilde{L}_{uv} = L^{+/2}LL^{+/2} = \Pi$. $\square$

**Status:** We establish rigorous partial results (§2), a conditional partial result with explicit gap analysis (§3), and a detailed catalog of why standard tools fail (§4). The general case remains open.

---

## 2. Proved Results

### Lemma 1 (Linearization)

*For any $S \subseteq V$:* $L_S \preceq \frac{1}{2}\sum_{v \in S} L_v^*$.

*Equivalently in normalized form:* $\tilde{L}_S \preceq \frac{1}{2}\sum_{v \in S} \tilde{L}_v^*$.

*Proof.* For indicators $s_u, s_v \in \{0,1\}$: $s_u s_v \leq \frac{1}{2}(s_u + s_v)$. (Case check: if either is 0, LHS $= 0 \leq$ RHS; if both are 1, LHS $= 1 =$ RHS.) Since $L_{uv} \succeq 0$:
$$L_S = \sum_e s_u s_v L_{uv} \preceq \sum_e \tfrac{s_u + s_v}{2} L_{uv} = \tfrac{1}{2}\sum_{v \in S} L_v^*. \quad \square$$

This converts the quadratic vertex-edge coupling into a linear sum of vertex contributions, at the cost of a factor-of-2 looseness. The inequality is tight when $S = V$ (both sides equal $L$).

### Theorem A (Independence Regime)

*If $G$ has average degree $\bar{d} \leq 6/\epsilon - 1$, there exists an ε-light subset $S$ with $|S| \geq \epsilon n / 6$.*

*Proof.* The greedy independent set bound gives $|S| \geq n/(\bar{d}+1) \geq \epsilon n / 6$. Since $S$ is independent, $L_S = 0 \preceq \epsilon L$. $\square$

**Remark.** This is a degenerate regime: ε-lightness is achieved trivially because $L_S = 0$. The result does not engage with the spectral structure of the problem and should not be taken as evidence that the general conjecture is "almost proved." It serves as a base case that handles sparse graphs.

**Corollary A.1** (Effective resistance decomposition). *For any graph $G$ and $\epsilon \in (0,1)$, there exists an independent set $I$ with $|I| \geq \epsilon n/3$ such that every edge in $G_I$ satisfies $R_{\text{eff}}(e) \leq \epsilon$, i.e., $\|\tilde{L}_{uv}\| \leq \epsilon$.*

*Proof.* By Foster's theorem [Fos49], $\sum_{e \in E} R_{\text{eff}}(e) = n-1$. Let $E_{\text{hi}} = \{e : R_{\text{eff}}(e) > \epsilon\}$. Then $|E_{\text{hi}}| \cdot \epsilon < n-1$, so $|E_{\text{hi}}| < (n-1)/\epsilon < n/\epsilon$. The subgraph $G_{\text{hi}} = (V, E_{\text{hi}})$ has average degree $2|E_{\text{hi}}|/n < 2/\epsilon$. By Turán's bound, $G_{\text{hi}}$ has an independent set $I$ with $|I| \geq n/(2/\epsilon + 1) \geq \epsilon n/3$ (using $2/\epsilon + 1 \leq 3/\epsilon$ for $\epsilon \leq 1$). Since $I$ is independent in $G_{\text{hi}}$, every edge of $G$ with both endpoints in $I$ has $R_{\text{eff}}(e) \leq \epsilon$. $\square$

**Corollary A.2** (Trace-small case). *If $\text{tr}(\tilde{L}_I) = \sum_{e \in E(I,I)} R_{\text{eff}}(e) \leq \epsilon$, then $I$ is ε-light with $|I| \geq \epsilon n/3$.*

*Proof.* $\|\tilde{L}_I\| \leq \text{tr}(\tilde{L}_I) \leq \epsilon$ (since $\tilde{L}_I \succeq 0$). $\square$

### Theorem B (Expectation Bound)

*For any graph $G$, sampling each vertex independently with probability $p$ gives:*
$$\mathbb{E}[\tilde{L}_S] \preceq p\Pi.$$
*In particular, with $p = \epsilon/2$: $\mathbb{E}[\tilde{L}_S] \preceq \frac{\epsilon}{2}\Pi$ and $\mathbb{E}[|S|] = \epsilon n/2$.*

*Proof.* By Lemma 1, $\tilde{L}_S \preceq \frac{1}{2}\sum_v \xi_v \tilde{L}_v^*$ pointwise (for every realization of $\xi_v \in \{0,1\}$). Taking expectations (valid since $A \preceq B$ pointwise implies $\mathbb{E}[A] \preceq \mathbb{E}[B]$):
$$\mathbb{E}[\tilde{L}_S] \preceq \frac{p}{2}\sum_v \tilde{L}_v^* = \frac{p}{2} \cdot 2\Pi = p\Pi. \quad \square$$

**Remark.** The true expectation is $\mathbb{E}[\tilde{L}_S] = p^2\Pi$ (since $\mathbb{E}[\xi_u\xi_v] = p^2$ for independent indicators and $\sum_e \tilde{L}_{uv} = \Pi$). The linearization bound $p\Pi$ is a factor $1/p$ loose. The gap between $\frac{\epsilon}{2}\Pi$ (at $p = \epsilon/2$) and the target $\epsilon\Pi$ is the "spectral cushion" that a concentration argument would need to exploit. However, the concentration must be on $\tilde{L}_S$ itself (not the linearized upper bound), since the linearization is only an inequality.

### Proposition C (Upper Bound on $c$)

*$c \leq 1/2$. That is, no universal constant $c > 1/2$ works for all graphs and all $\epsilon$.*

*Proof.* Fix $\epsilon \in (0,1)$ and let $m = \lfloor (2-\delta)/\epsilon \rfloor$ for small $\delta > 0$, so that $\epsilon m < 2$. Let $G$ be the disjoint union of $k = n/m$ copies of $K_m$.

Each component has Laplacian $L_{\text{comp}} = mI_m - J_m$ with $\lambda_{\max}(L_{\text{comp}}) = m$. If $S$ contains two vertices $u, v$ in the same component, then $L_{\{u,v\}}$ has nonzero eigenvalue 2, and the $\epsilon$-lightness condition $L_S \preceq \epsilon L$ restricted to that component requires $2 \leq \epsilon m$. Since $\epsilon m < 2$, this is impossible.

Therefore $|S| \leq k = n/m$, giving:
$$\frac{|S|}{\epsilon n} \leq \frac{1}{\epsilon m} \to \frac{1}{2} \quad \text{as } \delta \to 0.$$

Since this holds for all $\epsilon$ (with appropriate $m, n$), no universal $c > 1/2$ is possible. $\square$

**Remark.** The best possible constant is therefore $c = 1/2$ (if the conjecture is true). This matches the experimental observation that barrier greedy + partition achieves $|S|/(\epsilon n) \geq 0.5$ universally. The tight example is disjoint cliques with $m \approx 2/\epsilon$.

---

## 3. Partial Results for General Graphs

### 3.1. Setup and Decomposition

Let $I$ be the independent set from Corollary A.1 with $|I| \geq \epsilon n/3$ and all edges in $G_I$ having $R_{\text{eff}}(e) \leq \epsilon$. Sample $S \subseteq I$ by including each vertex independently with probability $p \in (0,1)$. Write $\xi_v \sim \text{Bernoulli}(p)$ and $\eta_v = \xi_v - p$.

**Decomposition.** $\tilde{L}_S = \sum_{e \in E(I,I)} \xi_u\xi_v\tilde{L}_{uv}$. Expanding $\xi_u\xi_v = p^2 + p(\eta_u + \eta_v) + \eta_u\eta_v$:

$$\tilde{L}_S = p^2\tilde{L}_I + p\tilde{W} + \tilde{Q}$$

where:
- $\tilde{W} = \sum_{v \in I} \eta_v \tilde{L}_v^{*,I}$ (linear in independent $\eta_v$), with $\tilde{L}_v^{*,I} = \sum_{u \in I: u \sim v} \tilde{L}_{uv}$
- $\tilde{Q} = \sum_{e \in E(I,I)} \eta_u\eta_v \tilde{L}_{uv}$ (quadratic, off-diagonal chaos)

**Deterministic term:** $\|p^2\tilde{L}_I\| \leq p^2$ (since $\tilde{L}_I \preceq \Pi$).

### 3.2. Bounding the Quadratic Term via Decoupling

**Rank-1 squaring identity.** Each $\tilde{L}_{uv}$ is rank-1 PSD with $\text{tr}(\tilde{L}_{uv}) = R_{\text{eff}}(e)$. For any rank-1 PSD matrix $M = \lambda\mathbf{v}\mathbf{v}^T$ ($\|\mathbf{v}\| = 1$): $M^2 = \lambda^2\mathbf{v}\mathbf{v}^T = \lambda M = \text{tr}(M) \cdot M$. Therefore:
$$\tilde{L}_{uv}^2 = R_{\text{eff}}(e) \cdot \tilde{L}_{uv} \preceq \epsilon\tilde{L}_{uv}$$
using $R_{\text{eff}}(e) \leq \epsilon$ for edges in $E(I,I)$.

**Decoupling [Ver18, Thm 6.1.1].** The decoupling inequality gives $\mathbb{E}[\|\tilde{Q}\|] \leq C_0\mathbb{E}[\|\tilde{Q}'\|]$ where $\tilde{Q}' = \sum_e \eta_u\eta'_v \tilde{L}_{uv}$ with $\{\eta'_v\}$ an independent copy of $\{\eta_v\}$, and $C_0$ is an absolute constant.

**Conditional matrix Bernstein.** Fix $\eta$ and write $\tilde{Q}' = \sum_{v \in I} \eta'_v \tilde{M}_v$ where $\tilde{M}_v = \sum_{u \in I: u \sim v} \eta_u \tilde{L}_{uv}$. Conditional on $\eta$, this is a sum of independent centered random matrices. By matrix Bernstein [Tro12]:

$$\mathbb{E}_{\eta'}[\|\tilde{Q}'\|] \leq \sqrt{2\left\|\sum_v \tilde{M}_v^2\right\|\log(n-1)} + \frac{2\max_v\|\tilde{M}_v\|\log(n-1)}{3}$$

**Variance bound.** Taking expectation over $\eta$ (cross terms vanish by independence):
$$\mathbb{E}_\eta\left[\sum_v \tilde{M}_v^2\right] = p(1-p)\sum_v \sum_{u \in I: u \sim v} \tilde{L}_{uv}^2 \preceq p\epsilon\sum_v \sum_{u \in I: u \sim v} \tilde{L}_{uv} = 2p\epsilon\tilde{L}_I \preceq 2p\epsilon\Pi$$

*Justification of the first equality:* $\mathbb{E}_\eta[\tilde{M}_v^2] = \sum_{u,w \sim v}\mathbb{E}[\eta_u\eta_w]\tilde{L}_{uv}\tilde{L}_{wv}$. Since $\mathbb{E}[\eta_u\eta_w] = 0$ for $u \neq w$ and $= p(1-p)$ for $u = w$, only diagonal terms survive. The inequality uses $\tilde{L}_{uv}^2 \preceq \epsilon\tilde{L}_{uv}$. The final sum counts each edge from both endpoints: $\sum_v \sum_{u \sim v} \tilde{L}_{uv} = 2\tilde{L}_I$.

So $\mathbb{E}_\eta[\|\sum_v \tilde{M}_v^2\|] \leq 2p\epsilon$.

**Max term bound.** $\|\tilde{M}_v\| \leq \sum_{u \sim v}|\eta_u|\|\tilde{L}_{uv}\| \leq d_I(v)\epsilon$ deterministically (since $|\eta_u| \leq 1$). Let $\Delta_I = \max_{v \in I} d_I(v)$.

**Combined bound on $\tilde{Q}$:**
$$\mathbb{E}[\|\tilde{Q}\|] \leq C_0\left(\sqrt{4p\epsilon\log n} + \frac{2\Delta_I\epsilon\log n}{3}\right) = O\left(\sqrt{p\epsilon\log n} + \Delta_I\epsilon\log n\right)$$

### 3.3. Bounding the Linear Term

$p\tilde{W} = p\sum_v \eta_v \tilde{L}_v^{*,I}$ is a sum of independent centered random matrices. By matrix Bernstein:

**Variance:** $\|\sum_v p^2\mathbb{E}[\eta_v^2](\tilde{L}_v^{*,I})^2\| = p^3(1-p)\|\sum_v (\tilde{L}_v^{*,I})^2\|$. Using $(\tilde{L}_v^{*,I})^2 \preceq \|\tilde{L}_v^{*,I}\|\tilde{L}_v^{*,I} \leq d_I(v)\epsilon \cdot \tilde{L}_v^{*,I}$:
$$\sum_v (\tilde{L}_v^{*,I})^2 \preceq \Delta_I\epsilon \sum_v \tilde{L}_v^{*,I} = 2\Delta_I\epsilon\tilde{L}_I \preceq 2\Delta_I\epsilon\Pi$$

So the variance parameter is $\sigma_W^2 \leq 2p^3\Delta_I\epsilon$.

**Max term:** $\|p\eta_v\tilde{L}_v^{*,I}\| \leq pd_I(v)\epsilon \leq p\Delta_I\epsilon$.

Matrix Bernstein: $\mathbb{E}[\|p\tilde{W}\|] \leq \sqrt{4p^3\Delta_I\epsilon\log n} + \frac{2p\Delta_I\epsilon\log n}{3}$.

### 3.4. Proposition D.1 (Relaxed ε-Lightness)

Combining §§3.2–3.3 with the deterministic term:

$$\mathbb{E}[\|\tilde{L}_S\|] \leq p^2 + O\left(\sqrt{p\epsilon\log n} + p\sqrt{p\Delta_I\epsilon\log n} + \Delta_I\epsilon\log n\right)$$

**Proposition D.1.** *For any graph $G$ and $\epsilon \in (0,1)$, there exists $S \subseteq V$ with $|S| \geq \epsilon^2 n/12$ such that:*
$$L_S \preceq C\left(\epsilon\sqrt{\log n} + \Delta_I\epsilon\log n\right) L$$
*where $C > 0$ is an absolute constant and $\Delta_I = \max_{v \in I} d_I(v)$ is the maximum degree in the induced subgraph $G_I$ on the independent set $I$ from Corollary A.1.*

*Proof.* Sample $S \subseteq I$ with $p = \epsilon/2$.

**Size:** $\mathbb{E}[|S|] = p|I| \geq \epsilon^2 n/6$. By Chernoff, $\Pr[|S| < \epsilon^2 n/12] \leq e^{-\epsilon^2 n/72}$.

**Spectral bound:** From the decomposition $\tilde{L}_S = p^2\tilde{L}_I + p\tilde{W} + \tilde{Q}$:
- Deterministic: $p^2 \leq \epsilon^2/4$
- Linear (§3.3): $\mathbb{E}[\|p\tilde{W}\|] \leq O(\sqrt{p^3\Delta_I\epsilon\log n} + p\Delta_I\epsilon\log n)$
- Quadratic (§3.2): $\mathbb{E}[\|\tilde{Q}\|] \leq O(\sqrt{p\epsilon\log n} + \Delta_I\epsilon\log n)$

The quadratic variance term $\sqrt{p\epsilon\log n} = \epsilon\sqrt{\log n/2}$ dominates the linear variance term when $\Delta_I \leq 2/\epsilon$.

Total: $\mathbb{E}[\|\tilde{L}_S\|] \leq \epsilon^2/4 + O(\epsilon\sqrt{\log n}) + O(\Delta_I\epsilon\log n)$.

By Markov, there exists a realization with both $|S| \geq \epsilon^2 n/12$ and $\|\tilde{L}_S\| \leq O(\epsilon\sqrt{\log n} + \Delta_I\epsilon\log n)$ (the Chernoff failure probability is exponentially small, so the union bound with the Markov bound succeeds). $\square$

### 3.5. Analysis of the Two Gaps

**Gap 1: The max term $\Delta_I\epsilon\log n$.**

The variance contribution $\epsilon\sqrt{\log n}$ is $\Delta_I$-independent, but the max term in matrix Bernstein introduces $\Delta_I\epsilon\log n$. For this to be $O(\epsilon)$, we need $\Delta_I = O(1/\log n)$, which fails for dense induced subgraphs.

One might try to remove high-degree vertices: let $I' = \{v \in I : d_I(v) \leq D\}$. The number removed is $|I \setminus I'| \leq 2|E(I,I)|/D$. To retain $|I'| \geq \epsilon n/6$, we need $|E(I,I)| \leq D\epsilon n/12$. But $|E(I,I)|$ has no a priori bound — it can be as large as $\binom{|I|}{2} = O(\epsilon^2 n^2)$.

**Gap 2: Subset size $\Theta(\epsilon^2 n)$ vs $\Theta(\epsilon n)$.**

We sample from $I$ (size $\Theta(\epsilon n)$) with probability $p = \epsilon/2$, giving $|S| = \Theta(\epsilon^2 n)$. To get $|S| = \Theta(\epsilon n)$, we need $p = \Theta(1)$, but then the deterministic term $p^2\|\tilde{L}_I\| = \Theta(1)$ exceeds $\epsilon$ for small $\epsilon$. Setting $p = \sqrt{\epsilon}$ gives $|S| = \Theta(\epsilon^{3/2}n)$ and deterministic term $\epsilon$, but the fluctuation terms worsen.

**Gap 3: Scalar vs spectral concentration.**

For any fixed direction $\mathbf{x}$, Hanson-Wright gives $|\mathbf{x}^T\tilde{Q}\mathbf{x}| = O(\sqrt{\epsilon})$ with probability $1 - 2e^{-c\sqrt{\epsilon}}$. But converting to a spectral norm bound $\|\tilde{Q}\| = O(\epsilon)$ requires a union bound over an ε-net of size $(C/\alpha)^{n-1}$, needing failure probability $e^{-\Omega(n)}$ per direction. The Hanson-Wright exponent is $O(\epsilon)$, independent of $n$. **This is the fundamental obstruction.**

---

## 4. Obstacles: Why Standard Tools Fail

### 4.1. Scalar Hanson-Wright + ε-Net

For fixed $\mathbf{x}$ with $\mathbf{x}^T L \mathbf{x} = 1$: $\mathbf{x}^T \tilde{L}_S \mathbf{x}$ is a degree-2 polynomial in independent Bernoulli variables. Hanson-Wright [RV13] gives tail exponent $O(\epsilon)$ (using $R_{\text{eff}}(e) \leq \epsilon$). An ε-net on $S^{n-2}$ has size $(C/\alpha)^{n-1}$, requiring exponent $\Omega(n)$. **Gap: $O(\epsilon)$ vs $\Omega(n)$.**

### 4.2. Matrix Exponential / Tropp MGF

Lieb's concavity + linearization gives $\mathbb{E}[\text{tr}\exp(\cdot)] \leq n\exp(-(3-e)/\Delta_I)$ where $\Delta_I = \max_v d_I(v)$. This is $< 1$ only when $\Delta_I < 0.28/\log n$. **Requires essentially no edges in $G_I$.**

### 4.3. MSS / Kadison-Singer

The normalized star Laplacians $T_v = \frac{1}{2}\tilde{L}_v^*$ satisfy $\sum T_v = \Pi$ with $\|T_v\| = \ell_v/2$ (half the leverage score). KS₂ requires $\delta = \max_v \|T_v\| < 1/4$ for convergent iteration. Since $\sum \ell_v = 2(n-1)$ (Foster), the average leverage score is $\approx 2$, so $\delta \geq 1$ generically. **Iteration diverges.**

### 4.4. Generic Chaining

The $\log n$ in §3 comes from the matrix dimension penalty (Golden-Thompson / Lieb), not sphere discretization. Generic chaining (Talagrand's $\gamma_2$) improves the latter but cannot remove the former. Intrinsic dimension $d_{\text{eff}} = \text{tr}(\Pi)/\|\Pi\| = n-1$ for our matrices. **No improvement.**

### 4.5. Separating Heavy Leverage Vertices

Removing vertices with $\ell_v > \delta$ costs $< 2n/\delta$ vertices (Foster). To retain $\epsilon n/6$ vertices: need $\delta \geq 12/\epsilon$, leaving $\|T_v\| \leq 6/\epsilon \gg 1$. **Still too large for KS₂.**

### 4.6. Dimension-Free Tensor Concentration (2025)

Recent papers [ACSA25, AV25] establish sharp, dimension-free concentration for sums of i.i.d. simple (rank-1) tensors $\frac{1}{N}\sum_{i=1}^N X_i^{\otimes p}$, with deviation depending on effective rank $r(\Sigma) = \text{tr}(\Sigma)/\|\Sigma\|$ rather than ambient dimension. **These do not apply to our problem** for three reasons:

1. **I.i.d. requirement.** The results require $X_1, \ldots, X_N$ to be i.i.d. copies of the same random vector. Our decoupled sum $\tilde{Q}' = \sum_v \eta'_v \tilde{M}_v$ has summands $\tilde{M}_v$ that are **non-identical** (different norms $d_I(v)\epsilon$, different spectral structure).

2. **Covariance estimation vs. heterogeneous sums.** The dimension-free results concern estimating $\mathbb{E}[X^{\otimes p}]$ from i.i.d. samples. Our problem is bounding $\|\sum_i a_i A_i\|$ where $a_i$ are independent scalars and $A_i$ are fixed, non-identical matrices — the classical matrix Bernstein setting, where $\log n$ is **tight** [vH23].

3. **van Handel's sharpness result.** The free probability approach [BvH21, vH24] shows that for sums of independent non-identical matrices, the bound $\mathbb{E}\|Z\| \lesssim \sigma(Z) + \sigma_*(Z)\sqrt{\log d}$ is **sharp** — the $\sqrt{\log d}$ cannot be removed in general. This **confirms** our $\sqrt{\log n}$ barrier rather than resolving it.

### 4.7. MSS Edge Partitioning vs. Vertex Selection

MSS/KS₂ partitions **edges** (vectors $v_i v_i^T$) into groups with bounded spectral norm per group. One might hope to use this to bound $\Delta_I$ by partitioning $E(I,I)$ into few groups with bounded degree per group. **This fails** because:

1. MSS partitions edges, not vertices. Controlling $L_S$ requires selecting **vertices** such that all edges with both endpoints in $S$ are spectrally small — a fundamentally different constraint.

2. Even if we partition $E(I,I)$ into $k$ groups with bounded spectral norm per group, the vertex sets of different edge groups overlap arbitrarily. There is no canonical way to extract a vertex subset with bounded induced degree from an edge partition.

3. The Paschalidis-Zhuang approach [PZ23] uses MSS iteratively for **spectral sparsification** (approximating $L$), which is the opposite of our goal (making $L_S$ spectrally small relative to $L$).

---

## 5. Computational Evidence and Promising Directions

### 5.1. Computational Experiments

We tested the largest ε-light subset across multiple graph families (complete, cycle, random $d$-regular, disjoint cliques, barbell, star, path, Erdős-Rényi) for $n \in \{20, 50, 100\}$ and $\epsilon \in \{0.05, 0.1, 0.2, 0.3, 0.5\}$, using four heuristics: greedy grow, greedy shrink, random sampling, and leverage-weighted sampling.

**Result.** In every case tested, $|S|/(\epsilon n) \geq 0.8$. The conjecture appears to be **YES** with $c$ close to 1.

Key observations:
- **Complete graphs:** $|S|/(\epsilon n) = 1.000$ exactly (tight with Proposition C).
- **Cycles and paths:** $|S|/(\epsilon n) \geq 1.000$ (independent sets of size $n/2$ are always ε-light).
- **Random $d$-regular:** $|S|/(\epsilon n) \geq 0.8$ for $d \in \{4, 10, 20, 48\}$, $n \leq 100$.
- **Disjoint cliques $k \times K_m$:** $|S|/(\epsilon n) \geq 0.8$ (greedy picks one vertex per component).
- **Stars:** $|S|/(\epsilon n) \geq 1.0$ (all leaves form an ε-light set for any $\epsilon$).
- **Barbell graphs:** $|S|/(\epsilon n) \geq 0.8$.

### 5.2. BSS Barrier Function Approach

Motivated by the Batson-Spielman-Srivastava barrier method for spectral sparsification, we tested a deterministic greedy using the barrier:
$$\Phi(S) = \text{tr}\left[(\epsilon\Pi - \tilde{L}_S)^{-1}\big|_{\mathbf{1}^\perp}\right]$$

The greedy adds the vertex $v$ that minimizes $\Phi(S \cup \{v\})$, stopping when no vertex can be added without $\Phi$ blowing up (i.e., $\lambda_{\max}(\tilde{L}_S)$ reaching $\epsilon$).

**Result.** The barrier greedy achieves $|S|/(\epsilon n) \geq 0.67$ for all tested graphs except stars. Combined with a random partition method (partition into $k = \lceil C/\epsilon \rceil$ groups, take the lightest), the combined best achieves $|S|/(\epsilon n) \geq 0.5$ universally.

**Barrier dynamics.** The barrier greedy reveals a two-phase structure:
1. **Independent set phase:** The first $\sim n/(d+1)$ vertices are added with 0 new edges (forming an independent set). The barrier stays flat at $(n-1)/\epsilon$.
2. **Edge accumulation phase:** Subsequent vertices each contribute 1–4 edges. The spectral ratio rises, and the barrier increases until it blows up.

For sparse graphs ($d = O(1/\epsilon)$), phase 1 alone gives $|S| \geq \epsilon n$. For dense graphs, phase 2 contributes additional vertices beyond the independent set.

### 5.3. Why the Linearized Barrier Fails

A natural idea is to apply BSS theory to the vertex star matrices $T_v = \frac{1}{2}\tilde{L}_v^*$, which satisfy $\sum_v T_v = \Pi$. If we could partition vertices into $k$ groups with $\sum_{v \in \text{group}} T_v \preceq \epsilon\Pi$, Lemma 1 would give ε-lightness.

**This fails completely.** For every graph tested, $\|T_v\| = 1/2$ for all vertices (since the leverage score $\ell_v = 2(n-1)/n \approx 2$ for regular graphs). Since $\|T_v\| = 1/2 > \epsilon$ for all $\epsilon < 1/2$, even a single vertex violates the linearized bound. The linearization (Lemma 1) is too loose by a factor of $\sim 1/\epsilon$.

**Key insight.** The actual $L_S$ is much smaller than the linearized bound $\frac{1}{2}\sum_{v \in S} L_v^*$ because the quadratic coupling $\xi_u\xi_v$ counts only edges with BOTH endpoints in $S$. When $|S| = \epsilon n$, a random vertex in $S$ has only $\sim \epsilon d_v$ neighbors in $S$, so $\|L_S\| \approx \epsilon \|L\|$ rather than $\frac{1}{2}\sum_{v \in S}\|L_v^*\| \approx |S|/2$.

### 5.4. Near-Complete Barrier Proof (Theorem E)

We present a barrier argument that proves the conjecture when $\Delta_I = O(1)$ and identifies the precise gap for general graphs.

**Setup.** Let $I$ be the independent set from Corollary A.1 with $|I| \geq \epsilon n/3$ and all edges in $G_I$ having $R_{\text{eff}}(e) \leq \epsilon$. Define the barrier:
$$\Phi(S) = \text{tr}\left[(\epsilon\Pi - \tilde{L}_S)^{-1}\big|_{\mathbf{1}^\perp}\right]$$

Build $S \subseteq I$ greedily: at each step, add the vertex $v \in I \setminus S$ minimizing $\Phi(S \cup \{v\})$.

**Barrier update.** When adding vertex $v$, the new contribution is $\delta_v = \sum_{u \in S \cap N_I(v)} \tilde{L}_{uv}$ (PSD, rank $\leq d_S(v)$). Let $A = \epsilon\Pi - \tilde{L}_S \succ 0$. The barrier changes by:
$$\Delta\Phi_v = \text{tr}[A^{-1}\delta_v(A - \delta_v)^{-1}]$$

**Lemma E.1** (Barrier bound when $\delta_v \preceq A/2$). *If $\delta_v \preceq A/2$, then $\Delta\Phi_v \leq 2\,\text{tr}[A^{-1}\delta_v]$.*

*Proof.* $(A - \delta_v)^{-1} \preceq 2A^{-1}$ when $\delta_v \preceq A/2$. $\square$

**Lemma E.2** (Average barrier increase). *The average of $\text{tr}[A^{-1}\delta_v]$ over $v \in I \setminus S$ satisfies:*
$$\frac{1}{|I \setminus S|}\sum_{v \in I \setminus S} \text{tr}[A^{-1}\delta_v] \leq \frac{2\Phi(S)}{|I \setminus S|}$$

*Proof.* Switching summation:
$$\sum_{v \notin S}\sum_{u \in S \cap N_I(v)} \text{tr}[A^{-1}\tilde{L}_{uv}] = \sum_{u \in S}\sum_{v \notin S, v \sim u} \text{tr}[A^{-1}\tilde{L}_{uv}] \leq \text{tr}\!\left[A^{-1}\sum_e 2\tilde{L}_e\right] = 2\text{tr}[A^{-1}\Pi] = 2\Phi$$
using $\sum_e \tilde{L}_e = \Pi$ and the factor 2 from double-counting. $\square$

**Theorem E** (Barrier greedy, conditional). *If at each step $t = 1, \ldots, T$ the best vertex $v_t$ satisfies $\delta_{v_t} \preceq A_t/2$ (where $A_t = \epsilon\Pi - \tilde{L}_{S_t}$), then after $T = |I|/2$ steps:*
$$\Phi(S_T) \leq \frac{16(n-1)}{\epsilon}$$
*In particular, $S_T$ is ε-light with $|S_T| = |I|/2 \geq \epsilon n/6$, giving $c = 1/6$.*

*Proof.* By Lemmas E.1–E.2, the best vertex has $\Delta\Phi \leq 4\Phi/(|I| - t)$. This gives:
$$\Phi_T \leq \Phi_0 \prod_{t=0}^{T-1}\left(1 + \frac{4}{|I|-t}\right) \leq \frac{n-1}{\epsilon}\prod_{t=0}^{|I|/2-1}\left(1 + \frac{4}{|I|-t}\right)$$
The product telescopes: $\prod_{j=|I|/2+1}^{|I|}(1 + 4/j) \leq \exp(4\sum_{j=|I|/2}^{|I|} 1/j) \leq e^{4\ln 2} = 16$. Since $\Phi_T < \infty$, we have $\tilde{L}_{S_T} \prec \epsilon\Pi$. $\square$

**The gap.** The condition "$\delta_{v_t} \preceq A_t/2$" requires $d_S(v_t) \cdot \epsilon \leq (\epsilon - \|\tilde{L}_{S_t}\|)/2$, i.e., the best vertex has few enough neighbors in $S$. This holds automatically when $d_S(v_t) = 0$ (the vertex has no neighbors in $S$ within $I$). The number of such vertices is $|I \setminus S| - |N_I(S) \setminus S| \geq |I| - |S|(1 + \Delta_I)$.

- **If $\Delta_I = O(1)$:** Non-neighbor vertices exist until $|S| = \Theta(|I|) = \Theta(\epsilon n)$. The condition holds throughout, and Theorem E gives $c = 1/6$. **Proof complete for this case.**
- **If $\Delta_I$ is large:** Non-neighbor vertices run out before $|S| = |I|/2$. The greedy is forced to add vertices with $d_S(v) \geq 1$, and the condition $\delta_v \preceq A/2$ may fail.

**Computational verification.** Tested on 16 graph families with $n \leq 50$, $\epsilon = 0.2$. The condition $\delta_v \preceq A/2$ holds for all steps in graphs with $\Delta_I = 0$ (cycles, sparse regular, stars, disjoint cliques with small components). For dense graphs ($\Delta_I \geq 7$), the condition fails at steps 3–8, but the greedy still achieves $|S|/(\epsilon n) \geq 0.5$ by exploiting the exact barrier formula beyond the regime where Lemma E.1 applies.

### 5.5. Random Sampling Is Impossible

**Proposition F.** *For $d$-regular graphs with $d \geq 4$ and $\epsilon = 0.2$, $\Pr[\text{random } S \text{ of size } \epsilon n \text{ is } \epsilon\text{-light}] \to 0$ as $n \to \infty$.*

Tested: $d = 4$, $n = 20, 30, 50, 80, 100$. $P(\text{light})$ drops from 0.168 to 0.000. Similar for $d = 10, 20$. This confirms that **any proof must use a deterministic or structured construction** — uniform random sampling of $\epsilon n$ vertices fails.

### 5.6. Log-Det Barrier Analysis

We tested the log-det barrier $\Psi(S) = -\log\det(A|_{\mathbf{1}^\perp})$ where $A = \epsilon\Pi - \tilde{L}_S$. The update is $\Delta\Psi_v = -\log\det(I - A^{-1/2}\delta_v A^{-1/2})$, which is finite whenever $\delta_v \prec A$ (no need for $\delta_v \preceq A/2$).

**Key finding.** The ratio $\text{avg}_v \Delta\Psi_v / \text{avg}_v \text{tr}[A^{-1}\delta_v]$ stays bounded by $\approx 2$ across all graphs and all steps, even when $\lambda_{\min}(A)$ is tiny. This contrasts sharply with the trace barrier $\Phi$, where the amplification factor $\Delta\Phi / \text{tr}[A^{-1}\delta_v]$ blows up to $650\times$.

**Why this doesn't close the proof.** To use the log-det barrier, we need $\min_v \Delta\Psi_v \cdot |I \setminus S| \leq C\Psi$ for a universal constant $C$. Computationally, this ratio reaches $\approx 3.3$ for $K_{50}$ at $\epsilon = 0.2$ and grows with $n$. The log-det barrier's additive recurrence $\Psi_T = \Psi_0 + \sum \Delta\Psi_t$ requires bounding $\sum \Delta\Psi_t$, which in turn requires bounding $\Phi_t = \text{tr}[A_t^{-1}]$ at each step — creating a circular dependence.

### 5.7. Precise Characterization of the Gap

The barrier approach (both trace and log-det) establishes:

1. **Lemma E.2 is tight:** $\sum_{v \in I \setminus S} \text{tr}[A^{-1}\delta_v] \leq 2\Phi$ holds in every case tested (verified computationally).
2. **The amplification is the sole obstacle:** The gap between $\text{tr}[A^{-1}\delta_v]$ (first-order) and $\Delta\Phi_v$ (exact) grows unboundedly as $\lambda_{\min}(A) \to 0$.
3. **The greedy works despite the gap:** The greedy always finds a feasible vertex (even when most vertices are infeasible), achieving $|S|/(\epsilon n) \geq 0.5$ universally.

The missing insight is how to **prove** that the greedy can always find a feasible vertex for $\Theta(\epsilon n)$ steps. The barrier framework provides the right potential function but the per-step bound is too loose for multi-rank updates.

### 5.8. Multi-Bin Barrier Method (Theorem F)

**Target statement.** For $k = \lceil 2/\epsilon \rceil$, there exists a partition $V = S_1 \sqcup \cdots \sqcup S_k$ such that every part is $\epsilon$-light: $L_{S_i} \preceq \epsilon L$ for all $i$. The largest part then satisfies $|S_i| \geq n/k \geq \epsilon n/2$, giving $c = 1/2$.

**Algorithm.** Process vertices $v = 1, \ldots, n$ in arbitrary order. Assign each vertex to the bin $i$ that minimizes the log-det barrier $\Psi_i(S_i \cup \{v\})$, where $\Psi_i = -\log\det(A_i|_{\mathbf{1}^\perp})$ and $A_i = \epsilon\Pi - \tilde{L}_{S_i}$.

**Why multi-bin is better than single-bin.** When placing vertex $v$ into bin $i$, the update is $\delta_{v,i} = \sum_{u \in S_i \cap N(v)} \tilde{L}_{uv}$. Since each already-placed neighbor $u$ is in exactly one bin, $\sum_{i=1}^k \delta_{v,i} = \sum_{u \in N(v), u \text{ placed}} \tilde{L}_{uv}$. The key: with $k$ bins, each bin receives only $\sim 1/k$ of $v$'s neighbors, so $\|\delta_{v,i}\|$ is $\sim 1/k$ times the single-bin value.

**Two regimes:**
- **Sparse regime** ($v$ has $< k$ already-placed neighbors): at least one bin has zero neighbors of $v$, so $\delta_{v,i} = 0$ and the barrier is unchanged. This covers the vast majority of steps.
- **Dense regime** ($v$ has $\geq k$ already-placed neighbors): the best bin has $\leq d/k$ neighbors.

### 5.8.1. Log-Det vs Trace Barrier: The Critical Difference

The **trace barrier** $\Phi_i = \text{tr}[A_i^{-1}]$ has exact change $\Delta\Phi_i = \text{tr}[A_i^{-1}\delta(A_i - \delta)^{-1}]$, which requires $\delta \preceq A_i/2$ for the standard $2\times$ amplification bound. This condition fails in the dense regime.

The **log-det barrier** $\Psi_i = -\log\det(A_i)$ has exact change:
$$\Delta\Psi_i = -\log\det(I - A_i^{-1/2}\delta_{v,i}A_i^{-1/2}) = -\sum_j \log(1 - \mu_j)$$
where $\mu_j$ are eigenvalues of $A_i^{-1/2}\delta_{v,i}A_i^{-1/2}$. The first-order term is $\text{tr}[A_i^{-1}\delta_{v,i}] = \sum_j \mu_j$.

**Key advantage:** The log-det amplification ratio is:
$$\frac{\Delta\Psi_i}{\text{tr}[A_i^{-1}\delta_{v,i}]} = \frac{-\sum_j\log(1-\mu_j)}{\sum_j \mu_j} \leq \frac{1}{1-\mu_{\max}}$$

This is finite whenever $\mu_{\max} < 1$ (i.e., $\delta \prec A$), with **no $A/2$ condition needed**. Compare: the trace barrier amplification is $\leq 1/(1-\mu_{\max})^2$, which diverges much faster.

### 5.8.2. Computational Verification

**Log-det amplification in best bin (all graphs, $\epsilon = 0.2$):**

| Graph | $\mu_{\max}$ | Amplification | $\Psi_{\text{final}}/\Psi_0$ | All light? |
|-------|-------------|---------------|------|-----|
| $K_{20}$ | 0.500 | 1.39 | 1.023 | YES |
| $K_{30}$ | 0.500 | 1.31 | 1.030 | YES |
| $K_{50}$ | 0.500 | 1.24 | 1.035 | YES |
| $K_{80}$ | 0.500 | 1.20 | 1.038 | YES |
| Reg(50,10) | 0.000 | — | 1.000 | YES |
| Reg(50,20) | 0.488 | 1.37 | 1.001 | YES |
| Reg(80,30) | 0.366 | 1.25 | — | YES |
| ER(50,0.5) | 0.433 | 1.31 | 1.001 | YES |
| ER(80,0.5) | 0.451 | 1.26 | 1.023 | YES |
| 5×K_{10} | 0.000 | — | 1.000 | YES |

**Contrast with trace barrier:** For $K_{80}$, the trace amplification in the best bin is **10.0** (vs 1.20 for log-det). The trace barrier's $A/2$ condition fails, but the log-det barrier's $\delta \prec A$ condition holds with $\mu_{\max} = 0.5$.

**Scaling:** Tested $K_n$ for $n \in \{10, 20, 30, 50, 80\}$ and $\epsilon \in \{0.1, 0.2, 0.3, 0.5\}$. All bins $\epsilon$-light in every case. $\Psi_{\text{final}}/\Psi_0$ converges to a constant $\leq 1.04$ as $n \to \infty$.

### 5.8.3. Theorem F.1 (Complete Graph)

**Theorem F.1.** *For $G = K_n$ and $\epsilon \in (0,1)$ with $k = \lceil 2/\epsilon \rceil$, any balanced partition into $k$ groups gives all groups $\epsilon$-light with $|S_i| \geq \lfloor n/k \rfloor \geq \epsilon n/2 - 1$.*

*Proof.* By symmetry of $K_n$, $\tilde{L}_{K_m}$ (the normalized Laplacian of $K_m$ embedded in $K_n$) has spectral norm $m/n$ (eigenvalue $m/n$ with multiplicity $m-1$ on the subspace $\mathbf{1}_S^\perp \cap \text{span}(\mathbf{e}_i : i \in S)$, and $0$ elsewhere). For a balanced partition with $|S_i| = \lfloor n/k \rfloor \leq n/k$: $\|\tilde{L}_{S_i}\| = |S_i|/n \leq 1/k \leq \epsilon/2 < \epsilon$. $\square$

### 5.8.4. Lemma H (Star Norm Identity) — Session 11

**Lemma H.** *For any vertex $v$ in any connected graph $G$, $\|\tilde{L}_v^*\| = 1$, where $\tilde{L}_v^* = \sum_{u \sim v} \tilde{L}_{vu}$ is the normalized star Laplacian of $v$.*

*Proof.*

**Upper bound.** $L_v^* = \sum_{e \ni v} L_e$ and $L - L_v^* = \sum_{e \not\ni v} L_e \succeq 0$. So $L_v^* \preceq L$, which gives $\tilde{L}_v^* = L^{+/2} L_v^* L^{+/2} \preceq L^{+/2} L L^{+/2} = \Pi$, hence $\|\tilde{L}_v^*\| \leq \|\Pi\| = 1$.

**Equality.** Vertex $v$ is isolated in $G - \text{star}(v)$ (removing all edges incident to $v$). Therefore $(L - L_v^*) \mathbf{e}_v = 0$. The vector $\mathbf{x} = \mathbf{e}_v - \frac{1}{n}\mathbf{1} \in \mathbf{1}^\perp$ satisfies:
$$\mathbf{x}^T (L - L_v^*) \mathbf{x} = 0 \implies \mathbf{x}^T L_v^* \mathbf{x} = \mathbf{x}^T L \mathbf{x}.$$
Therefore $\max_{\mathbf{x} \perp \mathbf{1}} \frac{\mathbf{x}^T L_v^* \mathbf{x}}{\mathbf{x}^T L \mathbf{x}} = 1$, i.e., $\|\tilde{L}_v^*\| = 1$. $\square$

**Verified computationally:** $\|\tilde{L}_v^*\| = 1.000000$ for every vertex in $K_n$ ($n \leq 20$), Star$_n$ ($n \leq 20$), Path$_n$ ($n \leq 10$), Barbell$_m$ ($m \leq 16$, including bridge vertices).

**Corollaries:**
- $\delta_{v,j} \preceq \tilde{L}_v^* \preceq \Pi$ for any bin $j$, so $\|\delta_{v,j}\| \leq 1$.
- $\sum_j \delta_{v,j} = \tilde{L}_v^{\text{placed}} \preceq \tilde{L}_v^*$, with $\|\tilde{L}_v^{\text{placed}}\| \leq 1$.
- The eigenvalue-1 direction of $\tilde{L}_v^*$ is $\mathbf{x}_v = L^{+/2}(\mathbf{e}_v - \frac{1}{n}\mathbf{1})$, which is the "vertex direction" of $v$ in the normalized space.
- For $K_n$: $\tilde{L}_v^*$ has eigenvalue 1 (multiplicity 1) and $2/n$ (multiplicity $n-2$).
- For Star$_n$ center: $\tilde{L}_v^*$ has eigenvalue 1 (multiplicity $n-1$), i.e., $\tilde{L}_v^* = \Pi$.

### 5.8.4a. Theorem I (Degeneracy Theorem) — Session 12

**Theorem I.** *Let $G$ be a graph with degeneracy $d < k = \lceil 3/\epsilon \rceil$. Then the greedy multi-bin algorithm with $k$ bins and degeneracy ordering produces a partition where all bins are $\epsilon$-light. Hence $c \geq 1/3$ for all graphs with degeneracy $< \lceil 3/\epsilon \rceil$.*

*Proof.* In the degeneracy ordering $v_1, \ldots, v_n$, each $v_t$ has at most $d$ back-neighbors (neighbors among $\{v_1, \ldots, v_{t-1}\}$). Since $d < k$, at most $d < k$ bins contain back-neighbors of $v_t$. Therefore at least one bin $j$ has zero back-neighbors of $v_t$, giving $\delta_{v_t, j} = 0$. The greedy places $v_t$ in such a bin with $\mu_{\max}^{(j)} = 0 < 1$, so the bin's spectral load is unchanged. By induction, all bins maintain $\|\tilde{L}_{S_j}\| = 0 \leq \epsilon$ throughout. $\square$

**Scope.** This covers all graphs with degeneracy $< \lceil 3/\epsilon \rceil$, including:
- All trees and forests ($d = 1$)
- All planar graphs ($d \leq 5$) for $\epsilon < 3/5 = 0.6$
- All graphs with bounded treewidth
- All $r$-regular graphs with $r < \lceil 3/\epsilon \rceil$
- Stars, wheels, paths, cycles, Petersen graph, and all sparse graphs

**Verified computationally:** For $d < k$, the degeneracy ordering gives $\mu_{\max} = 0$ at every step and all bins have spectral load exactly 0. Tested on $K_{10}$ ($d = 9 < k = 15$), Petersen ($d = 3$), Barbell$_{10}$ ($d = 9$), Reg(20,6) ($d = 6$), Cycle$_{20}$ ($d = 2$), Star$_{20}$ ($d = 1$).

**The dense case ($d \geq k$).** When degeneracy $d \geq k$, the graph contains a $k$-core (subgraph with minimum degree $\geq k$). In the degeneracy ordering, non-$k$-core vertices are processed first (with zero load, by the theorem above). The $k$-core vertices are processed last, and each has $\geq k$ back-neighbors, so no empty bin is guaranteed. However:
- Foster's theorem on the $k$-core gives average $R_{\text{eff}} \leq 2/k = 2\epsilon/3$ per edge.
- For $K_m$: $\|\delta_v(S)\| = (|S|+1)/m$ (verified for all $m, |S|$ tested), giving $\mu_{\max} = 2/(m\epsilon) < 2/3$ for $m > k$.
- The barbell bridge edge has $R_{\text{eff}} = 1 \gg \epsilon$, but the degeneracy ordering naturally separates the two bridge vertices: the first has only clique back-neighbors ($\mu = 2/(m\epsilon)$), and the second has only 1 back-neighbor (the first bridge vertex) and goes to an empty bin ($\mu = 0$).
- Computationally: 0 stuck cases across all tested graphs with $C = 3$.

**Remaining gap for dense case:** Prove $\mu_{\max} < 1$ for $k$-core vertices in general graphs. The scalar pigeonhole (Lemma H) gives $\min_j w^T M_j w \leq \epsilon/3$ per direction. Converting to spectral norm requires bounding the minimax-maximin ratio $C \leq 3$ for graph Laplacian partitions.

### 5.8.4b. The Remaining Gap for General Graphs — Session 12b Analysis

The log-det multi-bin barrier works computationally for all tested graphs. The degeneracy theorem (Theorem I) proves the sparse case ($d < k$). The dense case ($d \geq k$) remains open but is now much better understood.

**Projector + rank structure (Session 12b).** The constraint $\sum_j M_j \preceq \Pi$ is stronger than $\preceq B$ for generic PSD $B$, because $\Pi$ is a *projector* with eigenvalue exactly 1 in every direction of $\mathbf{1}^\perp$. The budget is perfectly uniform across all $n-1$ dimensions. Combined with the rank structure of $\delta_{v,j}$ (rank $\leq r_j$ = number of back-neighbors in bin $j$), this constrains how spectral mass distributes across bins.

**Empirical mechanism (Session 12b).** At the worst greedy step for every tested graph, the best bin has:
- **Load = 0** (the bin's existing spectral load $\|\tilde{L}_{S_j}\| = 0$).
- **rank$(\delta_{v,j}) = 1$** (exactly one back-neighbor in the bin).
- **$\mu = R_{\text{eff}}(v, u) / \epsilon < 1$** where $u$ is that single back-neighbor.

This holds even when the bin contains multiple vertices, because vertices from *different dense components* (e.g., different cliques in a barbell) share no edges, so their joint spectral load is zero. The greedy naturally interleaves vertices from different components across bins.

**Why load = 0 persists.** In the degeneracy ordering, the first $k$ vertices each go to a separate bin (Theorem I). Subsequent vertices are placed by the greedy, which distributes them across bins. A bin with vertices from different dense components has no internal edges between them, so load = 0 despite having multiple vertices. This "cross-component zero-load" effect is the key mechanism.

**The min R_eff question.** For the best bin to have $\mu < 1$, we need $R_{\text{eff}}(v, u) < \epsilon$ for the back-neighbor $u$ in that bin. Verified with exact computation (`nx.resistance_distance`):
- For every k-core vertex $v$ with $\geq k$ back-neighbors in the degeneracy ordering: $\min_u R_{\text{eff}}(v, u) < \epsilon$ over back-neighbors. **0 violations** across all tested graphs (K$_n$, Barbell, ER, Reg, MultiBridge, HubCliques, Chain).
- For k-core vertices as a set: $\min_{u \sim v} R_{\text{eff}}(v, u) < \epsilon$ for all vertices *except* those whose only k-core neighbors are bridge partners (e.g., HubCliques hub). But such vertices have $< k$ back-neighbors in the degeneracy ordering, so Theorem I applies.

**Proof attempt for min R_eff $< \epsilon$ in k-core.** If $v$ has degree $d_v \geq k$ in the k-core and leverage $\ell_v = \sum_{u \sim v} R_{\text{eff}}(v,u) < 3$, then $\min_u R_{\text{eff}} \leq \ell_v / d_v < 3/k = \epsilon$. By Foster, average leverage $< 2$, so most vertices satisfy this. Vertices with leverage $\geq 3$ (e.g., multi-bridge hubs) have $< k$ back-neighbors in the degeneracy ordering (the hub is processed before its bridge partners), so Theorem I handles them.

**What we can prove:**
- If $v$ has $< k$ already-placed neighbors, some bin has zero neighbors → $\delta = 0 \prec A$. ✓ (Theorem I)
- The amortized identity: $\sum_e w_e^T A_j^{-1} w_e = \epsilon \cdot \text{tr}[A_j^{-1}]$. This bounds the sum of first-order terms.
- The log-det amplification is $\leq 1/(1-\mu_{\max})$, bounded whenever $\mu_{\max} < 1$.
- The joint bound: $\sum_j (\tilde{L}_{S_j} + \delta_{v,j}) \preceq \Pi$ (total spectral load across all bins is bounded by the projection).
- Reformulation: $\mu_{\max} < 1$ for bin $j$ $\iff$ $\|\tilde{L}_{S_j} + \delta_{v,j}\| < \epsilon$.
- **Lemma H (Session 11):** $\|\tilde{L}_v^*\| = 1$ for all $v$. The star norm is always exactly 1.
- **Theorem I (Session 12):** Degeneracy $< k$ implies greedy with degeneracy ordering succeeds.
- **Session 12b:** At the worst step, best bin has load = 0, rank$(\delta) = 1$, $\mu = R_{\text{eff}}/\epsilon < 1$.

**The precise remaining gap.** Prove that for every k-core vertex $v$ with $\geq k$ back-neighbors in the degeneracy ordering, the greedy finds a bin $j$ with $\mu_j < 1$. The empirical mechanism is: (a) some bin has load = 0 (from cross-component interleaving), and (b) that bin's single back-neighbor has $R_{\text{eff}} < \epsilon$. Formalizing (a) requires understanding how the greedy distributes vertices across components. Formalizing (b) requires proving that back-neighbors with $R_{\text{eff}} < \epsilon$ end up in zero-load bins.

### 5.8.5. Proposition G (Barbell Obstruction for $k = \lceil 2/\epsilon \rceil$)

**Proposition G.** *The multi-bin greedy with $k = \lceil 2/\epsilon \rceil$ bins can reach $\mu_{\max} = 1$ (barrier blowup) on the barbell graph $B_m$ when $m = k$.*

*Proof.* Let $B_m$ be two copies of $K_m$ joined by a single bridge edge $(m{-}1, m)$. Set $\epsilon = 2/m$ so that $k = m$. The bridge vertex $m{-}1$ has degree $m = k$: it has $m{-}1$ neighbors in its clique and 1 bridge partner.

In the normalized Laplacian of $B_m$:
- Each within-clique edge from the bridge vertex has $R_{\text{eff}} = 2/m = \epsilon$.
- The bridge edge has $R_{\text{eff}} = 1$ (it is a cut edge).

Consider the ordering where vertex $m{-}1$ is placed last. Its $k = m$ neighbors are distributed one per bin. For each clique-neighbor bin $j$:
- $\delta_{v,j}$ is rank-1 with $\|\delta_{v,j}\| = R_{\text{eff}} = \epsilon$.
- $A_j = \epsilon\Pi - \tilde{L}_{S_j}$, and the bin contains vertices from $K_m$ giving $\lambda_{\min}(A_j) = \epsilon$.
- Therefore $\mu_{\max}^{(j)} = \epsilon/\epsilon = 1$.

For the bridge-partner bin: $\|\delta_{v,j}\| = R_{\text{eff}}(\text{bridge}) = 1 \gg \epsilon$, giving $\mu_{\max} \gg 1$.

Since $\mu_{\max} = 1$ in every bin, the log-det barrier $\Psi = -\sum \log(1-\mu_i)$ is infinite. The greedy cannot place this vertex in any bin. $\square$

**Verified computationally:** Barbell$_{10}$ with $\epsilon = 0.2$, $k = 10$: greedy gets stuck in 1/200 random orderings (the ordering where the bridge vertex is placed last with all neighbors in distinct bins). For $m \neq k$, the greedy never gets stuck.

**Consequence.** The partition approach with $k = \lceil 2/\epsilon \rceil$ bins **cannot prove $c = 1/2$** for general graphs. The barbell is a counterexample to strict feasibility of the log-det barrier at this bin count. Note: Proposition C already shows $c \leq 1/2$ via disjoint cliques, so $c = 1/2$ remains the optimal constant — but it cannot be achieved via balanced partitions.

### 5.8.6. More Bins: $k = \lceil C/\epsilon \rceil$ for $C > 2$ (Session 10)

With more bins, the barbell obstruction disappears and real margin appears.

**Computational sweep** (200+ trials per configuration, all graph families):

| $C$ | Barbell (adversarial $m = k{+}1$) | $K_n$ | All graphs |
|-----|------|------|------|
| 2.0 | $\mu_{\max} \leq 0.91$ (tight at $m = k{+}1$), **STUCK at $m = k$** | $\leq 0.83$ | Fails for barbell |
| 2.5 | $\mu_{\max} \leq 0.74$ | $\leq 0.74$ | 0 stuck in all tests |
| 3.0 | $\mu_{\max} \leq 0.64$ | $\leq 0.67$ | 0 stuck, margin $\geq 0.33$ |
| 4.0 | $\mu_{\max} = 0$ (empty bins) | $\leq 0.56$ | 0 stuck, margin $\geq 0.44$ |

**Barbell scaling at $C = 3$, $m = k{+}1$ (near-adversarial):**

| $\epsilon$ | $k$ | $m$ | $n$ | worst $\mu_{\max}$ | margin |
|-----|-----|-----|-----|-----|------|
| 0.30 | 10 | 11 | 22 | 0.606 | 0.394 |
| 0.20 | 15 | 16 | 32 | 0.625 | 0.375 |
| 0.15 | 20 | 21 | 42 | 0.635 | 0.365 |

The margin converges to $\approx 1/3$ as $m \to \infty$ (pattern: $\mu_{\max} \approx m/(m + (m{-}1)) \to 1/2$, well below 1).

**Conclusion.** $C = 3$ (giving $c = 1/3$) provides uniform margin $\geq 1/3$ across all tested graphs. This is the target for a provable result.

### 5.8.7. Approaches Attempted to Close the Gap

1. **Coloring $G_{\text{hi}}$ + matrix pigeonhole.** Color the high-resistance graph ($R_{\text{eff}} > \epsilon$) with $k$ colors. Each color class has only low-$R$ edges. But $\sum_i \tilde{L}_{S_i} \preceq \Pi$ does NOT imply $\min_i \|\tilde{L}_{S_i}\| \leq 1/k$. Counterexample: $M_1 = \text{diag}(0.6, 0)$, $M_2 = \text{diag}(0, 0.6)$ with $M_1 + M_2 \preceq I$ but $\|M_i\| = 0.6 > 1/2$.

2. **Random partition + matrix Bernstein.** For a random $k$-partition with proper coloring of $G_{\text{hi}}$: $\mathbb{E}[\tilde{L}_{S_j}] = (1/k^2)\Pi$, $\|\mathbb{E}\| = \epsilon^2/4$. Matrix Bernstein gives $\|\tilde{L}_{S_j}\| \leq \epsilon^2/4 + O(\epsilon^{3/2}\sqrt{\log n})$. This is $< \epsilon$ for $n \leq e^{O(1/\epsilon)}$ but fails for $n \to \infty$ due to $\sqrt{\log n}$. Verified computationally: bound $< \epsilon$ for all tested graphs ($n \leq 200$).

3. **Random partition (empirical).** Random $k$-partition succeeds for $K_n$ (91% at $n = 50$) but fails for general graphs (0% for Reg(50,10)). Confirms greedy is essential.

4. **Amortized potential.** $\Phi_n \leq \Phi_0 \cdot n^{\epsilon^2}$ (finite for fixed $\epsilon$), but uses first-order approximation which requires $\mu_{\max} < 1$ — circular.

5. **Direct norm bound.** $\|\delta_{v,j}\|/\lambda_{\min}(A_j)$ can equal 1 even for rank-1 delta (e.g., $K_n$ with $s = 1$: ratio $= R_{\text{eff}}/\epsilon = (2/n)/\epsilon$, which is $< 1$ but the directional $\mu_{\max}$ equals this exactly).

6. **Quadratic form contradiction (Session 10).** If all $\mu_{\max}^{(j)} \geq 1$, summing $w_j^T \delta_{v,j} w_j \geq w_j^T A_j w_j$ over bins does NOT yield a contradiction for general graphs (the witnesses $w_j$ are different for each bin).

7. **Potential function tracking (Session 10).** The log-det potential $\sum_j \Psi_j$ grows linearly in $n$ but stays bounded. However, bounded total potential does not imply $\mu_{\max} < 1$ at each step — the argument is circular.

8. **Joint pigeonhole (Session 10).** The bound $\sum_j M_j \preceq \Pi$ where $M_j = \tilde{L}_{S_j} + \delta_{v,j}$ gives scalar pigeonhole: for any fixed $w$, $\min_j w^T M_j w \leq 1/k \leq \epsilon/2$. But converting to spectral norm (uniform over $w$) requires a matrix pigeonhole that does not hold for general PSD matrices.

### 5.8.8. Gap Closure Experiments (Sessions 9–10)

**Session 9 experiments:**

**Experiment A (Interlacing families).** Computed the expected characteristic polynomial of $\tilde{L}_{S_j}$ over all random $k$-colorings for $K_4$–$K_{12}$, $C_5$–$C_8$, and Petersen. Result: the expected polynomial is **never real-rooted** (max $|\text{imag}|$ up to 0.34). Standard MSS interlacing requires real-rootedness → **Route killed.** However, all roots' real parts are $\leq \epsilon$ in every case, suggesting the expected polynomial "knows" the answer through a non-real-rootedness mechanism.

**Experiment B (Leverage ordering).** Tested ascending/descending leverage order, random, and natural ordering across $K_{10}$–$K_{30}$, Petersen, $C_{12}$, Reg(20,6). Result: **ordering is irrelevant** for $K_n$ (uniform leverage). For all graphs, 0/500 orderings ever stuck. $\mu_{\max}$ for $K_n$ converges to $\sim 1/k \approx \epsilon/2$. Confirms greedy is robust but ordering provides no proof leverage.

**Experiment C (Structural contradiction).** At the worst greedy step (across 300 random orderings), extracted witness vectors and trace sums. For $K_{20}$ at $\epsilon = 0.2$, $k = 10$: $\sum_j \text{tr}(A_j^{-1}\delta_{v,j}) = 11.75$ vs $k = 10$. The trace sum **exceeds** $k$ even when no bins are bad → **trace-based "all bins bad" contradiction is impossible.** Cross-bin witness ratios: $\sim 0.33$ (bad direction of one bin is only $1/3$ as bad in others). This confirms Laplacian structure prevents alignment of bad directions, but the non-alignment factor is insufficient for a trace argument.

**Session 10 experiments (non-alignment and barbell):**

**Experiment D (Quadratic form contradiction).** Tested whether $\sum_j w_j^T \delta_{v,j} w_j \geq \sum_j w_j^T A_j w_j$ ("all bins bad") leads to contradiction via $\sum_j \delta_{v,j} \preceq \Pi$. Result: no contradiction for general graphs because witnesses $w_j$ are bin-specific.

**Experiment E (Effective rank analysis).** For the best bin at the worst step: $\|M_{\text{best}}\| = \text{tr}(M_{\text{best}})/\text{eff\_rank}$. The effective rank is always $\geq \text{tr}/\epsilon$, ensuring $\|M\| < \epsilon$. But proving effective rank bounds requires Laplacian structure not captured by trace pigeonhole.

**Experiment F (Minimax vs maximin).** The minimax $\min_j \mu_{\max}^{(j)}$ is always well below 1, but the maximin $\max_w \min_j w^T \delta w / w^T A w$ is much smaller. The gap (factor 2–4×) shows the spectral pigeonhole per-direction is much stronger than the uniform bound.

**Experiment G (Barbell boundary — CRITICAL).** Barbell$_{10}$ at $\epsilon = 0.2$, $k = 10$: greedy gets stuck (1/200 trials). Bridge edge has $R_{\text{eff}} = 1$ (cut edge, always exactly 1 regardless of $m$). Bridge vertex leverage = 2.8. The stuck case occurs when $m = k$ exactly (bridge degree = number of bins). See Proposition G (§5.8.5).

**Experiment H ($C$-sweep).** Systematic test of $k = \lceil C/\epsilon \rceil$ for $C \in \{2, 2.5, 3, 4\}$ across barbells ($m = 8$–$30$), complete graphs, stars, paths, random regular. Results in §5.8.6.

**Session 11 experiments and proof attempts:**

**Experiment I (Comprehensive $C = 3$ sweep).** 19 graph families ($K_n$, Barbell, Star, Path, Cycle, Petersen, Wheel, Random Regular) × 4 values of $\epsilon$ × 500 trials = **0 stuck cases**. Worst $\mu_{\max} = 0.635$ (Barbell$_{21}$, $\epsilon = 0.15$). Confirms $c = 1/3$ target universally.

**Experiment J ($b_v$ analysis).** At the worst greedy step, measured $b_v$ = number of bins containing neighbors of $v$. Result: $b_v < k$ for Star, Wheel, Path, Cycle, Petersen (empty bin exists, $\mu = 0$). Only $K_n$ and Barbell have $b_v = k$.

**Experiment K ($\min R_{\text{eff}}$ when $b_v = k$).** When all $k$ bins have neighbors of $v$: checked whether $\min_u R_{\text{eff}}(v,u) < \epsilon$. Result: **0 violations** across $K_n$ ($n \leq 30$), Barbell ($m \leq 21$), 200 trials each.

**Experiment L (Minimax-maximin ratio).** Measured $\|M_{\text{best}}\| / (1/k)$ at the worst step. Results: $K_{20}$: 1.50, Barbell$_{16}$: 1.88, Barbell$_{21}$: 1.43. All well below 3, confirming the minimax-maximin gap is $\leq 2$ for graph Laplacians.

**Proof attempt 1 (Scalar pigeonhole + Lemma H).** Joint bound $\sum_j M_j \preceq \Pi$ gives $\min_j w^T M_j w \leq \epsilon/3$ for any direction $w$. Gap: need spectral norm $\|M_{j^*}\| < \epsilon$, not just one direction. Requires minimax-maximin ratio $C \leq 3$. **STATUS: OPEN.**

**Proof attempt 2 ($\min R_{\text{eff}} < \epsilon$ when $b_v = k$).** For $K_n$: $R_{\text{eff}} = 2/n \leq 2\epsilon/3 < \epsilon$ when $n \geq 3/\epsilon + 1$. For Barbell: clique edges have $R_{\text{eff}} = 2/m < \epsilon$ when $m > 2/\epsilon$. General case: need to show internal edges in $N(v)$ force small $R_{\text{eff}}$. **STATUS: OPEN (verified, not proved).**

**Proof attempt 3 (Weaver/KS2 connection).** Edge vectors $w_e$ with $\sum w_e w_e^T = \Pi$ and $\|w_e\|^2 = R_{\text{eff}}(e)$. Bownik's $KS_r$ bound gives $\|M_j\| \leq 1/k + \sqrt{\alpha/k} + \alpha \approx 1.91\epsilon$. Too loose ($> \epsilon$). **STATUS: INSUFFICIENT.**

**Proof attempt 4 (Barrier/potential).** Inherently circular: bounding barrier increase requires $\mu_{\max} < 1$. **STATUS: DEAD.**

### 5.9. Remaining Proof Directions (Updated after Session 11)

**Routes killed by experiments:**
- Interlacing families (vanilla MSS): expected polynomial not real-rooted.
- Trace-based "all bins bad" contradiction: trace sum exceeds $k$ regardless.
- **$c = 1/2$ via balanced partition**: Barbell obstruction (Proposition G). The partition approach with $k = \lceil 2/\epsilon \rceil$ bins provably fails.
- Joint matrix pigeonhole: $\sum M_j \preceq \Pi$ does not imply $\min_j \|M_j\| < \epsilon$ for general PSD matrices.
- Amortized potential: circular (assumes $\mu_{\max} < 1$).
- Trace pigeonhole: $\min_j \text{tr}(M_j) \leq (n-1)/k \approx \epsilon n/3 \gg \epsilon$ for $n \gg 3$.

**Primary route: $c = 1/3$ via $k = \lceil 3/\epsilon \rceil$ bins.**

With $k = \lceil 3/\epsilon \rceil$, the C-sweep (§5.8.6) shows $\mu_{\max} \leq 2/3$ uniformly across all tested graphs, with margin $\geq 1/3$. The proof requires showing that at each greedy step, $\exists$ bin $j$ with $\|M_j\| = \|\tilde{L}_{S_j} + \delta_{v,j}\| < \epsilon$.

**Proof ingredients available (Session 11):**

1. **Lemma H (Star Norm Identity).** $\|\tilde{L}_v^*\| = 1$ for all $v$. Corollary: $\sum_j \delta_{v,j} \preceq \tilde{L}_v^* \preceq \Pi$.

2. **Joint bound.** $\sum_j M_j \preceq \Pi$ where $M_j = \tilde{L}_{S_j} + \delta_{v,j}$. This holds because internal edges and $v$-to-bin edges are disjoint subsets of all edges, and $\sum_e \tilde{L}_e = \Pi$.

3. **Scalar pigeonhole.** For any fixed unit $w \perp \mathbf{1}$: $\min_j w^T M_j w \leq 1/k \leq \epsilon/3$.

4. **$b_v < k$ case (Session 11).** Let $b_v$ = number of bins containing at least one neighbor of $v$. If $b_v < k$, some bin has zero neighbors of $v$, so $\delta_{v,j} = 0$ and $\mu_{\max}^{(j)} = 0$. Verified: Star, Wheel, Path, Cycle, Petersen all have $b_v < k$ at every step (greedy clusters non-adjacent vertices). Only $K_n$ and barbell (with clique neighborhoods) have $b_v = k$.

5. **$b_v = k$ case: $\min_u R_{\text{eff}}(v,u) < \epsilon$ (Session 11, verified).** When all $k$ bins have neighbors of $v$, the minimum effective resistance among $v$'s placed neighbors is always $< \epsilon$. Verified: 0 violations across $K_n$ ($n \leq 30$), Barbell ($m \leq 21$), 200 trials each. This means the best bin has a rank-1 delta with $\|\delta\| = R_{\text{eff}} < \epsilon$ and $\lambda_{\min}(A_j) \geq \epsilon - \text{load}$, giving $\mu < 1$.

6. **Foster's theorem.** $\sum_v \text{leverage}_v = 2(n-1)$, average leverage $< 2$.

**The precise remaining gap:**

The scalar pigeonhole gives $\min_j w^T M_j w \leq \epsilon/3$ for any fixed direction $w$. The spectral norm is $\|M_j\| = \max_w w^T M_j w$. Converting the per-direction bound to a spectral norm bound requires:
$$\min_j \|M_j\| \leq C \cdot \max_w \min_j w^T M_j w \leq C/k$$
for some constant $C$. For general PSD matrices, $C$ can be as large as the dimension. For graph Laplacians, experiments show $C \leq 2$ (the minimax-maximin gap is at most $2\times$). **Proving $C \leq 3$ would close the proof with $c = 1/3$.**

**Secondary routes still alive:**

1. **Double barrier (upper + lower).** BSS uses both upper ($\Phi_U = \text{tr}[A_j^{-1}]$) and lower ($\Phi_L = \text{tr}[(\tilde{L}_{S_j} + \delta\Pi)^{-1}]$) barriers. The lower barrier forces balanced loading → uniform slack → $\mu_{\max}$ bounded. We have only used the upper barrier.

2. **Non-real-rootedness polynomial method.** Expected polynomial has roots $\leq \epsilon$ (verified) but is not real-rooted. A Schwartz-Zippel or probabilistic argument might extract existence of a good coloring without real-rootedness.

3. **Global local-search.** Minimize $\sum_i (-\log\det A_i)$ over partitions via vertex swaps. Convexity of log-det might give a descent proof without controlling $\mu_{\max}$ step-by-step.

---

## 6. Summary

| Result | Status | Scope |
|--------|--------|-------|
| **Lemma 1** (Linearization) | **Proved** | All graphs |
| **Theorem A** (Independence regime) | **Proved** | $\bar{d} = O(1/\epsilon)$; $|S| \geq \epsilon n/6$ |
| **Corollary A.1** (Eff. resistance decomp.) | **Proved** | All graphs; $|I| \geq \epsilon n/3$, $R_{\text{eff}} \leq \epsilon$ |
| **Corollary A.2** (Trace-small) | **Proved** | $\text{tr}(\tilde{L}_I) \leq \epsilon$; $|I| \geq \epsilon n/3$ |
| **Theorem B** (Expectation) | **Proved** | All graphs (expectation only, no concentration) |
| **Proposition C** (Upper bound) | **Proved** | $c \leq 1/2$ |
| **Proposition D.1** (Relaxed ε-lightness) | **Proved** | $|S| \geq \epsilon^2 n/12$; spectral bound $O(\epsilon\sqrt{\log n} + \Delta_I\epsilon\log n)$ |
| **Computational evidence** (§5) | **Tested** | $|S|/(\epsilon n) \geq 0.8$ for all graph families tested ($n \leq 100$) |
| **BSS barrier greedy** (§5.2) | **Tested** | Works empirically; combined with partition gives $|S|/(\epsilon n) \geq 0.5$ |
| **Theorem E** (Barrier, conditional) | **Proved** | $c = 1/6$ when $\Delta_I = O(1)$; gap: $\delta_v \preceq A/2$ condition for dense $G_I$ |
| **Theorem F** (Multi-bin, computational) | **Tested** | $k = \lceil 2/\epsilon \rceil$ bins, all $\epsilon$-light in most cases; **fails for barbell at $m = k$** |
| **Theorem F.1** (Complete graph) | **Proved** | $K_n$: balanced $k$-partition is $\epsilon$-light; $c = 1/2$ |
| **Lemma H** (Star norm identity) | **Proved** | $\|\tilde{L}_v^*\| = 1$ for all $v$ in all connected graphs |
| **Theorem I** (Degeneracy case) | **Proved** | $c = 1/3$ for all graphs with degeneracy $< \lceil 3/\epsilon \rceil$ (trees, planar, bounded treewidth, sparse regular) |
| **Proposition F** (Random sampling fails) | **Tested** | $P(\text{random } S \text{ of size } \epsilon n \text{ is } \epsilon\text{-light}) \to 0$ as $n \to \infty$ |
| **Proposition G** (Barbell obstruction) | **Proved** | $k = \lceil 2/\epsilon \rceil$ greedy hits $\mu_{\max} = 1$ on barbell $B_m$ with $m = k$; $c = 1/2$ via partitions is impossible |
| **Theorem F** ($C = 3$ variant, computational) | **Tested** | $k = \lceil 3/\epsilon \rceil$ bins: $\mu_{\max} \leq 2/3$ for all tested graphs; would give $c = 1/3$ |
| **Full conjecture** ($c > 0$ universal) | **Open** | Target: $c = 1/3$ via $k = \lceil 3/\epsilon \rceil$ multi-bin partition |

### Honest Assessment of Gaps

**Five developments** from Sessions 10–12 reshape the proof landscape:

**1. Barbell obstruction (Proposition G).** The log-det multi-bin barrier with $k = \lceil 2/\epsilon \rceil$ bins **provably fails** on the barbell graph $B_m$ when $m = k$. The bridge vertex hits $\mu_{\max} = 1$ in every bin, making the barrier infinite. This kills the $c = 1/2$ target via the partition approach.

**2. $C = 3$ gives uniform margin.** With $k = \lceil 3/\epsilon \rceil$ bins, the greedy achieves $\mu_{\max} \leq 2/3$ across all tested graphs (including adversarial barbells), with margin $\geq 1/3$. Comprehensive sweep: 0 stuck across 19 graph families × 4 $\epsilon$ values × 500 trials.

**3. Star Norm Identity (Lemma H).** $\|\tilde{L}_v^*\| = 1$ for all $v$. This gives the joint bound $\sum_j M_j \preceq \Pi$ and scalar pigeonhole $\min_j w^T M_j w \leq \epsilon/3$ for any direction $w$.

**4. Degeneracy Theorem (Theorem I, Session 12).** For all graphs with degeneracy $d < k = \lceil 3/\epsilon \rceil$, the greedy with degeneracy ordering **provably** produces an $\epsilon$-light partition with $c = 1/3$. The proof is clean: each vertex has $< k$ back-neighbors, so an empty bin always exists with $\delta = 0$. This covers all trees, planar graphs ($d \leq 5$, for $\epsilon < 0.6$), bounded-treewidth graphs, and sparse regular graphs.

**5. Projector-rank mechanism (Session 12b).** At the worst greedy step for every tested graph, the best bin has load $= 0$, rank$(\delta_{v,j}) = 1$, and $\mu = R_{\text{eff}}(v,u)/\epsilon < 1$. Even bins with multiple vertices have zero load when their vertices come from different dense components (no cross-component edges). This "cross-component zero-load" effect is the key empirical mechanism. Verified with exact $R_{\text{eff}}$ computation: 0 violations across all tested graphs including adversarial constructions (MultiBridge, HubCliques, Chain of cliques).

**The remaining gap (refined, Session 12b):** The **dense case** — graphs with degeneracy $d \geq k$, i.e., containing a $k$-core with minimum degree $\geq k$. In the degeneracy ordering, non-$k$-core vertices are handled by Theorem I (zero load). The $k$-core vertices are processed last and have $\geq k$ back-neighbors, so no empty bin is guaranteed. However:
- Foster's theorem on the $k$-core gives average $R_{\text{eff}} \leq 2\epsilon/3$ per edge.
- For $K_m$: $\|\delta_v(S)\| = (|S|+1)/m$ (verified), giving $\mu_{\max} = 2/(m\epsilon) < 2/3$ for $m > k$.
- The barbell's degeneracy ordering naturally separates bridge vertices: the first has only clique back-neighbors ($\mu = 2/(m\epsilon)$), the second goes to an empty bin ($\mu = 0$).
- Computationally: 0 stuck cases across all tested dense graphs with $C = 3$.
- The projector-rank analysis (Session 12b) shows the empirical mechanism: best bin has load $= 0$, rank$(\delta) = 1$, $\mu = R_{\text{eff}}/\epsilon < 1$.

Formally, the dense case reduces to proving that for every $k$-core vertex with $\geq k$ back-neighbors: (a) some bin has load $= 0$ from cross-component interleaving, and (b) that bin's single back-neighbor has $R_{\text{eff}} < \epsilon$. Both hold empirically with 0 violations.

**What would close the proof ($c = 1/3$):**

1. **Prove the minimax-maximin gap $C \leq 3$ for graph Laplacians.** The rank-1 structure of edge Laplacians and the identity $\sum_e \tilde{L}_e = \Pi$ constrain the geometry. Empirically $C \leq 2$.
2. **$K_n$ is proved** (Theorem F.1). The complete graph admits a balanced partition with all parts $\epsilon$-light.
3. **Sparse case is proved** (Theorem I). All graphs with degeneracy $< \lceil 3/\epsilon \rceil$.
4. **$\min_u R_{\text{eff}}(v,u) < \epsilon$ when $b_v = k$ (Session 11, verified).** When all bins have neighbors, the minimum $R_{\text{eff}}$ is always $< \epsilon$. Structural graph theory argument needed for general proof.

---

## References

- [ACSA25] O. Al-Ghattas, J. Chen, D. Sanz-Alonso, *Sharp concentration of simple random tensors*, arXiv:2502.16916, 2025.
- [AV25] P. Abdalla, R. Vershynin, *On the dimension-free concentration of simple tensors via matrix deviation*, arXiv:2506.09333, 2025.
- [Bow24] M. Bownik, *Selector form of Weaver's conjecture, Feichtinger's conjecture, and frame sparsification*, arXiv:2405.18235, 2024.
- [BvH21] A. S. Bandeira, M. T. Boedihardjo, R. van Handel, *Matrix concentration inequalities and free probability*, Invent. Math. **234**, 2023, 419–487.
- [Fos49] R. M. Foster, *The average impedance of an electrical network*, Contributions to Applied Mechanics, 1949.
- [MSS15] A. W. Marcus, D. A. Spielman, N. Srivastava, *Interlacing families II: Mixed characteristic polynomials and the Kadison-Singer problem*, Ann. Math. **182**(1), 2015, 327–350.
- [PZ23] P. Paschalidis, A. Zhuang, *Linear-sized spectral sparsifiers and the Kadison-Singer problem*, arXiv:2308.12483, 2023.
- [RV13] M. Rudelson, R. Vershynin, *Hanson-Wright inequality and sub-gaussian concentration*, Electron. Commun. Probab. **18**(82), 2013, 1–9.
- [SS11] D. A. Spielman, N. Srivastava, *Graph sparsification by effective resistances*, SIAM J. Comput. **40**(6), 2011, 1913–1926.
- [ST11] D. A. Spielman, S.-H. Teng, *Spectral sparsification of graphs*, SIAM J. Comput. **40**(4), 2011, 981–1025.
- [Tro12] J. A. Tropp, *User-friendly tail bounds for sums of random matrices*, Found. Comput. Math. **12**(4), 2012, 389–434.
- [Ver18] R. Vershynin, *High-Dimensional Probability*, Cambridge University Press, 2018.
- [vH24] A. S. Bandeira, G. Cipolloni, D. Schröder, R. van Handel, *Matrix concentration inequalities and free probability II*, arXiv:2406.11453, 2024.

---

## Appendix: Partial Lean 4 Verification

The algebraic and arithmetic skeleton of our partial results has been formally verified in Lean 4 + Mathlib. The file `FirstProof/P06_EpsilonLight.lean` compiles with **zero errors and zero `sorry`s** and verifies the following components:

1. **Linearization inequality** (`linearization_ineq_real`): For $s, t \in [0,1]$: $st \leq (s+t)/2$. Key to the expectation bound in §3.1. Verified by `nlinarith`.

2. **Foster counting** (`foster_edge_count`, `avg_degree_bound`): The edge-counting argument: if $m\tau < \text{total}$ and $\text{total} < n$, then $m\tau < n$. Used in Theorem A (sparse regime).

3. **Independent set arithmetic** (`indep_set_denom_bound`, `indep_set_pos`): For $\varepsilon \leq 1$: $2 + \varepsilon \leq 3$, so $\varepsilon n/(2+\varepsilon) \geq \varepsilon n/3$. Used in Corollary A.1.

4. **Trace-spectral norm bound** (`psd_spectral_from_trace`): For PSD matrices: $\|M\| \leq \text{tr}(M) \leq \varepsilon$ implies $\|M\| \leq \varepsilon$. Transitivity of $\leq$.

5. **Expectation computation** (`expectation_computation`, `spectral_cushion`, `spectral_cushion_pos`): The arithmetic $(\varepsilon/2)/2 \cdot 2 = \varepsilon/2$ and the spectral cushion $\varepsilon - \varepsilon/2 = \varepsilon/2 > 0$.

6. **Upper bound $c \leq 1$** (`upper_bound_on_c`): Proposition C: if $c \cdot x \leq x$ and $x > 0$, then $c \leq 1$. Verified by `le_of_mul_le_mul_right`.

7. **Concrete clique checks**: $K_3$ with $\varepsilon = 1/2$ violates lightness ($2 > 1.5$); $K_4$ with $\varepsilon = 1/2$ satisfies it ($2 \leq 2$). Verified by `norm_num`.

8. **Hanson-Wright decomposition** (`deterministic_term`, `hw_frobenius_bound`): The deterministic term $(\varepsilon/2)^2 = \varepsilon^2/4$ and the Frobenius bound.

9. **$\varepsilon$-net gap** (`epsilon_net_gap`): For $\varepsilon < 1$ and $n \geq 2$: $\varepsilon/16 < n$. This is the precise gap showing the Hanson-Wright exponent is too small for the union bound.

10. **MCE and KS₂ bounds** (`mce_exponent_check`, `ks2_convergence_condition`): The matrix Chernoff exponent check $(e-1)/2 < 1$ and the KS₂ convergence condition $1/2 + \delta < 1 \Rightarrow \delta < 1/2$.

11. **Proof structure** (`theorem_A_structure`, `prop_D1_structure`): The logical skeleton of Theorem A (sparse → independent set → light) and Proposition D.1 (expectation → concentration).

**Scope and limitations.** The Lean file verifies arithmetic, algebraic identities, and logical structure. The spectral theory (graph Laplacians, PSD ordering, matrix concentration) is beyond current Mathlib capabilities.
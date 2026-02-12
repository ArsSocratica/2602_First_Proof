# Problem 7 — Proof Draft

## Theorem

**No when $\delta(G) = 0$ or $\dim(G/K) \leq 4$; open when $\delta(G) \neq 0$ and $\dim(G/K) \geq 5$.**

Let $G$ be a connected real semi-simple Lie group with finite center and no compact factors, $K \subset G$ a maximal compact subgroup, and $\delta(G) = \operatorname{rank}_\mathbb{C}(\mathfrak{g}) - \operatorname{rank}_\mathbb{C}(\mathfrak{k})$ the fundamental rank.

**Case 1 ($\delta(G) = 0$).** If $\Gamma \subset G$ is a uniform lattice with torsion (not necessarily 2-torsion), then $\Gamma$ cannot be the fundamental group of a compact manifold without boundary whose universal cover is $\mathbb{Q}$-acyclic. The proof uses the Euler characteristic: $\mathbb{Q}$-acyclicity forces $\chi(M) = \chi_\mathbb{Q}(\Gamma) \neq 0$, while L²-Betti number vanishing forces $\chi(M) = 0$. **Proof complete.**

**Case 2 ($G \cong \mathrm{SL}(2, \mathbb{C})$, $\delta(G) = 1$, $d = 3$).** The dimension-forcing result (Corollary 2) gives $\dim M = 3$. By the Kneser–Milnor decomposition and Perelman's geometrization, every closed irreducible 3-manifold with infinite $\pi_1$ is aspherical, forcing $\Gamma$ to be torsion-free — contradiction. **Proof complete.**

**Case 2b ($d = 4$).** Vacuous: no connected real semi-simple $G$ without compact factors has $\delta(G) \neq 0$ and $\dim(G/K) = 4$ (all $d = 4$ groups — $\mathrm{SU}(2,1)$, $\mathrm{SO}_0(4,1)$, $\mathrm{Sp}(2,\mathbb{R})$ — have $\delta = 0$). See Step 4c.

**Case 3 ($\delta(G) \neq 0$, $d \geq 5$).** The Euler characteristic and geometrization obstructions are both unavailable. A thorough analysis of surgery-theoretic obstructions (Sullivan splitting, Smith theory, finiteness, integral Poincaré duality) reveals **no obstruction** to the existence of such a manifold. The question reduces to whether an integral Poincaré complex with the required properties exists. The smallest open case is $G = \mathrm{SL}(3, \mathbb{R})$, $d = 5$. **Status: open.**

---

## Proof

### Setup and Notation

Let $G$ be a connected real semi-simple Lie group with finite center and no compact factors. Let $K \subset G$ be a maximal compact subgroup, so that $X = G/K$ is the associated Riemannian symmetric space of non-compact type. Let $d = \dim(X)$.

Let $\Gamma \subset G$ be a uniform (cocompact) lattice. By Selberg's lemma, $\Gamma$ contains a torsion-free normal subgroup $\Gamma' \trianglelefteq \Gamma$ of finite index $m = [\Gamma : \Gamma']$. The quotient $\Gamma' \backslash X$ is a closed Riemannian manifold of dimension $d$.

Define the **fundamental rank** (or **deficiency**) of $G$:
$$\delta(G) = \operatorname{rank}_\mathbb{C}(\mathfrak{g}) - \operatorname{rank}_\mathbb{C}(\mathfrak{k})$$
where $\operatorname{rank}_\mathbb{C}(\mathfrak{g})$ denotes the absolute rank of $G$ (the dimension of a Cartan subalgebra of $\mathfrak{g}_\mathbb{C}$), and similarly for $K$. Equivalently, $\delta(G) = 0$ if and only if $K$ contains a maximal torus of $G$ (the "equal-rank" condition), which happens if and only if the compact dual $G_u/K$ has nonzero Euler characteristic.

**Remark on terminology:** We say $\widetilde{M}$ is **$\mathbb{Q}$-acyclic** if $\widetilde{H}_i(\widetilde{M}; \mathbb{Q}) = 0$ for all $i \geq 0$, i.e., $H_0(\widetilde{M}; \mathbb{Q}) \cong \mathbb{Q}$ and $H_i(\widetilde{M}; \mathbb{Q}) = 0$ for $i > 0$.

---

### Step 1: Spectral Sequence Collapse

**Lemma 1.** Let $M$ be a closed manifold with $\pi_1(M) \cong \Gamma$ and suppose $\widetilde{M}$ is $\mathbb{Q}$-acyclic. Then
$$H_i(M; \mathbb{Q}) \cong H_i(\Gamma; \mathbb{Q}) \quad \text{for all } i \geq 0.$$

*Proof.* Consider the Cartan-Leray (Lyndon-Hochschild-Serre) spectral sequence for the regular covering $\widetilde{M} \to M$ with deck group $\Gamma$:
$$E_2^{p,q} = H_p(\Gamma;\, H_q(\widetilde{M}; \mathbb{Q})) \;\Longrightarrow\; H_{p+q}(M; \mathbb{Q}).$$

Since $\widetilde{M}$ is $\mathbb{Q}$-acyclic:
- $H_0(\widetilde{M}; \mathbb{Q}) \cong \mathbb{Q}$ with trivial $\Gamma$-action (as $\widetilde{M}$ is connected and path-connected).
- $H_q(\widetilde{M}; \mathbb{Q}) = 0$ for all $q > 0$.

Therefore $E_2^{p,q} = 0$ for $q > 0$, and $E_2^{p,0} = H_p(\Gamma; \mathbb{Q})$. The spectral sequence is concentrated on the $q = 0$ line and hence collapses at $E_2$:
$$H_i(M; \mathbb{Q}) \cong E_\infty^{i,0} = E_2^{i,0} = H_i(\Gamma; \mathbb{Q}). \qquad \square$$

**Corollary 1.** Under the hypotheses of Lemma 1:
$$\chi(M) = \chi_\mathbb{Q}(\Gamma) := \sum_{i=0}^{\operatorname{vcd}(\Gamma)} (-1)^i \dim_\mathbb{Q} H_i(\Gamma; \mathbb{Q}).$$

*Proof.* Since $\Gamma$ is a uniform lattice in $G$, it has virtual cohomological dimension $\operatorname{vcd}(\Gamma) = d = \dim(G/K)$. Thus $H_i(\Gamma; \mathbb{Q}) = 0$ for $i > d$, and the sum is finite. The equality follows from Lemma 1 and the definition $\chi(M) = \sum (-1)^i \dim_\mathbb{Q} H_i(M; \mathbb{Q})$. $\square$

**Corollary 2** (Dimension forcing). Under the hypotheses of Lemma 1, $\dim M = d = \dim(G/K)$.

*Proof.* Let $n = \dim M$. Since $\Gamma'$ is a torsion-free uniform lattice, $\Gamma' \backslash G/K$ is a closed orientable aspherical $d$-manifold, so $\Gamma'$ is a Poincaré duality group of dimension $d$ with $H^d(\Gamma'; \mathbb{Q}) \cong \mathbb{Q}$. Since $G$ is connected, all deck transformations of $G/K \to \Gamma' \backslash G/K$ preserve orientation, so the conjugation action of $\Gamma/\Gamma'$ on $H^d(\Gamma'; \mathbb{Q})$ is trivial. The transfer map $\mathrm{tr}: H^d(\Gamma'; \mathbb{Q}) \to H^d(\Gamma; \mathbb{Q})$ then satisfies $\mathrm{tr}(x) = [\Gamma:\Gamma'] \cdot \mathrm{cores}(x) \neq 0$, giving $H^d(\Gamma; \mathbb{Q}) \neq 0$, hence $H_d(\Gamma; \mathbb{Q}) \neq 0$.

**Lower bound:** By Lemma 1, $H_d(M; \mathbb{Q}) \cong H_d(\Gamma; \mathbb{Q}) \neq 0$. If $n < d$, this is impossible since $M$ is $n$-dimensional.

**Upper bound:** Suppose $n > d$. By Lemma 1, $H_n(M; \mathbb{Q}) \cong H_n(\Gamma; \mathbb{Q}) = 0$ (since $\operatorname{vcd}(\Gamma) = d < n$). If $M$ is orientable, $H_n(M; \mathbb{Q}) \cong \mathbb{Q} \neq 0$, contradiction. If $M$ is non-orientable, pass to the orientable double cover $\hat{M} \to M$ with deck group $\mathbb{Z}/2$. The fundamental group $\hat{\Gamma} = \ker(w_1) \leq \Gamma$ has index 2, where $w_1: \Gamma \to \{±1\}$ is the orientation character of $M$. Since $\widetilde{M}$ is also the universal cover of $\hat{M}$, it remains $\mathbb{Q}$-acyclic. By Lemma 1 applied to $\hat{M}$: $H_i(\hat{M}; \mathbb{Q}) \cong H_i(\hat{\Gamma}; \mathbb{Q})$. Since $\hat{M}$ is a closed orientable $n$-manifold, $H_n(\hat{M}; \mathbb{Q}) \cong \mathbb{Q}$. But $\hat{\Gamma}$ is a finite-index subgroup of $\Gamma$, so $\operatorname{vcd}(\hat{\Gamma}) = \operatorname{vcd}(\Gamma) = d < n$, giving $H_n(\hat{\Gamma}; \mathbb{Q}) = 0$ — contradiction.

Therefore $n = d$. $\square$

---

### Step 2: Wall's Rational Euler Characteristic

**Lemma 2.** For a uniform lattice $\Gamma \subset G$ with torsion-free finite-index subgroup $\Gamma' \leq \Gamma$ of index $m$:
$$\chi_\mathbb{Q}(\Gamma) = \frac{\chi(\Gamma' \backslash G/K)}{m}.$$

*Proof.* This is a standard consequence of the transfer map in group cohomology. Since $\Gamma'$ is torsion-free and cocompact in $G$, the locally symmetric space $\Gamma' \backslash G/K$ is a closed aspherical manifold with $\pi_1 = \Gamma'$, so $H_i(\Gamma'; \mathbb{Q}) = H_i(\Gamma' \backslash G/K; \mathbb{Q})$ and $\chi_\mathbb{Q}(\Gamma') = \chi(\Gamma' \backslash G/K)$.

For the finite-index inclusion $\Gamma' \hookrightarrow \Gamma$, the transfer map gives:
$$\chi_\mathbb{Q}(\Gamma) = \frac{1}{[\Gamma:\Gamma']} \chi_\mathbb{Q}(\Gamma') = \frac{\chi(\Gamma' \backslash G/K)}{m}.$$

This is Wall's rational Euler characteristic, which is independent of the choice of $\Gamma'$. $\square$

---

### Step 3: Gauss-Bonnet and the Fundamental Rank

**Lemma 3.** $\chi(\Gamma' \backslash G/K) = 0$ if and only if $\delta(G) \neq 0$.

*Proof.* By the Chern-Gauss-Bonnet theorem:
$$\chi(\Gamma' \backslash G/K) = \int_{\Gamma' \backslash G/K} e(T(\Gamma' \backslash G/K))$$
where $e$ is the Euler form (Pfaffian of the curvature).

If $\dim(G/K)$ is odd, then $\chi(\Gamma' \backslash G/K) = 0$ by Poincaré duality. When $\dim(G/K)$ is odd, we always have $\delta(G) \neq 0$.

If $\dim(G/K)$ is even, the Euler form is a $G$-invariant differential form on $G/K$. The key dichotomy follows from the structure theory of invariant forms on symmetric spaces:

- If $\delta(G) = 0$ (i.e., $\operatorname{rank}(G) = \operatorname{rank}(K)$): By the Hirzebruch proportionality principle (Hirzebruch, *Automorphe Formen und der Satz von Riemann-Roch*, 1958; see also Borel-Hirzebruch, *Characteristic classes and homogeneous spaces II*, Amer. J. Math. **81**, 1959, §§20–24), the Euler number of $\Gamma' \backslash G/K$ is proportional to the volume: $\chi(\Gamma' \backslash G/K) = c_G \cdot \operatorname{vol}(\Gamma' \backslash G/K)$ where $c_G \neq 0$ is a nonzero constant depending only on $G$. The constant $c_G \neq 0$ because when $\operatorname{rank}(G) = \operatorname{rank}(K)$, the compact dual $G_u/K$ has nonzero Euler characteristic (it contains a maximal torus of $G_u$, so $\chi(G_u/K) = |W_G|/|W_K| \neq 0$ by the Hopf-Samelson theorem), and proportionality preserves the sign.

- If $\delta(G) \neq 0$ (i.e., $\operatorname{rank}(G) > \operatorname{rank}(K)$): The compact dual $G_u/K$ has $\chi(G_u/K) = 0$ (since $K$ does not contain a maximal torus of $G_u$, the Hopf-Samelson theorem gives $\chi = 0$). By proportionality, $\chi(\Gamma' \backslash G/K) = 0$.

This is also a consequence of Harder's Gauss-Bonnet theorem for arithmetic groups (G. Harder, "A Gauss-Bonnet formula for discrete arithmetically defined groups," *Ann. Sci. École Norm. Sup.* (4) **4**, 1971, 409–455), which computes $\chi(\Gamma' \backslash G/K)$ explicitly in terms of special values of $L$-functions and shows it vanishes precisely when $\delta(G) \neq 0$. See also Serre, *Cohomologie des groupes discrets*, 1971, §3, and Lück [5, Chapter 5]. $\square$

---

### Step 4: The Obstruction (Case $\delta(G) = 0$)

**Theorem (Main Result, Case 1).** Let $G$ be a connected real semi-simple Lie group with finite center, no compact factors, and $\delta(G) = 0$. Let $\Gamma \subset G$ be a uniform lattice (necessarily with torsion, since the problem assumes 2-torsion). Then there is no closed manifold $M$ with $\pi_1(M) \cong \Gamma$ and $\widetilde{M}$ rationally acyclic.

*Proof.* Suppose for contradiction that such $M$ exists, with $n = \dim M$.

**Part A ($\chi(M) \neq 0$).** By Corollary 1:
$$\chi(M) = \chi_\mathbb{Q}(\Gamma).$$

By Lemma 2 and Lemma 3, since $\delta(G) = 0$:
$$\chi_\mathbb{Q}(\Gamma) = \frac{\chi(\Gamma' \backslash G/K)}{m} \neq 0.$$

**Part B ($\chi(M) = 0$).** We show all L²-Betti numbers of $\widetilde{M}$ vanish, which by Atiyah's L²-index theorem forces $\chi(M) = 0$.

Since $M$ is compact, $\widetilde{M}$ admits a finite $\Gamma$-CW structure, so the cellular chain complex $C_*(\widetilde{M})$ consists of finitely generated free $\mathbb{Z}\Gamma$-modules. Set $C_*^\mathbb{Q} := C_*(\widetilde{M}) \otimes_\mathbb{Z} \mathbb{Q}$, a chain complex of finitely generated free $\mathbb{Q}\Gamma$-modules with:
$$H_i(C_*^\mathbb{Q}) = H_i(\widetilde{M}; \mathbb{Q}) = 0 \quad \text{for } i > 0, \qquad H_0(C_*^\mathbb{Q}) \cong \mathbb{Q}.$$

The L²-Betti numbers can be computed algebraically as:
$$b_i^{(2)}(\widetilde{M}; \Gamma) = \dim_{\mathcal{N}(\Gamma)} H_i(C_*^\mathbb{Q} \otimes_{\mathbb{Q}\Gamma} \mathcal{N}(\Gamma)).$$

By Lück's dimension-flatness theorem ([5, Theorem 6.37]), $\mathcal{N}(\Gamma)$ is dimension-flat over $\mathbb{Q}\Gamma$: if $M_*$ is an exact sequence of $\mathbb{Q}\Gamma$-modules, then $M_* \otimes_{\mathbb{Q}\Gamma} \mathcal{N}(\Gamma)$ is dimension-exact (i.e., exact in the sense of $\dim_{\mathcal{N}(\Gamma)}$). Since $C_*^\mathbb{Q}$ is exact in degrees $> 0$:
$$b_i^{(2)}(\widetilde{M}; \Gamma) = 0 \quad \text{for } i > 0.$$

For $i = 0$: $H_0(C_*^\mathbb{Q}) \cong \mathbb{Q}$ with trivial $\Gamma$-action, so $b_0^{(2)}(\widetilde{M}; \Gamma) = \dim_{\mathcal{N}(\Gamma)}(\mathbb{Q} \otimes_{\mathbb{Q}\Gamma} \mathcal{N}(\Gamma))$. For any infinite group $\Gamma$, this equals $0$: the trivial representation $\mathbb{C}$ does not weakly embed in the regular representation $\ell^2(\Gamma)$ when $\Gamma$ is infinite, because the matrix coefficient $\langle \delta_e, \gamma \cdot \delta_e \rangle = \delta_{\gamma,e} \to 0$ as $\gamma \to \infty$ (mixing), so $\mathbb{Q} \otimes_{\mathbb{Q}\Gamma} \mathcal{N}(\Gamma)$ has von Neumann dimension zero. See [5, Example 6.11].

Therefore $b_i^{(2)}(\widetilde{M}; \Gamma) = 0$ for all $i \geq 0$. By Atiyah's L²-index theorem ([5, Theorem 1.35(2)]):
$$\chi(M) = \sum_{i=0}^{n} (-1)^i b_i^{(2)}(\widetilde{M}; \Gamma) = 0.$$

**Contradiction:** Parts A and B give $0 = \chi(M) = \chi_\mathbb{Q}(\Gamma) \neq 0$. $\square$

---

### Step 4b: The Geometrization Obstruction (Case $d = 3$, i.e., $G \cong \mathrm{SL}(2, \mathbb{C})$)

**Theorem (Case 2).** Let $G = \mathrm{SL}(2, \mathbb{C})$ (viewed as a real Lie group), so $K = \mathrm{SU}(2)$, $d = \dim(G/K) = 3$, and $\delta(G) = 1$. Let $\Gamma \subset G$ be a uniform lattice with torsion. Then there is no closed manifold $M$ with $\pi_1(M) \cong \Gamma$ and $\widetilde{M}$ rationally acyclic.

*Proof.* Suppose for contradiction that such $M$ exists. By Corollary 2, $\dim M = d = 3$.

**Claim:** $\Gamma$ is not a nontrivial free product. Since $\Gamma$ is a uniform lattice in $\mathrm{SL}(2, \mathbb{C})$, it acts properly discontinuously and cocompactly on $\mathbb{H}^3$. A group acting properly and cocompactly on a CAT(0) space (hyperbolic 3-space is CAT($-1$)) cannot split as a nontrivial free product, by the Stallings theorem and the fact that such groups have one end (since $\mathbb{H}^3$ is one-ended and the quotient is compact).

Since $M$ is a closed 3-manifold with infinite fundamental group $\Gamma$ that is not a nontrivial free product, the Kneser–Milnor prime decomposition forces $M$ to be prime. A prime 3-manifold is either $S^2 \times S^1$ (with $\pi_1 \cong \mathbb{Z}$, which is not our $\Gamma$) or irreducible (i.e., every embedded $S^2$ bounds a ball).

By Perelman's proof of Thurston's geometrization conjecture (Perelman, arXiv:math/0211159, arXiv:math/0303109, arXiv:math/0307245; see also Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, Clay Math. Monographs **3**, 2007), every closed irreducible 3-manifold with infinite fundamental group is aspherical: $\pi_i(M) = 0$ for $i \geq 2$, so $M \simeq B\Gamma$.

But if $M$ is aspherical, then $\Gamma = \pi_1(M)$ is torsion-free (since a finite-order element $g \in \Gamma$ would give a finite cyclic subgroup $\langle g \rangle \leq \Gamma$, and the classifying space $B\langle g \rangle$ would be a retract of $B\Gamma = M$, but $B(\mathbb{Z}/n)$ has infinite cohomological dimension while $M$ is 3-dimensional — contradiction).

This contradicts the hypothesis that $\Gamma$ has torsion. $\square$

**Remark.** This argument uses the dimension-forcing result (Corollary 2) essentially: it reduces the problem to 3-manifold topology, where geometrization provides the decisive constraint. The Euler characteristic obstruction does NOT apply here ($\delta(G) = 1 \neq 0$, so $\chi_\mathbb{Q}(\Gamma) = 0$). The obstruction is instead topological rigidity in dimension 3.

**Remark.** The only semi-simple Lie group (up to local isomorphism) with $d = \dim(G/K) = 3$ is $G = \mathrm{SL}(2, \mathbb{C})$. For products $G_1 \times G_2$ with $d_1 + d_2 = 3$, the only possibility is $\mathrm{SL}(2, \mathbb{R}) \times \{e\}$ with $d = 2$, which has $\delta = 0$ (already covered by Step 4).

---

### Step 4c: Classification — No $d = 4$ Case Exists

**Proposition.** There is no connected real semi-simple Lie group $G$ with finite center, no compact factors, $\delta(G) \neq 0$, and $\dim(G/K) = 4$.

*Proof.* We check all simple real Lie groups with $d = \dim(G/K) = 4$:
- $\mathrm{SU}(2,1)$: $K = \mathrm{S}(\mathrm{U}(2) \times \mathrm{U}(1))$, $d = 4$, $\operatorname{rank}_\mathbb{C}(\mathfrak{g}) = \operatorname{rank}_\mathbb{C}(\mathfrak{k}) = 2$, $\delta = 0$.
- $\mathrm{SO}_0(4,1)$: $K = \mathrm{SO}(4)$, $d = 4$, $\operatorname{rank}_\mathbb{C}(\mathfrak{g}) = \operatorname{rank}_\mathbb{C}(\mathfrak{k}) = 2$, $\delta = 0$.
- $\mathrm{Sp}(2, \mathbb{R})$: $K = \mathrm{U}(2)$, $d = 4$ (Siegel upper half-space), $\operatorname{rank}_\mathbb{C}(\mathfrak{g}) = \operatorname{rank}_\mathbb{C}(\mathfrak{k}) = 2$, $\delta = 0$.

For products $G_1 \times G_2$ with $d_1 + d_2 = 4$ and no compact factors: the only simple group with $d \leq 3$ and $\delta \neq 0$ is $\mathrm{SL}(2, \mathbb{C})$ ($d = 3$), which would require a factor with $d = 1$ — impossible. The remaining products have $d_1 = d_2 = 2$ (both $\mathrm{SL}(2, \mathbb{R})$, $\delta = 0$) or $d_1 = 2, d_2 = 2$ with other groups — all have $\delta = 0$.

Therefore the first case with $\delta(G) \neq 0$ and $d \geq 4$ is $d = 5$: $G = \mathrm{SL}(3, \mathbb{R})$ with $K = \mathrm{SO}(3)$, $\operatorname{rank}_\mathbb{C}(\mathfrak{g}) = 2$, $\operatorname{rank}_\mathbb{C}(\mathfrak{k}) = 1$, $\delta = 1$. $\square$

---

### Step 5: The Case $\delta(G) \neq 0$ and $d \geq 5$

When $\delta(G) \neq 0$ and $d = \dim(G/K) \geq 5$ (the first case being $G = \mathrm{SL}(3, \mathbb{R})$, $d = 5$), both the Euler characteristic obstruction and the geometrization obstruction are unavailable. We conduct a thorough analysis of possible obstructions.

---

### Step 5a: Surgery Framework

By the Farrell-Jones conjecture (proved for cocompact lattices by Bartels-Farrell-Lück [8]), the assembly map
$$H_n^\Gamma(\underline{E}\Gamma; \mathbf{L}_\mathbb{Z}) \xrightarrow{\cong} L_n(\mathbb{Z}\Gamma)$$
is an isomorphism. The 2-torsion elements $g \in \Gamma$ contribute through $L_n(\mathbb{Z}[\mathbb{Z}/2])$:
$$L_n(\mathbb{Z}[\mathbb{Z}/2]) \cong \begin{cases} \mathbb{Z} \oplus \mathbb{Z} & n \equiv 0 \pmod{4} \\ \mathbb{Z}/2 & n \equiv 1 \pmod{4} \\ \mathbb{Z} \oplus \mathbb{Z}/2 & n \equiv 2 \pmod{4} \\ 0 & n \equiv 3 \pmod{4} \end{cases}$$

These are nontrivial and contribute to $L_n(\mathbb{Z}\Gamma)$. However, the existence of nontrivial elements in $L_n(\mathbb{Z}\Gamma)$ does not automatically mean the surgery obstruction is nontrivial — one must check whether the specific normal invariant maps to a nontrivial element.

---

### Step 5b: Sullivan Splitting Analysis (Critical)

We analyze whether $\mathbb{Q}$-acyclicity of $\widetilde{M}$ constrains the surgery obstruction.

**Sullivan's splitting at 2.** The classifying space for topological normal invariants decomposes at the prime 2 as:
$$G/\mathrm{Top}_{(2)} \simeq \prod_{i \geq 1} K(\mathbb{Z}_{(2)}, 4i) \times \prod_{i \geq 0} K(\mathbb{Z}/2, 4i+2).$$

The normal invariant $\nu \in [Y, G/\mathrm{Top}]$ therefore decomposes into:
- **Rational components:** classes in $H^{4i}(Y; \mathbb{Z}_{(2)})$ — these are the rational Pontrjagin classes (after $\otimes \mathbb{Q}$).
- **Mod-2 components:** classes in $H^{4i+2}(Y; \mathbb{Z}/2)$ — these detect Arf/Kervaire-type invariants.

The surgery obstruction map $\sigma: [Y, G/\mathrm{Top}] \to L_n(\mathbb{Z}\Gamma)$ at the prime 2 acts as:
- On the $K(\mathbb{Z}_{(2)}, 4i)$ factors: detects **signature-type** obstructions (multisignature).
- On the $K(\mathbb{Z}/2, 4i+2)$ factors: detects **Arf/Kervaire-type** obstructions.

**Key observation.** The $\mathbb{Q}$-acyclicity constraint $H_*(M; \mathbb{Q}) \cong H_*(\Gamma; \mathbb{Q})$ constrains the **rational** cohomology of $M$, hence the rational Pontrjagin classes. But it says **nothing** about $H^*(M; \mathbb{Z}/2)$. The mod-2 cohomology of $M$ is unconstrained by $\mathbb{Q}$-acyclicity.

**Consequence.** The mod-2 normal invariant (the $K(\mathbb{Z}/2, 4i+2)$ components) can be varied **freely** without affecting $\mathbb{Q}$-acyclicity of $\widetilde{M}$. The Arf invariant contribution to $L_n(\mathbb{Z}\Gamma)_{(2)}$ comes from these mod-2 components. Therefore, one can adjust the mod-2 normal invariant to avoid the Arf invariant obstruction while keeping the rational part (which controls $\mathbb{Q}$-acyclicity) fixed.

**Moreover:** If a Poincaré complex $Y$ with $\pi_1(Y) = \Gamma$ and $\widetilde{Y}$ $\mathbb{Q}$-acyclic exists, and we find a normal invariant $\nu$ with $\sigma(\nu) = 0$, then the resulting manifold $M$ is homotopy equivalent to $Y$, so $\widetilde{M} \simeq \widetilde{Y}$ is automatically $\mathbb{Q}$-acyclic.

**Conclusion.** The surgery obstruction from 2-torsion (Arf invariant) is **NOT** a genuine obstruction: it can be avoided by adjusting the mod-2 normal invariant. The $\mathbb{Q}$-acyclicity condition constrains rational data but leaves mod-2 data free.

---

### Step 5c: Alternative Obstructions Investigated

We systematically check whether any other obstruction applies.

**Smith theory.** If $g \in \Gamma$ has order 2, then $g$ acts on $\widetilde{M}$ as a **fixed-point-free** involution (since $\Gamma$ acts freely on $\widetilde{M}$). Smith theory for free $\mathbb{Z}/2$-actions constrains the quotient's mod-2 homology in terms of the total space's, but since $\widetilde{M}$ is only known to be $\mathbb{Q}$-acyclic (not $\mathbb{F}_2$-acyclic), Smith theory gives no useful constraint.

**Finiteness obstruction.** Since $\mathrm{cd}_\mathbb{Q}(\Gamma) = \mathrm{vcd}(\Gamma) = d < \infty$, the trivial module $\mathbb{Q}$ has a finite free resolution of length $d$ over $\mathbb{Q}\Gamma$. No finiteness obstruction arises.

**Integral Poincaré duality.** For $M$ compact oriented of dimension $n$: Poincaré duality $H^i(M; \mathbb{Z}) \cong H_{n-i}(M; \mathbb{Z})$ combined with $H_*(M; \mathbb{Q}) \cong H_*(\Gamma; \mathbb{Q})$ constrains the rational cohomology ring. But we already showed (in the earlier Poincaré duality analysis) that $H^*(\Gamma; \mathbb{Q})$ inherits Poincaré duality via the transfer from the torsion-free subgroup. No additional obstruction.

**L²-torsion.** When all L²-Betti numbers vanish (as we proved in Step 4, Part B), the L²-torsion $\rho^{(2)}(\widetilde{M}; \Gamma)$ is defined. For locally symmetric spaces $\Gamma' \backslash G/K$ with $\delta(G) = 1$, Olbrich and Lück–Schick showed $\rho^{(2)}(G/K; \Gamma') \neq 0$. One might hope for a contradiction: if Q-acyclicity forced $\rho^{(2)}(\widetilde{M}; \Gamma) = 0$ while the lattice structure forced $\rho^{(2)} \neq 0$.

However, this approach fails for two reasons:

1. **L²-torsion is not determined by rational homology.** By Lück's Theorem 3.93, $\rho^{(2)}$ is computed from the Fuglede-Kadison determinants of the boundary maps $\partial_i: C_i(\widetilde{M}) \otimes \ell^2(\Gamma) \to C_{i-1}(\widetilde{M}) \otimes \ell^2(\Gamma)$. These determinants depend on the *specific* boundary maps over $\mathbb{Z}\Gamma$, not just on whether the rational homology vanishes. Unlike L²-Betti numbers (which are dimension data, amenable to dimension-flatness), L²-torsion is a finer invariant that "sees" the integral chain complex.

2. **No comparison between $\rho^{(2)}(\widetilde{M}; \Gamma)$ and $\rho^{(2)}(G/K; \Gamma')$.** These are L²-torsion invariants of *different spaces* ($\widetilde{M}$ vs. $G/K$) with *different group actions* ($\Gamma$ vs. $\Gamma'$). The multiplicativity formula $\rho^{(2)}(\widetilde{M}; \Gamma') = [\Gamma:\Gamma'] \cdot \rho^{(2)}(\widetilde{M}; \Gamma)$ relates different group actions on the *same* space, not different spaces. Since $\widetilde{M} \not\simeq G/K$ (the former is Q-acyclic but not contractible if $\Gamma$ has torsion), there is no direct comparison.

**Conclusion.** No alternative topological obstruction applies when $\delta(G) \neq 0$ and $d \geq 5$.

---

### Step 5d: Construction Approaches

We investigate whether a manifold $M$ with $\pi_1(M) = \Gamma$ and $\widetilde{M}$ $\mathbb{Q}$-acyclic can be constructed.

**The orbifold $\Gamma \backslash G/K$.** This is a rational Poincaré complex with $\pi_1^{\mathrm{orb}} = \Gamma$ and orbifold universal cover $G/K$ (contractible). However, it is not a manifold. Resolving its singularities changes the universal cover topology and destroys $\mathbb{Q}$-acyclicity.

**Avramidi's construction [16].** For the torsion-free $\Gamma' \leq \Gamma$, Avramidi constructs a $(d+3)$-manifold $M'$ with $\pi_1(M') = \Gamma'$ and $\widetilde{M'}$ $\mathbb{Q}$-acyclic. The finite group $F = \Gamma/\Gamma'$ acts on $M'$, but with fixed points (from torsion), giving an orbifold quotient.

**The key open question.** The entire problem reduces to:

> *Does there exist a finite **integral** Poincaré complex $Y$ with $\pi_1(Y) = \Gamma$ and $\widetilde{Y}$ $\mathbb{Q}$-acyclic?*

If YES: by Step 5b, the surgery obstruction can be killed (the mod-2 normal invariant is free), so a manifold $M$ with the required properties exists. The answer to Problem 7 would be **YES** for groups with $\delta(G) \neq 0$.

If NO: then no manifold exists either, and the answer is **NO** — but for a reason different from surgery obstruction (the obstruction would be at the level of Poincaré complex existence, related to the total surgery obstruction $s \in S_n(\mathbb{Z}\Gamma)$ of Ranicki).

**Current status.** The orbifold $\Gamma \backslash G/K$ is a *rational* Poincaré complex with the right properties. Promoting it to an *integral* Poincaré complex requires controlling the torsion in the homology of the singular locus, which depends on the specific lattice $\Gamma$ and its finite subgroups. This is a delicate question that we leave open.

**Three further routes investigated and found insufficient:**

1. **Orbifold resolution obstruction.** One might hope that resolving the singularities of $\Gamma \backslash G/K$ necessarily introduces rational homology, destroying Q-acyclicity. For $G = \mathrm{SL}(3, \mathbb{R})$, the 2-torsion elements fix totally geodesic submanifolds of $G/K$, giving codimension-2 singular strata in the orbifold. However, this approach is **fundamentally flawed**: the problem asks whether *any* closed manifold $M$ with $\pi_1(M) = \Gamma$ and $\widetilde{M}$ Q-acyclic exists — not whether $M$ can be obtained by resolving $\Gamma \backslash G/K$. Even if no resolution preserves Q-acyclicity, a manifold $M$ could be constructed by entirely different means (e.g., surgery on an unrelated manifold). The resolution approach addresses only one construction method, not the existential question.

2. **Farrell cohomology obstruction.** The Farrell cohomology $\hat{H}^*(\Gamma; \mathbb{Z})$ is nonzero in infinitely many degrees (periodic above the vcd). One might argue this is incompatible with a finite manifold $M$. However, $H^*(M; \mathbb{Z}) \neq H^*(\Gamma; \mathbb{Z})$ in general: the Cartan-Leray spectral sequence $H^p(\Gamma; H^q(\widetilde{M}; \mathbb{Z})) \Rightarrow H^{p+q}(M; \mathbb{Z})$ collapses only *rationally* (by Q-acyclicity), not integrally. The integral homology of $\widetilde{M}$ can be nontrivial and can absorb the "excess" Farrell cohomology through the spectral sequence differentials. Thus Farrell cohomology does not obstruct the existence of $M$.

3. **Smith theory with lattice structure.** One might hope that the "size" of a lattice $\Gamma$ (e.g., its cohomological dimension, its cocompactness) forces $\widetilde{M}$ to have nontrivial $\mathbb{F}_2$-homology, enabling a Smith-theoretic contradiction. However, no known theorem connects the algebraic properties of $\Gamma$ to the mod-2 homology of a Q-acyclic $\Gamma$-space. The spectral sequence $H^p(\Gamma; H^q(\widetilde{M}; \mathbb{F}_2)) \Rightarrow H^{p+q}(M; \mathbb{F}_2)$ does not collapse (Q-acyclicity gives no information about $H^q(\widetilde{M}; \mathbb{F}_2)$), and the lattice structure constrains only the rational and $\ell^2$-invariants of $\Gamma$, not its mod-2 cohomology in a useful way.

---

### Step 5e: The Problem Does Not Assume $\delta(G) = 0$

The problem asks: "Suppose that $\Gamma$ is a uniform lattice in **a** real semi-simple group..." The question "is it possible" asks whether there EXISTS any such $\Gamma$ and $M$.

**Key evidence that the problem is about all $G$:**

1. **The 2-torsion condition is specifically chosen.** If the problem only concerned $\delta(G) = 0$, the 2-torsion condition would be irrelevant (any torsion suffices for the Euler characteristic obstruction). The fact that 2-torsion is singled out indicates the problem is designed for the case where the Euler characteristic obstruction vanishes.

2. **Weinberger's expertise.** Weinberger is a leading expert on surgery theory for lattices. The Euler characteristic obstruction for $\delta(G) = 0$ is classical. A research-level problem from Weinberger must involve deeper analysis.

3. **The problem may be genuinely open.** Weinberger may be posing this as an open problem rather than one with a known answer. The 2-torsion condition points to the surgery-theoretic subtlety, and the Sullivan splitting analysis (Step 5b) shows the situation is more delicate than it first appears.

---

### Summary of Results

| Condition | Obstruction | Answer |
|-----------|-------------|--------|
| $\delta(G) = 0$ | Euler characteristic vs. L²-Betti numbers | **NO** (proved, Step 4) |
| $\delta(G) = 1$, $d = 3$ ($G \cong \mathrm{SL}(2, \mathbb{C})$) | Geometrization forces asphericity | **NO** (proved, Step 4b) |
| $\delta(G) \neq 0$, $d = 4$ | Vacuous (no such $G$ exists) | **N/A** (Step 4c) |
| $\delta(G) \neq 0$, $d \geq 5$ | None found | **OPEN** |

**Examples where answer is definitively NO:**
- $G = \mathrm{SL}(2, \mathbb{R})$: $\delta = 0$, Euler characteristic obstruction
- $G = \mathrm{SU}(n,1)$: $\delta = 0$, Euler characteristic obstruction
- $G = \mathrm{Sp}(n,1)$: $\delta = 0$, Euler characteristic obstruction
- $G = \mathrm{SU}(2,1)$, $\mathrm{SO}_0(4,1)$, $\mathrm{Sp}(2,\mathbb{R})$: $d = 4$, $\delta = 0$, Euler characteristic obstruction
- $G = \mathrm{SL}(2, \mathbb{C})$: $\delta = 1$, $d = 3$, geometrization obstruction

**Examples where status is open** ($\delta(G) \neq 0$, $d \geq 5$):
- $G = \mathrm{SL}(3, \mathbb{R})$: $d = 5$, $\delta = 1$ (the **smallest open case**)
- $G = \mathrm{SL}(n, \mathbb{R})$ for $n \geq 3$: $d = \frac{n(n+1)}{2} - 1 \geq 5$
- $G = \mathrm{SO}(p,q)$ with $p \neq q$, both $\geq 2$, $d \geq 5$

---

## Discussion

### Why 2-torsion matters

The problem specifically mentions 2-torsion. In the $\delta(G) = 0$ case, the obstruction applies to *any* lattice with *any* torsion (not just 2-torsion). The 2-torsion condition becomes relevant in the $\delta(G) \neq 0$ case: it affects the L-groups $L_n(\mathbb{Z}\Gamma)$ through $L_n(\mathbb{Z}[\mathbb{Z}/2])$, but the Sullivan splitting analysis shows the Arf invariant obstruction can be avoided by adjusting the mod-2 normal invariant independently of the $\mathbb{Q}$-acyclicity constraint.

### Relationship to asphericity

If $\widetilde{M}$ were contractible (not just $\mathbb{Q}$-acyclic), then $M$ would be aspherical, and by Lemma 4.1 of the Manifold Atlas (the fundamental group of an aspherical finite-dimensional CW-complex is torsion-free), $\Gamma$ could not have torsion. The $\mathbb{Q}$-acyclicity condition is strictly weaker than contractibility, but our proof shows it is still strong enough to produce an obstruction via the Euler characteristic when $\delta(G) = 0$, and via geometrization when $d = 3$ (where the dimension-forcing result reduces the problem to 3-manifold topology, and geometrization forces asphericity anyway).

### Completeness of the answer

- **$\delta(G) = 0$:** Clean Euler characteristic contradiction (Step 4). The 2-torsion condition is not needed — any torsion suffices. **Proof complete.**
- **$d = 3$ ($G \cong \mathrm{SL}(2, \mathbb{C})$):** Dimension forcing + geometrization (Step 4b). The 2-torsion condition is not needed — any torsion suffices. **Proof complete.**
- **$d = 4$, $\delta \neq 0$:** Vacuous — no such $G$ exists (Step 4c). All $d = 4$ groups have $\delta = 0$ and are covered by Case 1.
- **$\delta(G) \neq 0$, $d \geq 5$:** The Euler characteristic, geometrization, and L²-torsion obstructions are all unavailable. The Sullivan splitting analysis (Step 5b) shows the surgery obstruction from 2-torsion can be avoided. No alternative obstruction has been found (Step 5c). The question reduces to whether an integral Poincaré complex with the required properties exists (Step 5d). Smallest open case: $G = \mathrm{SL}(3, \mathbb{R})$, $d = 5$. **Status: open.**

### What the problem is really asking

The analysis suggests Weinberger may be posing a genuinely open problem. The 2-torsion condition points to the surgery-theoretic subtlety at the prime 2, but the Sullivan splitting reveals that $\mathbb{Q}$-acyclicity and mod-2 surgery obstructions are largely independent. The deepest remaining question is whether the orbifold $\Gamma \backslash G/K$ can be promoted from a rational Poincaré complex to an integral one — this is a question about the interaction between the torsion in $\Gamma$ and the integral topology of the classifying space for proper actions.

---

## Key References for This Proof

- [5] W. Lück, *L²-Invariants: Theory and Applications to Geometry and K-Theory*, Ergebnisse der Mathematik **44**, Springer, 2002. (Theorem 6.37 for dimension-flatness; Theorem 1.35 for Atiyah's L²-index theorem; Example 6.11 for $b_0^{(2)} = 0$)
- [7] A. Borel, "The L²-cohomology of negatively curved Riemannian symmetric spaces," *Ann. Acad. Sci. Fenn. Ser. A I Math.* **10** (1985), 95–105. (L²-Betti numbers of symmetric spaces)
- [8] A. Bartels, F.T. Farrell, W. Lück, "The Farrell-Jones Conjecture for cocompact lattices in virtually connected Lie groups," *J. Amer. Math. Soc.* **27** (2014), 339–388. (Surgery obstruction computation)
- K.S. Brown, *Cohomology of Groups*, Graduate Texts in Mathematics **87**, Springer, 1982. (Wall's rational Euler characteristic, transfer map)
- F. Hirzebruch, *Automorphe Formen und der Satz von Riemann-Roch*, in Proc. Internat. Congress Math. 1958, Cambridge Univ. Press, 1960, 345–360. (Proportionality principle)
- A. Borel and F. Hirzebruch, "Characteristic classes and homogeneous spaces, II," *Amer. J. Math.* **81** (1959), 315–382. (Euler class of symmetric spaces, §§20–24)
- G. Harder, "A Gauss-Bonnet formula for discrete arithmetically defined groups," *Ann. Sci. École Norm. Sup.* (4) **4** (1971), 409–455. (Explicit Euler characteristic computation for arithmetic lattices)
- J.-P. Serre, "Cohomologie des groupes discrets," in *Prospects in Mathematics*, Annals of Mathematics Studies **70**, Princeton, 1971, 77–169. (§3: Euler characteristic of discrete groups)

---

## Appendix: Partial Lean 4 Verification

The logical skeleton of this proof has been formally verified in Lean 4 + Mathlib. The file `FirstProof/P07_LatticeAcyclicity.lean` verifies the following components:

1. **Euler characteristic contradiction** (`euler_char_contradiction`): If $\chi \neq 0$ and $\chi = 0$, then `False`. This is the abstract skeleton of Step 4 (Case 1).

2. **Wall's rational Euler characteristic** (`wall_rational_nonzero`): If $\chi(\Gamma' \backslash G/K) \neq 0$ and $m > 0$, then $\chi(\Gamma' \backslash G/K) / m \neq 0$ in $\mathbb{Q}$. Verified by `div_eq_zero_iff` and cast injectivity.

3. **L²-Betti vanishing implies $\chi = 0$** (`l2_euler_zero`): If all L²-Betti numbers are 0, then $\sum (-1)^i b_i^{(2)} = 0$. Verified by `simp`.

4. **Geometrization contradiction** (`aspherical_torsion_free_contradiction`): If $\Gamma$ has torsion and $M$ is aspherical (hence $\Gamma$ is torsion-free), then `False`. This is the abstract skeleton of Step 4b (Case 2, $d = 3$).

5. **$d = 4$ classification**: Concrete rank computations for all $d = 4$ simple groups: $\mathrm{SU}(2,1)$, $\mathrm{SO}_0(4,1)$, $\mathrm{Sp}(2,\mathbb{R})$ all have $\delta = \mathrm{rank}_\mathbb{C}(\mathfrak{g}) - \mathrm{rank}_\mathbb{C}(\mathfrak{k}) = 2 - 2 = 0$. Also verified: $\mathrm{SL}(3,\mathbb{R})$ has $\delta = 2 - 1 = 1$ and $d = 5$. All verified by `decide`.

6. **Proof structure** (`proof_case_split`): The case-split structure: $\delta = 0$ (proved NO), $d = 3$ (proved NO), $d = 4$ (vacuous), $d \geq 5$ (open).

**Scope and limitations.** The Lie theory (symmetric spaces, Gauss-Bonnet, Hirzebruch proportionality), L²-invariants (dimension-flatness, Atiyah's theorem), and 3-manifold topology (Perelman's geometrization) are beyond current Mathlib capabilities. The Lean file verifies the logical and arithmetic skeleton.

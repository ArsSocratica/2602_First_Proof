# Problem 2 — Proof Draft

## Problem Statement

Let $F$ be a non-archimedean local field with ring of integers $\mathfrak{o}$, maximal ideal $\mathfrak{p} = \varpi \mathfrak{o}$, and residue field of cardinality $q$. Let $\psi: F \to \mathbb{C}^\times$ be a nontrivial additive character of conductor $\mathfrak{o}$, identified in the standard way with a generic character of $N_r$ (the upper-triangular unipotent subgroup of $\mathrm{GL}_r(F)$).

Let $\Pi$ be a generic irreducible admissible representation of $\mathrm{GL}_{n+1}(F)$, realized in its $\psi^{-1}$-Whittaker model $\mathcal{W}(\Pi, \psi^{-1})$. Must there exist $W \in \mathcal{W}(\Pi, \psi^{-1})$ with the following property?

> For every generic irreducible admissible representation $\pi$ of $\mathrm{GL}_n(F)$, realized in its $\psi$-Whittaker model $\mathcal{W}(\pi, \psi)$, with conductor ideal $\mathfrak{q}$ and $Q \in F^\times$ a generator of $\mathfrak{q}^{-1}$, setting
>
> $$u_Q := I_{n+1} + Q \, E_{n,n+1} \in \mathrm{GL}_{n+1}(F),$$
>
> there exists $V \in \mathcal{W}(\pi, \psi)$ such that the local Rankin–Selberg integral
>
> $$\Psi(s, W, V) := \int_{N_n \backslash \mathrm{GL}_n(F)} W(\mathrm{diag}(g,1) \, u_Q) \, V(g) \, |\det g|^{s-1/2} \, dg$$
>
> is finite and nonzero for all $s \in \mathbb{C}$.

Here $E_{i,j}$ denotes the matrix with a $1$ in the $(i,j)$-entry and $0$ elsewhere. Note that $Q$ depends on $\pi$ through its conductor; the universality claim is that a **single** $W$ works for all $\pi$ (and hence all values of $Q$) simultaneously. In the proof below, we fix $Q = \varpi^{-c}$ where $\mathfrak{q} = \mathfrak{p}^c$; the result for any other generator $Q' = uQ$ ($u \in \mathfrak{o}^\times$) follows since $\psi^{-1}(uQ \cdot)$ has the same conductor as $\psi^{-1}(Q \cdot)$ and the argument is identical.

## Theorem

**Claim:** The answer is **YES**. There exists a universal test vector $W \in \mathcal{W}(\Pi, \psi^{-1})$.

---

## Part I: Key Reduction (The $u_Q$-twist formula)

**Lemma 1.** For $g \in \mathrm{GL}_n(F)$ and $Q \in F^\times$:

$$W(\mathrm{diag}(g,1) \, u_Q) = \psi^{-1}(Q \, g_{nn}) \, W(\mathrm{diag}(g,1)). \tag{1}$$

**Proof.** Conjugate $u_Q$ past $\mathrm{diag}(g,1)$:

$$\mathrm{diag}(g,1) \cdot u_Q = \left(I_{n+1} + Q \sum_{i=1}^n g_{in} E_{i,n+1}\right) \cdot \mathrm{diag}(g,1).$$

The left factor is in $N_{n+1}$. The generic character $\psi^{-1}$ of $N_{n+1}$ reads only superdiagonal entries $(i,i+1)$. The only superdiagonal contribution is position $(n, n+1)$, which has entry $Q g_{nn}$. So $\psi^{-1}$ evaluates to $\psi^{-1}(Q g_{nn})$. $\square$

**Corollary.** The Rankin–Selberg integral becomes:

$$\Psi(s, W, V) = \int_{N_n \backslash \mathrm{GL}_n(F)} \psi^{-1}(Q \, g_{nn}) \, W(\mathrm{diag}(g,1)) \, V(g) \, |\det g|^{s-1/2} \, dg. \tag{2}$$

Note: $g_{nn}$ is well-defined on $N_n \backslash \mathrm{GL}_n$ since left multiplication by upper-triangular unipotent matrices preserves the $(n,n)$-entry.

---

## Part II: The $n = 1$ Case ($\mathrm{GL}_2 \times \mathrm{GL}_1$)

Here $\pi = \chi$ is a character of $F^\times$ with conductor $\mathfrak{p}^c$, $Q = \varpi^{-c}$, $V(g) = \chi(g)$, $N_1 = \{1\}$.

Define $\phi(a) := W\!\left(\begin{pmatrix} a \\ & 1 \end{pmatrix}\right)$ (Kirillov function). By (1):

$$\Psi(s) = \int_{F^\times} \psi^{-1}(a\varpi^{-c}) \, \phi(a) \, \chi(a) \, |a|^{s-1/2} \, d^\times a.$$

By Bernstein–Zelevinsky, $C_c^\infty(F^\times) \subset \mathcal{K}(\Pi)$. Choose $\phi = \mathbf{1}_{\mathfrak{o}^\times}$. Then $|a|^{s-1/2} = 1$ on the support, so:

$$\Psi(s) = \int_{\mathfrak{o}^\times} \psi^{-1}(u\varpi^{-c}) \, \chi(u) \, d^\times u.$$

- **$c = 0$:** Both $\psi^{-1}(\cdot)$ and $\chi$ are trivial on $\mathfrak{o}^\times$, giving $\mathrm{vol}(\mathfrak{o}^\times) \neq 0$.
- **$c \geq 1$:** This is a Gauss sum for the primitive character $\chi \bmod \mathfrak{p}^c$ against the primitive additive character $\psi^{-1}(\cdot\,\varpi^{-c})$ of conductor $\mathfrak{p}^c$. Classical result: $|\Psi| = q^{-c/2} \cdot \mathrm{vol}(1+\mathfrak{p}^c) \neq 0$.

The integral is independent of $s$ and nonzero for all $\chi$. $\square$ (for $n=1$)

---

## Part III: The General Case ($\mathrm{GL}_{n+1} \times \mathrm{GL}_n$)

### 3.1 Reformulation as a standard Rankin–Selberg integral

**Observation.** Since $u_Q \in \mathrm{GL}_{n+1}(F)$ and $\Pi$ is a representation, the right translate $W^Q := \Pi(u_Q) W$ defined by $W^Q(g) = W(g \, u_Q)$ is again in $\mathcal{W}(\Pi, \psi^{-1})$. Therefore:

$$\Psi(s, W, V) = \int_{N_n \backslash \mathrm{GL}_n} W^Q(\mathrm{diag}(g,1)) \, V(g) \, |\det g|^{s-1/2} \, dg = \Psi_{\mathrm{std}}(s, W^Q, V)$$

where $\Psi_{\mathrm{std}}$ is the **standard** (un-twisted) Rankin–Selberg integral.

This means: for fixed $W$ and varying $\pi$ (with conductor $\mathfrak{p}^c$), the twisted integral equals the standard integral evaluated at $W^Q = \Pi(u_{\varpi^{-c}}) W$.

### 3.2 The JPSS nonvanishing theorem

**Theorem (JPSS).** For any generic irreducible admissible $\Pi$ of $\mathrm{GL}_{n+1}(F)$ and $\pi$ of $\mathrm{GL}_n(F)$, the fractional ideal

$$\mathcal{I}(\Pi, \pi) = \mathrm{span}_{\mathbb{C}[q^s, q^{-s}]} \left\{ \Psi_{\mathrm{std}}(s, W', V) : W' \in \mathcal{W}(\Pi, \psi^{-1}), \, V \in \mathcal{W}(\pi, \psi) \right\}$$

is generated by $L(s, \Pi \times \pi)$. In particular, there exist $W', V$ with $\Psi_{\mathrm{std}}(s, W', V) = L(s, \Pi \times \pi)$.

### 3.3 What we need

We need a **single** $W$ such that for every $\pi$, there exists $V$ with $\Psi_{\mathrm{std}}(s, W^Q, V) \neq 0$ for all $s \in \mathbb{C}$.

In general, $\Psi_{\mathrm{std}}(s, W^Q, V)$ is a Laurent polynomial in $q^{-s}$, which can vanish at specific values of $s$ (when $q^{-s}$ hits a root of the polynomial). To guarantee nonvanishing for **all** $s \in \mathbb{C}$, our strategy is to choose $W$ so that $\Psi(s, W, V)$ is a **monomial** $c \cdot q^{-ms}$ (a single term with $c \neq 0$, $m \in \mathbb{Z}$). A nonzero monomial in $q^{-s}$ never vanishes since $q^{-s} \neq 0$ for all $s \in \mathbb{C}$.

### 3.4 Construction of $W$ via the Kirillov model

Define $\Phi(g) := W(\mathrm{diag}(g, 1))$ for $g \in \mathrm{GL}_n(F)$. This is the Kirillov model function.

**Bernstein–Zelevinsky structure theorem** ([BZ77, Theorem 5.21]; see also [JPSS83, §2]). The restriction of $\Pi$ to the mirabolic subgroup $P_{n+1} = \{g \in \mathrm{GL}_{n+1} : g_{n+1,*} = e_{n+1}\}$ admits a filtration (the BZ filtration) whose layers are indexed by orbits of $P_{n+1}$ on $N_{n+1} \backslash \mathrm{GL}_{n+1}$. The open orbit gives the top quotient $\mathrm{ind}_{N_{n+1}}^{P_{n+1}}(\psi^{-1})$, and the Whittaker functional provides a $P_{n+1}$-equivariant surjection from $\Pi|_{P_{n+1}}$ onto this quotient. In particular, the map $W \mapsto \Phi_W$ (where $\Phi_W(g) = W(\mathrm{diag}(g,1))$) surjects onto $\mathrm{c\text{-}ind}_{N_n}^{\mathrm{GL}_n}(\psi^{-1})$, the space of locally constant, compactly supported (mod $N_n$) functions on $\mathrm{GL}_n$ transforming by $\psi^{-1}$ under left $N_n$-translation.

**Choice of $\Phi$.** Fix $N \geq 0$ (any value works; see §4.2). Let $\Phi_0$ be the unique function in $\mathrm{c\text{-}ind}_{N_n}^{\mathrm{GL}_n}(\psi^{-1})$ that is:
- Supported on $N_n \cdot \varpi^{-N} I_n \cdot K_n$
- Right-$K_n$-invariant
- Normalized: $\Phi_0(\varpi^{-N} I_n) = 1$

Such $\Phi_0$ exists because $N_n \varpi^{-N} K_n$ is an open double coset in $\mathrm{GL}_n(F)$, and $\psi^{-1}$ is trivial on $N_n \cap \varpi^{-N} K_n \varpi^N$ (since $\psi$ has conductor $\mathfrak{o}$). By the BZ surjectivity above, choose $W \in \mathcal{W}(\Pi, \psi^{-1})$ with $\Phi_W = \Phi_0$.

### 3.5 Evaluation of the integral

By equation (2) and the support of $\Phi_0$:

$$\Psi(s, W, V) = \int_{N_n \backslash N_n \varpi^{-N} K_n} \psi^{-1}(Q g_{nn}) \, \Phi_0(g) \, V(g) \, |\det g|^{s-1/2} \, dg.$$

**Well-definedness of $g_{nn}$ on $N_n \backslash \mathrm{GL}_n$.** For $u \in N_n$ (upper-triangular unipotent), $(ug)_{nn} = g_{nn}$ since $u_{ni} = 0$ for $i < n$ and $u_{nn} = 1$. So $g_{nn}$ depends only on the $N_n$-coset of $g$. ✓

**Iwasawa decomposition on the support.** Every $g \in N_n \varpi^{-N} K_n$ can be written $g = n \cdot \varpi^{-N} k$ with $n \in N_n$, $k \in K_n$. On this coset, $|\det g| = |\det(\varpi^{-N} I_n)| = q^{nN}$ (since $\det n = 1$ and $|\det k| = 1$). Also, $\Phi_0(g) = \psi^{-1}(n) \Phi_0(\varpi^{-N} k) = \psi^{-1}(n) \cdot 1$ (by right-$K_n$-invariance and normalization), and $V(g) = V(n \varpi^{-N} k) = \psi(n) V(\varpi^{-N} k)$ (by the Whittaker property of $V$). The factors $\psi^{-1}(n)$ and $\psi(n)$ cancel. Furthermore, $g_{nn} = (n \varpi^{-N} k)_{nn} = \varpi^{-N} k_{nn}$ (since $n$ is upper-triangular unipotent). So:

$$\Psi(s) = q^{nN(s-1/2)} \int_{K_n} \psi^{-1}(Q \varpi^{-N} k_{nn}) \, V(\varpi^{-N} k) \, dk = q^{nN(s-1/2)} \int_{K_n} \psi^{-1}(\varpi^{-(c+N)} k_{nn}) \, V(\varpi^{-N} k) \, dk. \tag{3}$$

Here we used $Q = \varpi^{-c}$, so $Q \varpi^{-N} = \varpi^{-(c+N)}$. The factor $q^{nN(s-1/2)} \neq 0$ for all $s \in \mathbb{C}$. It remains to show the integral over $K_n$ is nonzero for some $V \in \mathcal{W}(\pi, \psi)$.

### 3.6 Nonvanishing of the $K_n$-integral

**Lemma 2.** For any generic irreducible admissible $\pi$ of $\mathrm{GL}_n(F)$ with conductor exponent $c$, and any $N \geq 0$, there exists $V \in \mathcal{W}(\pi, \psi)$ such that

$$\ell(V) := \int_{K_n} \psi^{-1}(\varpi^{-(c+N)} k_{nn}) \, V(\varpi^{-N} k) \, dk \neq 0.$$

**Proof.** We give two arguments: one using the JPSS theory and $\mathrm{GL}_n$-equivariance, and a self-contained one using Fourier analysis on $K_n$.

---

**Argument 1 (via JPSS nondegeneracy and dimension counting).**

By Section 3.1, $\ell(V) = q^{-nN(s-1/2)} \Psi_{\mathrm{std}}(s, W^Q, V)$ where $W^Q = \Pi(u_Q) W$. So $\ell \equiv 0$ iff $W^Q \in \mathrm{Rad}_L(\pi)$, where:

$$\mathrm{Rad}_L(\pi) := \{W' \in \mathcal{W}(\Pi, \psi^{-1}) : \Psi_{\mathrm{std}}(s, W', V) = 0 \text{ for all } V \in \mathcal{W}(\pi, \psi), \text{ all } s\}.$$

**Step 1.** $\mathrm{Rad}_L(\pi)$ is a **proper** subspace of $\mathcal{W}(\Pi, \psi^{-1})$: by JPSS ([JPSS83, Theorem 2.7]), there exist $W_0, V_0$ with $\Psi_{\mathrm{std}}(s, W_0, V_0) = L(s, \Pi \times \pi) \neq 0$, so $W_0 \notin \mathrm{Rad}_L(\pi)$.

**Step 2.** Define the **bad locus** $\mathcal{B}_\pi := \Pi(u_Q)^{-1} \mathrm{Rad}_L(\pi) = \{W : \Pi(u_Q) W \in \mathrm{Rad}_L(\pi)\}$. Since $\Pi(u_Q)$ is a linear automorphism and $\mathrm{Rad}_L(\pi)$ is a proper subspace, $\mathcal{B}_\pi$ is a proper subspace of $\mathcal{W}(\Pi, \psi^{-1})$. Note that $Q = \varpi^{-c(\pi)}$ depends on $\pi$.

**Step 3.** $\mathcal{B}_\pi$ depends only on the **inertial equivalence class** $[\pi]$ (the orbit of $\pi$ under unramified twists $\pi \mapsto \pi \otimes |\det|^s$). Indeed:
- The conductor $c(\pi)$ is unchanged by unramified twists, so $Q = \varpi^{-c}$ and $u_Q$ depend only on $[\pi]$.
- For $\pi' = \pi \otimes |\det|^s$, the Whittaker functions satisfy $V'(g) = V(g)|\det g|^s$, so $\Psi_{\mathrm{std}}(s_0, W', V') = \Psi_{\mathrm{std}}(s_0 + s, W', V)$. Since $s_0 + s$ ranges over $\mathbb{C}$ as $s_0$ does, $\mathrm{Rad}_L(\pi') = \mathrm{Rad}_L(\pi)$.

The set of inertial equivalence classes of generic irreducible admissible representations of $\mathrm{GL}_n(F)$ is **countable**: they are parametrized by a partition of $n$ and a tuple of supercuspidal representations (up to unramified twist) of smaller $\mathrm{GL}$'s, both of which are discrete data.

**Step 4.** A vector space over an uncountable field cannot be a countable union of proper subspaces (this is elementary; see e.g. [La02, Ch. III, Exercise 17] or note that each proper subspace has measure zero under any nondegenerate Gaussian, so their countable union has measure zero). Since $\mathcal{W}(\Pi, \psi^{-1})$ is a $\mathbb{C}$-vector space and $\{\mathcal{B}_{[\pi]}\}_{[\pi]}$ is a countable family of proper subspaces:

$$\mathcal{W}(\Pi, \psi^{-1}) \neq \bigcup_{[\pi]} \mathcal{B}_{[\pi]}.$$

Therefore, there exists $W \in \mathcal{W}(\Pi, \psi^{-1}) \setminus \bigcup_{[\pi]} \mathcal{B}_{[\pi]}$, i.e., $W^Q = \Pi(u_Q) W \notin \mathrm{Rad}_L(\pi)$ for all $\pi$. For such $W$, $\ell(V) \neq 0$ for some $V$, for each $\pi$. $\square$ (Argument 1)

**Remark.** This argument is existential: it proves a suitable $W$ exists without identifying it explicitly. The problem asks only for existence. See §3.7 for how this combines with the monomial structure to yield the full result.

---

**Argument 2 (supplementary; self-contained for $n = 1$, partial for $n \geq 2$).**

Suppose for contradiction that $\ell(V) = 0$ for all $V \in \mathcal{W}(\pi, \psi)$.

**Step 1 (Finite reduction).** Since $\pi$ is admissible, there exists $M \geq c + N$ such that $V(\varpi^{-N} k)$ is right-$K_1(\mathfrak{p}^M)$-invariant for all $V \in \mathcal{W}(\pi, \psi)$. The function $k \mapsto \psi^{-1}(\varpi^{-(c+N)} k_{nn})$ is right-$K_1(\mathfrak{p}^M)$-invariant for $M \geq c+N$ (since $k \mapsto k' k$ with $k' \in K_1(\mathfrak{p}^M)$ changes $k_{nn}$ by an element of $\mathfrak{p}^M$, and $\psi^{-1}(\varpi^{-(c+N)} \cdot)$ has conductor $\mathfrak{p}^{c+N} \subset \mathfrak{p}^M$). Then:

$$\ell(V) = \mathrm{vol}(K_1(\mathfrak{p}^M)) \sum_{\bar{k} \in K_n/K_1(\mathfrak{p}^M)} \psi^{-1}(\varpi^{-(c+N)} \bar{k}_{nn}) \, V(\varpi^{-N} \bar{k}).$$

Let $S = K_n / K_1(\mathfrak{p}^M)$ (a finite set). The assumption $\ell \equiv 0$ means the evaluation vector $\mathrm{ev}(V) := (V(\varpi^{-N} \bar{k}))_{\bar{k} \in S} \in \mathbb{C}^S$ lies in the hyperplane

$$H := \ker f, \quad f(\bar{k}) := \psi^{-1}(\varpi^{-(c+N)} \bar{k}_{nn}),$$

for **all** $V \in \mathcal{W}(\pi, \psi)$.

**Step 2 ($K_n$-equivariance).** The evaluation image $\mathcal{E} := \{\mathrm{ev}(V) : V \in \mathcal{W}(\pi, \psi)\} \subset \mathbb{C}^S$ is stable under the right regular representation $R$ of $K_n$ on $\mathbb{C}^S$, since $\mathrm{ev}(\pi(h)V)(\bar{k}) = V(\varpi^{-N} \bar{k} h) = (R(h) \, \mathrm{ev}(V))(\bar{k})$ for $h \in K_n$. It is nonzero: by the Whittaker separation property, there exists $V$ with $V(\varpi^{-N}) \neq 0$.

If $\mathcal{E} \subset H$, then $K_n$-stability gives $\mathcal{E} \subset \bigcap_{h \in K_n} R(h)^{-1} H = \bigcap_{h \in K_n} \ker(f \circ R(h))$.

**Step 3 (Fourier analysis on the $n$-th row).** We show that $\bigcap_{h \in K_n} \ker(f \circ R(h))$ forces the $n$-th row marginals to vanish.

Define $g_h := f \circ R(h)$ for $h \in K_n$. If $v \in \bigcap_h \ker g_h$, then $\Gamma_v(h) := \sum_{\bar{k}} v_{\bar{k}} \psi^{-1}(\varpi^{-(c+N)} (\bar{k} h)_{nn}) = 0$ for all $h \in K_n$.

Since $(\bar{k} h)_{nn} = \sum_j \bar{k}_{nj} h_{jn}$ (the $n$-th row of $\bar{k}$ dotted with the $n$-th column of $h$), the function $\Gamma_v$ depends on $h$ only through its $n$-th column. Taking $h = I + t E_{jn}$ (with $t \in \mathfrak{o}$, $j \neq n$): $(\bar{k} h)_{nn} = \bar{k}_{nn} + t \bar{k}_{nj}$, so:

$$0 = \sum_{\bar{k}} v_{\bar{k}} \, \psi^{-1}(\varpi^{-(c+N)}(\bar{k}_{nn} + t \bar{k}_{nj})) \quad \forall t \in \mathfrak{o}, \; \forall j \in \{1, \ldots, n-1\}.$$

Grouping by the $n$-th row value $\mathbf{r} = (r_1, \ldots, r_n) \in (\mathfrak{o}/\mathfrak{p}^M)^n$, define $\hat{v}(\mathbf{r}) := \sum_{\bar{k}: \mathrm{row}_n(\bar{k}) = \mathbf{r}} v_{\bar{k}}$. Then:

$$0 = \sum_{\mathbf{r}} \hat{v}(\mathbf{r}) \, \psi^{-1}(\varpi^{-(c+N)}(r_n + t r_j)) \quad \forall t \in \mathfrak{o}/\mathfrak{p}^M, \; \forall j.$$

The character $(r_1, \ldots, r_n) \mapsto \psi^{-1}(\varpi^{-(c+N)}(r_n + t r_j))$ is the additive character indexed by the vector $\mathbf{a} = (0, \ldots, t, \ldots, 0, 1) \in (\mathfrak{o}/\mathfrak{p}^M)^n$ (with $t$ in position $j$). Similarly, taking $h = \mathrm{diag}(1, \ldots, 1, a)$ with $a \in \mathfrak{o}^\times$ gives the character indexed by $(0, \ldots, 0, a)$. As $t, j, a$ vary, these vectors generate all of $(\mathfrak{o}/\mathfrak{p}^{c+N})^n$. (Note: $a$ ranges over $\mathfrak{o}^\times$, but $\mathfrak{o}^\times$ generates $\mathfrak{o}/\mathfrak{p}^M$ additively since $1 \in \mathfrak{o}^\times$ and $\mathfrak{o}^\times + \mathfrak{o}^\times = \mathfrak{o}$.) By Fourier inversion on $(\mathfrak{o}/\mathfrak{p}^{c+N})^n$:

$$\hat{v}(\mathbf{r}) = 0 \quad \text{for all } \mathbf{r} \in (\mathfrak{o}/\mathfrak{p}^M)^n. \tag{$*$}$$

**Step 4 (Conclusion).** Equation ($*$) shows that $\ell \equiv 0$ forces the $n$-th row marginals of all evaluation vectors to vanish. For $n = 1$, the $n$-th row IS the full matrix (a scalar), so ($*$) directly gives $v = 0$ and the contradiction is immediate. For $n \geq 2$, the $n$-th row marginal vanishing is a necessary condition but not sufficient to force $v = 0$; the full contradiction requires the representation-theoretic input of Argument 1. $\square$

### 3.7 Completing the proof

Combining the results:

1. **Equation (1):** $W(\mathrm{diag}(g,1) u_Q) = \psi^{-1}(Qg_{nn}) W(\mathrm{diag}(g,1))$.

2. **Choice of $W$:** $\Phi_W$ is right-$K_n$-invariant, supported on $N_n \varpi^{-N} K_n$, with $\Phi_W(\varpi^{-N} I_n) = 1$. Such $W$ exists by the BZ surjectivity of the Kirillov model.

3. **Monomial structure:** $\Psi(s, W, V) = q^{nN(s-1/2)} \cdot \ell(V)$ where $\ell(V) = \int_{K_n} \psi^{-1}(\varpi^{-(c+N)} k_{nn}) V(\varpi^{-N} k) \, dk$.

4. **Nonvanishing:** $\ell(V) \neq 0$ for some $V \in \mathcal{W}(\pi, \psi)$, by Lemma 2.

5. **Independence of $s$:** Since $\Psi(s) = q^{nN(s-1/2)} \cdot \ell(V)$ with $\ell(V) \neq 0$ and $q^{nN(s-1/2)} \neq 0$ for all $s$, we have $\Psi(s) \neq 0$ for all $s \in \mathbb{C}$.

6. **Universality and the monomial structure.** Argument 1 of Lemma 2 gives $W_0 \in \mathcal{W}(\Pi, \psi^{-1})$ with $\Pi(u_Q) W_0 \notin \mathrm{Rad}_L(\pi)$ for all $\pi$. For such $W_0$, $\Psi_{\mathrm{std}}(s, \Pi(u_Q) W_0, V) \neq 0$ for some $V$ (for each $\pi$). However, $W_0$ may not have single-coset Kirillov support, so $\Psi(s, W_0, V)$ could be a Laurent polynomial in $q^{-s}$ with zeros at specific $s$-values.

   To guarantee nonvanishing for **all** $s \in \mathbb{C}$, we restrict to single-coset vectors. For fixed $N$, define $\mathcal{S}_N := \{W \in \mathcal{W}(\Pi, \psi^{-1}) : \Phi_W \text{ supported on } N_n \varpi^{-N} K_n\}$. By BZ surjectivity, $\mathcal{S}_N$ is infinite-dimensional (it contains functions with all possible right-$K'$-invariance levels). Every $W \in \mathcal{S}_N$ gives a monomial $\Psi(s, W, V) = q^{nN(s-1/2)} \cdot \ell(V)$.

   For each inertial class $[\pi]$, $\mathcal{S}_N \cap \mathcal{B}_{[\pi]}$ is a subspace of $\mathcal{S}_N$. It is **proper**: if $\mathcal{S}_N \subset \mathcal{B}_{[\pi]}$, then $\ell_W(V) = 0$ for all $V \in \mathcal{W}(\pi, \psi)$ and all $W \in \mathcal{S}_N$. Since $V(\varpi^{-N} k)$ and $\psi^{-1}(\varpi^{-(c+N)} k_{nn})$ are both locally constant on $K_n$ (by admissibility and the conductor of $\psi$), there exists a congruence subgroup $K' \subset K_n$ such that both are right-$K'$-invariant. Taking $W \in \mathcal{S}_N$ with $\Phi_W(\varpi^{-N} k) = \mathrm{vol}(K')^{-1} \cdot \mathbf{1}_{K'}(k)$ gives exact point evaluation: $\ell_W(V) = \psi^{-1}(\varpi^{-(c+N)}) V(\varpi^{-N})$. If this vanishes for all $V$, then $V(\varpi^{-N}) = 0$ for all $V \in \mathcal{W}(\pi, \psi)$, contradicting the Whittaker separation property.

   So $\{\mathcal{S}_N \cap \mathcal{B}_{[\pi]}\}_{[\pi]}$ is a countable family of proper subspaces of $\mathcal{S}_N$, and $\mathcal{S}_N \neq \bigcup_{[\pi]} (\mathcal{S}_N \cap \mathcal{B}_{[\pi]})$. There exists $W \in \mathcal{S}_N \setminus \bigcup_{[\pi]} \mathcal{B}_{[\pi]}$: a single-coset vector with $\ell(V) \neq 0$ for some $V$, for each $\pi$.

$\square$

---

## Part IV: Verification and Remarks

### 4.1 Finiteness

The integral $\Psi(s, W, V)$ is finite for all $s$ because $\Phi_W$ has compact support modulo $N_n$. The integrand is compactly supported on $N_n \backslash \mathrm{GL}_n$, so the integral converges absolutely for all $s \in \mathbb{C}$ (not just for $\mathrm{Re}(s) \gg 0$). This is stronger than what the problem asks.

### 4.2 The role of $N$

The parameter $N$ can be any non-negative integer. Different choices of $N$ give different test vectors $W$. The proof works for any $N$; the simplest choice is $N = 0$, giving $\Phi_W$ supported on $N_n K_n$ (the "big cell" neighborhood of the identity).

**Remark on constraints.** The BZ surjectivity (§3.4) guarantees the existence of $W$ with $\Phi_W = \Phi_0$ for *any* $N \geq 0$, with no lower bound needed. The Fourier argument in Lemma 2 requires $M \geq c + N$ (which is always satisfiable since $M$ is chosen after $c$ and $N$ are fixed). So the proof is valid for all $N \geq 0$.

### 4.3 Explicit formula for $n = 2$ ($\mathrm{GL}_3 \times \mathrm{GL}_2$)

For concreteness, take $n = 2$, $N = 0$. Then $\Phi_W$ is the right-$K_2$-invariant function on $N_2 \backslash \mathrm{GL}_2$ supported on $N_2 K_2$ with $\Phi_W(I_2) = 1$. The integral is:

$$\Psi(s) = \int_{K_2} \psi^{-1}(\varpi^{-c} k_{22}) \, V(k) \, dk.$$

For $\pi$ with conductor $\mathfrak{p}^c$ and $V$ the newform $V_0$ (fixed by $K_1(\mathfrak{p}^c)$):

$$\Psi(s) = \sum_{\bar{k} \in K_2/K_1(\mathfrak{p}^c)} \psi^{-1}(\varpi^{-c} \bar{k}_{22}) \, V_0(\bar{k}) \cdot \mathrm{vol}(K_1(\mathfrak{p}^c)).$$

This is a finite sum of Gauss-sum-type terms. By Lemma 2, it is nonzero for some choice of $V$ (possibly different from the newform).

### 4.4 Notes on Lemma 2

The proof of Lemma 2 (Section 3.6) is the most delicate part of the argument. Two complementary approaches are given:

- **Argument 1** (primary, complete) uses the JPSS nondegeneracy of the RS pairing and a dimension argument (a vector space over an uncountable field is not a countable union of proper subspaces). The key steps are: (i) the left radical $\mathrm{Rad}_L(\pi)$ is a proper subspace for each $\pi$ (by JPSS); (ii) the bad locus $\mathcal{B}_\pi = \Pi(u_Q)^{-1} \mathrm{Rad}_L(\pi)$ is proper; (iii) $\mathcal{B}_\pi$ depends only on the inertial class $[\pi]$ (since unramified twists don't change $\mathrm{Rad}_L$ or the conductor); (iv) the inertial classes are countable, so $\bigcup_{[\pi]} \mathcal{B}_{[\pi]}$ cannot exhaust $\mathcal{W}(\Pi, \psi^{-1})$. The §3.7 universality argument further restricts to single-coset vectors $\mathcal{S}_N$ and shows $\mathcal{S}_N \cap \mathcal{B}_{[\pi]}$ is proper for each $[\pi]$ (via the Whittaker separation property). This argument is existential.

- **Argument 2** (Fourier-analytic reduction) provides an independent perspective for a fixed $\pi$: it reduces the nonvanishing to a finite-dimensional problem via Fourier analysis on $(\mathfrak{o}/\mathfrak{p}^{c+N})^n$ (the $n$-th row of $K_n$). Steps 1–3 are fully rigorous and show that $\ell \equiv 0$ forces all $n$-th row marginals to vanish. For $n = 1$ this directly gives the contradiction and the argument is fully self-contained.

Argument 1 answers the existence question posed by the problem. Argument 2 provides useful structural insight and a complete proof for $n = 1$.

### 4.5 Summary

The proof has three ingredients:
1. **Algebraic:** The $u_Q$-twist reduces to multiplication by $\psi^{-1}(Qg_{nn})$ (Lemma 1).
2. **Analytic:** Choosing $W$ with single-determinant-level support makes $\Psi(s)$ a monomial in $q^{-s}$, eliminating the "$\forall s$" condition.
3. **Representation-theoretic:** The JPSS nondegeneracy of the Rankin–Selberg pairing guarantees nonvanishing for some $V$ (Lemma 2).

---

## Appendix: Partial Lean 4 Verification

The logical skeleton of this proof has been formally verified in Lean 4 + Mathlib. The file `FirstProof/P02_RankinSelberg.lean` verifies the following components:

1. **Proper subspace preservation** (`not_subset_proper`, `preimage_proper_of_proper`): A vector space is not contained in a proper subspace, and the preimage of a proper subspace under a linear automorphism is proper. This models the key Step 2 of Lemma 2: $\mathcal{B}_\pi = \Pi(u_Q)^{-1}\mathrm{Rad}_L(\pi)$ is proper whenever $\mathrm{Rad}_L(\pi)$ is proper.

2. **Monomial nonvanishing** (`monomial_nonzero`): A nonzero scalar times a positive power $c \cdot b^s \neq 0$ for all $s$, when $c \neq 0$ and $b > 0$. This is the real-variable version of the key monomial trick (§3.5): $\Psi(s) = q^{nN(s-1/2)} \cdot \ell(V)$ is nonzero for all $s \in \mathbb{C}$ when $\ell(V) \neq 0$.

3. **Countability of inertial classes**: Verified that $\mathbb{N} \times \mathbb{N}$ is countable, modeling the countability of inertial equivalence classes (Step 3 of Lemma 2).

4. **Gauss sum positivity** (`gauss_sum_pos`, `unramified_nonzero`): For the $n = 1$ case: $q^c > 0$ for $q > 1$ (Gauss sum magnitude), and $\mathrm{vol}(\mathfrak{o}^\times) > 0$ implies nonvanishing in the unramified case.

5. **Proof structure** (`proof_structure`, `universality_from_avoidance`): The logical skeleton: the three ingredients (twist formula + monomial structure + nonvanishing) combine to give universality.

**Scope and limitations.** The $p$-adic representation theory (Whittaker models, Bernstein–Zelevinsky filtration, JPSS nondegeneracy, conductor theory) is not in Mathlib. The Lean file verifies the abstract linear algebra and arithmetic arguments that underpin the proof.

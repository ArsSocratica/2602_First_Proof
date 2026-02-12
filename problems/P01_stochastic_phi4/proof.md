# Problem 1 — Φ⁴₃ Measure Equivalence Under Smooth Shifts

## Answer

**No.** The measures $\mu$ and $T_\psi^*\mu$ are not equivalent; they are mutually singular.

## Theorem

Let $\mathbb{T}^3$ be the three-dimensional unit torus, $\mu$ the $\Phi^4_3$ measure on $\mathcal{D}'(\mathbb{T}^3)$, and $\psi \in C^\infty(\mathbb{T}^3)$ with $\psi \not\equiv 0$. Let $T_\psi(\phi) = \phi + \psi$. Then $\mu$ and $T_\psi^* \mu$ are **mutually singular**.

---

## Proof Overview

We construct a measurable set $A$ with $\mu(A) = 1$ and $(T_\psi^*\mu)(A) = 0$.

- **Part A (background):** The HKN separating set $A^{\alpha,\gamma}$ from arXiv:2409.10037 establishes $\mu \perp \mu_0$. We explain why this set does **not** suffice for the shift problem (Appendix A).
- **Part B (novel contribution):** Using Hairer's separating functional $A_\psi$ (from his 2022 note, hairer.org/Phi4.pdf), we show $\mu(A_\psi) = 1$ and $(T_\psi^*\mu)(A_\psi) = 0$. The dominant mechanism is a **deterministic mass-shift term** $-be^{n/4}\|\psi\|_{L^2}^2$ from the unmollified field in Hairer's functional, where $b \neq 0$ is the logarithmic mass renormalization constant.

**Remark on novelty.** Hairer's 2022 note establishes $\mu \perp \mu_0$. Our contribution is the explicit verification that the same separating set $A_\psi$ also gives $(T_\psi^*\mu)(A_\psi) = 0$ via the Hermite shift formula, and the explanation of why the HKN framework cannot achieve this.

---

## Part A: The HKN Separating Set

### Setup (following arXiv:2409.10037)

The $\Phi^4_3$ model on $\mathbb{T}^3$ is the special case of arXiv:2409.10037 with $k=3$, $\sigma=2$, $d=3$, $m=n_0=n_1=n_2=n_3=0$. Let $Z(t)$ be the stationary GFF with covariance $(1-\Delta)^{-1}$. Define the sharp frequency cutoff $P_N f = \sum_{|l|\leq N}\hat{f}(l)e_l$, write $Z_N = P_N Z$, and let $\langle\nabla\rangle = (1-\Delta)^{1/2}$.

**Key constants.** The GFF variance at cutoff $N$:
$$c_{N,1}^\alpha := \mathbb{E}[|\langle\nabla\rangle^\alpha Z_N(t,x)|^2] = \sum_{|l|\leq N}\langle l\rangle^{2\alpha-2} \simeq N^{2\alpha+1}$$

The renormalization constant (arXiv:2409.10037, eq. (3.4)):
$$c_{N,2}^\alpha := \mathbb{E}\left[H_3(\langle\nabla\rangle^\alpha Z_N; c_{N,1}^\alpha)\cdot\langle\nabla\rangle^\alpha Y_N\right]$$
where $Y$ is the Wick-renormalized nonlinear stochastic object. By Lemma 3.5 of arXiv:2409.10037, for $\alpha > \alpha_\star$: $c_{N,2}^\alpha \gtrsim N^{\delta(\alpha)}$ where
$$\delta(\alpha) = 4\alpha + 1, \qquad \alpha_0 = -\tfrac{1}{4}$$

**Derivation.** The general formula (arXiv:2409.10037, eq. (3.7)) is $\delta(\alpha) = k(\alpha + m - \frac{\sigma-d}{2}) - (A - n_0 + \sigma - \alpha)$ where $A = \frac{k}{2}(\sigma-d) + \sum_{i=0}^k n_i$. For $\Phi^4_3$: $k=3$, $\sigma=2$, $d=3$, $m=n_i=0$, so $A = -3/2$ and $\delta(\alpha) = 3(\alpha + 1/2) - (1/2 - \alpha) = 4\alpha + 1$. Setting $\delta(\alpha_0)=0$ gives $\alpha_0 = -1/4$.

### The separating set

For $\alpha > \alpha_\star$ and $0 < \gamma < \delta(\alpha)$:
$$A^{\alpha,\gamma} := \left\{\phi \in \mathcal{D}' : \lim_{N\to\infty} N^{-\gamma}\left\langle H_4(\langle\nabla\rangle^\alpha P_N\phi; c_{N,1}^\alpha) + 4c_{N,2}^\alpha, 1\right\rangle_{L^2} = 0\right\}$$

### $\mu(A^{\alpha,\gamma}) = 1$

By arXiv:2409.10037, Theorem 3.1 and Corollary 4.1: for any global-in-time solution $u(t)$ of the dynamic $\Phi^4_3$ model, $\mathbb{P}(u(t) \in A^{\alpha,\gamma}) = 1$. In particular $\mu(A^{\alpha,\gamma}) = 1$.

### $\mu_0(A^{\alpha,\gamma}) = 0$

Under the GFF ($Y=0$, $v=0$): $N^{-\gamma}\langle\text{Wick}((\langle\nabla\rangle^\alpha Z_N)^4), 1\rangle \to 0$ a.s. (Lemma 3.3), but $N^{-\gamma}c_{N,2}^\alpha \gtrsim N^{\delta(\alpha)-\gamma} \to \infty$. So $\mu_0(A^{\alpha,\gamma}) = 0$. $\square$

---

## Part B: Singularity of $\mu$ and $T_\psi^*\mu$ (Novel Contribution)

### Why the HKN set does not suffice

The HKN separating set $A^{\alpha,\gamma}$ from Part A separates $\mu$ from the GFF $\mu_0$, but does **not** separate $\mu$ from $T_\psi^*\mu$. The reason: the shifted field $\tilde{\Phi}+\psi$ has decomposition $Z + \lambda Y + (v+\psi)$, and since $\psi \in C^\infty$, the shift is absorbed into the regular remainder $v \to v+\psi$, which vanishes after $N^{-\gamma}$ scaling. Therefore $(T_\psi^*\mu)(A^{\alpha,\gamma}) = 1$ as well. (See Appendix A for the detailed calculation.)

To prove $\mu \perp T_\psi^*\mu$, we use a **different** separating functional — the one from Hairer's original note ("$\Phi^4_3$ is orthogonal to GFF," September 2022, hairer.org/Phi4.pdf), which uses super-exponential mollification and an unmollified mass-correction term.

### Hairer's separating functional

Let $\rho \in C_c^\infty(\mathbb{R}^3)$ be a mollifier with $\int\rho = 1$, and set $\rho_n(x) = e^{3e^n}\rho(e^{e^n}x)$ (mollification at scale $\varepsilon_n = e^{-e^n}$). Define $\Phi_n = \rho_n * \Phi$. The pointwise variance of $\Phi_n$ under the GFF is:
$$c_n := \mathbb{E}_{\mu_0}[|\Phi_n(x)|^2] = \sum_{k \in \mathbb{Z}^3} \langle k\rangle^{-2}|\hat{\rho}_n(k)|^2 \simeq a \cdot e^{e^n}$$
where $a > 0$ is an explicit constant depending on $\rho$.

The **Wick cube** at scale $n$ is $:\!\Phi_n^3\!: = H_3(\Phi_n; c_n) = \Phi_n^3 - 3c_n\Phi_n$.

The **mass renormalization constant** $b$ is the logarithmic coefficient in the mass counterterm of the $\Phi^4_3$ construction:
$$a_\varepsilon = a_1\varepsilon^{-1} + b\log(\varepsilon^{-1}) + O(1), \qquad b \neq 0$$
This constant $b$ is nonzero for $\Phi^4_3$ in 3D — it arises from the second-order Feynman diagram (the "sunset" or "setting sun" graph) and is the fundamental reason for singularity. Its nonvanishing is established in the literature (see e.g. Hairer, *Invent. Math.* 198, 2014, §10; Gubinelli-Hofmanová, *Comm. Math. Phys.* 384, 2021).

**Definition.** For $\psi \in C^\infty(\mathbb{T}^3)$ with $\psi \not\equiv 0$, define:
$$A_\psi := \left\{\Phi \in \mathcal{D}'(\mathbb{T}^3) : \lim_{n\to\infty} e^{-3n/4}\langle :\!\Phi_n^3\!: - be^n\Phi, \psi\rangle = 0\right\}$$

Note the critical structural feature: the term $-be^n\Phi$ uses the **unmollified** distributional field $\Phi$, not the mollified $\Phi_n$. This is what makes the functional sensitive to smooth shifts.

### $\mu(A_\psi) = 1$

We must show $e^{-3n/4}\langle :\!\Phi_n^3\!: - be^n\Phi, \psi\rangle \to 0$ $\mu$-a.s. The key move is to split the **unmollified** field $\Phi$ into the mollified field $\Phi_n$ plus a correction:

$$\langle :\!\Phi_n^3\!: - be^n\Phi, \psi\rangle = \underbrace{\langle :\!\Phi_n^3\!: - be^n\Phi_n, \psi\rangle}_{\text{(A) renormalized cubic}} - \underbrace{be^n\langle \Phi - \Phi_n, \psi\rangle}_{\text{(B) mollification error}}$$

**Part (A): The renormalized cubic is $O(1)$.**

$:\!\Phi_n^3\!: - be^n\Phi_n = \Phi_n^3 - 3c_n\Phi_n - be^n\Phi_n = \Phi_n^3 - (3c_n + be^n)\Phi_n = \Phi_n^3 - C_{\varepsilon_n}\Phi_n + O(1)\cdot\Phi_n$

where $C_{\varepsilon_n} = 3c_n + be^n + O(1)$ is the full counterterm at scale $\varepsilon_n = e^{-e^n}$. The convergence of the renormalized product $\Phi_n^3 - C_{\varepsilon_n}\Phi_n \to :\!\Phi^3\!:_{\mathrm{ren}}$ in $\mathcal{C}^{-1/2-\kappa}(\mathbb{T}^3)$ is a **proven theorem** (Hairer, *Invent. Math.* 198, 2014, Theorem 1.1; also Gubinelli-Imkeller-Perkowski, *Forum Math. Pi* 3, 2015; Barashkov-Gubinelli, *Electron. J. Probab.* 26, 2021). Tested against smooth $\psi$, this converges to the finite random variable $\langle :\!\Phi^3\!:_{\mathrm{ren}}, \psi\rangle$. The $O(1)\cdot\Phi_n$ correction tested against $\psi$ converges to $O(1)\cdot\langle\Phi, \psi\rangle$, finite $\mu$-a.s.

Therefore: $\langle :\!\Phi_n^3\!: - be^n\Phi_n, \psi\rangle = O(1)$ as $n \to \infty$, $\mu$-a.s.

**Part (B): The mollification error is super-exponentially small.**

Write $\langle \Phi - \Phi_n, \psi\rangle = \langle \Phi, \psi - \rho_n * \psi\rangle$. Since $\psi \in C^\infty$ and $\varepsilon_n = e^{-e^n}$:

$$\|\psi - \rho_n * \psi\|_{H^s}^2 = \sum_k |1 - \hat{\rho}(\varepsilon_n k)|^2 \langle k\rangle^{2s} |\hat{\psi}(k)|^2 \leq C\varepsilon_n^4 \|\psi\|_{H^{s+2}}^2$$

since $|1 - \hat{\rho}(\varepsilon_n k)| \leq C\varepsilon_n^2|k|^2$. Using the BG decomposition $\Phi = W_\infty + v^*$ (Barashkov-Gubinelli 2021):

- **GFF part:** $\mathrm{Var}(\langle W_\infty, \psi - \rho_n * \psi\rangle) = \|\psi - \rho_n * \psi\|_{H^{-1}}^2 = O(e^{-4e^n})$.
- **Drift part:** $|\langle v^*, \psi - \rho_n * \psi\rangle| \leq \|v^*\|_{L^2} \cdot O(\varepsilon_n^2) = O(e^{-2e^n})$ a.s.

Therefore: $|be^n\langle \Phi - \Phi_n, \psi\rangle| = O(e^{n - 2e^n}) \to 0$ super-exponentially fast.

**Combined:** $e^{-3n/4}\langle :\!\Phi_n^3\!: - be^n\Phi, \psi\rangle = e^{-3n/4} \cdot O(1) + O(e^{n-2e^n}) \to 0$ $\mu$-a.s. $\square$

**Remark.** The only deep input is the convergence of the renormalized cubic, which is established content of regularity structures / paracontrolled calculus / BG variational approach. The super-exponential mollification $\varepsilon_n = e^{-e^n}$ is essential for Part (B): with polynomial mollification, the error would decay only polynomially and the mass term factor $e^n$ would not be dominated.

### $\mu_0(A_\psi) = 0$

Under the GFF $\mu_0$ (where $\Phi = Z$ is the free field with no nonlinear interaction):

**Step 1.** The Wick cube $:\!\Phi_n^3\!:$ in 3D has covariance that diverges only **logarithmically** in the variance of the field:
$$\text{Var}_{\mu_0}(\langle:\!\Phi_n^3\!:, \psi\rangle) \sim C_\psi \cdot e^n$$
(The covariance involves a triple convolution sum $\sum_{k_1,k_2,k_3} \langle k_i\rangle^{-2}|\hat{\rho}_n(k_i)|^2|\hat{\psi}(k_1+k_2+k_3)|^2$, which in 3D grows like $e^n$ — logarithmically in the pointwise variance $c_n \sim e^{e^n}$.)

As Hairer explains (MathOverflow answer, Jan 12, 2026): "The integral of [the Wick cube's] covariance only diverges logarithmically (in the variance of the field itself, i.e. like $e^n$). As a consequence, if one multiplies it by $e^{-\alpha n}$ for any $\alpha > 1/2$ that's good enough to guarantee that it converges weakly to 0."

Since $3/4 > 1/2$: $e^{-3n/4}\langle:\!\Phi_n^3\!:, \psi\rangle \to 0$ a.s. under $\mu_0$.

**Step 2.** The mass term: $-be^{n-3n/4}\langle\Phi, \psi\rangle = -be^{n/4}\langle\Phi, \psi\rangle$.

Under $\mu_0$, $\langle\Phi, \psi\rangle$ is a non-degenerate Gaussian random variable (with variance $\|\psi\|_{H^{-1}}^2 > 0$ since $\psi \neq 0$). Therefore $e^{n/4}\langle\Phi, \psi\rangle \to \pm\infty$ a.s., and the full expression diverges.

**Conclusion:** $\mu_0(A_\psi) = 0$. $\square$

### $(T_\psi^*\mu)(A_\psi) = 0$ — the key step

We must show: for $\mu$-a.e. $\Phi$, the shifted field $\Phi + \psi \notin A_\psi$.

Evaluate the functional at $\Phi + \psi$. Write $(\Phi+\psi)_n = \Phi_n + \psi_n$ where $\psi_n = \rho_n * \psi \to \psi$ in $C^\infty$ (since $\psi$ is smooth).

$$e^{-3n/4}\langle:\!(\Phi_n+\psi_n)^3\!:_{c_n} - be^n(\Phi+\psi), \psi\rangle$$

**Hermite shift formula.** $H_3(x+a; c) = H_3(x;c) + 3a\,H_2(x;c) + 3a^2 x + a^3$, so:

$$:\!(\Phi_n+\psi_n)^3\!:_{c_n} = :\!\Phi_n^3\!:_{c_n} + 3\psi_n\,:\!\Phi_n^2\!:_{c_n} + 3\psi_n^2\,\Phi_n + \psi_n^3$$

The full shifted expression becomes:

$$\underbrace{:\!\Phi_n^3\!:_{c_n} - be^n\Phi}_{\text{(I) original}} + \underbrace{3\psi_n\,:\!\Phi_n^2\!:_{c_n}}_{\text{(II) Wick square}} + \underbrace{3\psi_n^2\,\Phi_n}_{\text{(III) linear}} + \underbrace{\psi_n^3}_{\text{(IV) deterministic}} - \underbrace{be^n\psi}_{\text{(V) mass shift}}$$

We test against $\psi$ and scale by $e^{-3n/4}$:

**Term (I):** $e^{-3n/4}\langle:\!\Phi_n^3\!: - be^n\Phi, \psi\rangle \to 0$ $\mu$-a.s., since $\mu(A_\psi) = 1$.

**Term (II):** $3e^{-3n/4}\langle\psi_n\,:\!\Phi_n^2\!:_{c_n}, \psi\rangle$. The Wick square $:\!\Phi_n^2\!:$ tested against the smooth function $\psi_n\psi$ has variance:
$$\text{Var}(\langle\psi_n\,:\!\Phi_n^2\!:, \psi\rangle) = 2\sum_{k,l} \langle k\rangle^{-2}\langle l\rangle^{-2}|\hat{\rho}_n(k)|^2|\hat{\rho}_n(l)|^2|\widehat{\psi_n\psi}(k+l)|^2$$
Since $\psi_n\psi$ is smooth, $|\widehat{\psi_n\psi}(m)|$ decays rapidly. The inner sum over $k$ (for fixed $m = k+l$) is $\sum_k \langle k\rangle^{-2}\langle m-k\rangle^{-2}|\hat{\rho}_n(k)|^2|\hat{\rho}_n(m-k)|^2$, which converges (in 3D, $\sum_k \langle k\rangle^{-4} < \infty$). So the total variance converges to a finite limit.

Therefore: $e^{-3n/4}\langle\psi_n\,:\!\Phi_n^2\!:, \psi\rangle = O(e^{-3n/4}) \to 0$ a.s.

**Term (III):** $3e^{-3n/4}\langle\psi_n^2\Phi_n, \psi\rangle = 3e^{-3n/4}\langle\psi^2\psi, \Phi_n\rangle(1+o(1))$. The quantity $\langle\psi^2\psi, \Phi_n\rangle$ is a Gaussian (under the GFF component) with variance $\sum_k |\widehat{\psi^2\psi}(k)|^2\langle k\rangle^{-2}|\hat{\rho}_n(k)|^2$, which converges to the finite limit $\|\psi^2\psi\|_{H^{-1}}^2$. Under $\mu$, the non-Gaussian correction from $v^*$ adds a bounded deterministic shift. So: $e^{-3n/4}\langle\psi_n^2\Phi_n, \psi\rangle = O(e^{-3n/4}) \to 0$ a.s.

**Term (IV):** $e^{-3n/4}\langle\psi_n^3, \psi\rangle = e^{-3n/4}\|\psi\|_{L^4}^4(1+o(1)) \to 0$.

**Term (V):** $-be^{n-3n/4}\langle\psi, \psi\rangle = -b\|\psi\|_{L^2}^2 \cdot e^{n/4}$.

Since $b \neq 0$ and $\|\psi\|_{L^2}^2 > 0$: **Term (V) diverges deterministically** as $\pm e^{n/4} \to \pm\infty$.

**Conclusion.** The full shifted expression satisfies:
$$e^{-3n/4}\langle:\!(\Phi+\psi)_n^3\!: - be^n(\Phi+\psi), \psi\rangle = \underbrace{o(1)}_{\text{Terms I-IV}} - b\|\psi\|_{L^2}^2 e^{n/4} \to \mp\infty$$

Therefore $\Phi + \psi \notin A_\psi$ for $\mu$-a.e. $\Phi$, giving $(T_\psi^*\mu)(A_\psi) = 0$. $\square$

### Why this works: the role of the unmollified field

The critical structural feature is the term $-be^n\langle\Phi, \psi\rangle$ in Hairer's functional, which uses the **unmollified** distributional field $\Phi$. When we shift $\Phi \to \Phi + \psi$, this becomes $-be^n\langle\Phi, \psi\rangle - be^n\|\psi\|_{L^2}^2$. The first part is absorbed into the original functional (which → 0 under $\mu$), but the second part $-be^n\|\psi\|_{L^2}^2$ is a **deterministic divergence** that survives the $e^{-3n/4}$ scaling.

By contrast, the Hermite shift terms (II)-(IV) all involve the **mollified** field $\Phi_n$ tested against smooth functions, which produces bounded random variables. The super-exponential mollification ($\varepsilon_n = e^{-e^n}$) ensures these terms are killed by the $e^{-3n/4}$ scaling.

This explains why the HKN framework (which uses polynomial cutoff $P_N$ and has no unmollified term) cannot detect smooth shifts — see Appendix A.

---

## Conclusion

Combining Parts A and B: $\mu(A_\psi) = 1$ and $(T_\psi^*\mu)(A_\psi) = 0$, so $\mu$ and $T_\psi^*\mu$ are mutually singular. $\blacksquare$

**Remark.** The proof extends to shifts $\psi \in C^{1,\alpha}(\mathbb{T}^3)$ for any $\alpha > 0$, as noted by Hairer (MathOverflow, Dec 5, 2024). The key requirement is that $\psi_n \to \psi$ in $L^\infty$ and $\langle\psi^2\psi, \Phi_n\rangle$ has bounded variance, which holds as long as $\psi^3 \in H^{-1}(\mathbb{T}^3)$.

---

## Key Citations

- **arXiv:2409.10037** (Hairer-Kusuoka-Nagoji), Theorem 3.1 and Corollary 4.1: $\mu(A^{\alpha,\gamma}) = 1$ for the $\Phi^4_3$ measure. Formalization of Hairer's 2022 note using polynomial frequency cutoff and $H_{k+1}$ Hermite polynomials.
- **Hairer**, "$\Phi^4_3$ is orthogonal to GFF," unpublished note (September 2022), hairer.org/Phi4.pdf. Original proof of $\mu \perp \mu_0$ via the separating set $A_\psi$. MathOverflow answer (Jan 12, 2026, MO 485884) explaining the "easy direction" ($\mu_0(A_\psi) = 0$). MathOverflow comment (Dec 5, 2024, MO 481553) confirming extension to $C^{1,\alpha}$ shifts.
- **Hairer**, *Invent. Math.* 198 (2014), §10: Construction of $\Phi^4_3$ via regularity structures; mass renormalization constant $b \neq 0$.
- **Gubinelli-Hofmanová**, *Comm. Math. Phys.* 384 (2021): PDE construction of $\Phi^4_3$; confirms $b \neq 0$.
- **Barashkov-Gubinelli**, *Electron. J. Probab.* 26 (2021), Theorem 1.1 (arXiv:2004.01513): Variational decomposition $\tilde{\Phi} = W_\infty + v^*$.

---

## Appendix A: Why the HKN Framework Cannot Detect Smooth Shifts

The HKN separating set $A^{\alpha,\gamma}$ (Part A) separates $\mu$ from $\mu_0$ but NOT from $T_\psi^*\mu$. Here we give the detailed calculation.

**Claim.** $(T_\psi^*\mu)(A^{\alpha,\gamma}) = 1$.

**Proof.** Let $u \sim \mu$ with decomposition $u = Z + \lambda Y + v$ (Assumption 2.1 of arXiv:2409.10037). Set $\tilde{u} = u + \psi$. Then $\tilde{u} = Z + \lambda Y + \tilde{v}$ where $\tilde{v} = v + \psi$.

Since $\psi \in C^\infty \subset C^\beta$ for any $\beta$, and $v \in C^\beta$ for $\beta < 1$ (by the SPDE regularity theory), $\tilde{v}$ has the same regularity as $v$.

Apply the HKN expansion (eq. (3.12) of arXiv:2409.10037):

$$N^{-\gamma} H_4(\langle\nabla\rangle^\alpha \tilde{u}_N; c_{N,1}^\alpha) = N^{-\gamma}\text{Wick}((\langle\nabla\rangle^\alpha Z_N)^4) - 4N^{-\gamma}\text{Wick}((\langle\nabla\rangle^\alpha Z_N)^3)\langle\nabla\rangle^\alpha Y_N + R_N$$

where $R_N$ collects all terms with at least one factor of $\langle\nabla\rangle^\alpha \tilde{v}_N$.

- **First term:** $\to 0$ in $\mathcal{D}'$ a.s. by Lemma 3.3 (with $J = k+1 = 4$).
- **Remainder $R_N$:** Each term in $R_N$ has the form $N^{-\gamma}(c_{N,1}^\alpha)^p(\langle\nabla\rangle^\alpha Z_N)^{i-2p}(\langle\nabla\rangle^\alpha Y_N)^j(\langle\nabla\rangle^\alpha \tilde{v}_N)^{4-i-j}$ with $(i,j) \neq (4,0),(3,1)$. The regularity analysis (eq. (3.13)-(3.14) of arXiv:2409.10037) shows each such term $\to 0$, since $\tilde{v}_N$ has the same regularity as $v_N$ (adding smooth $\psi$ doesn't change the Hölder exponent).
- **Second term:** Has expectation $-4c_{N,2}^\alpha$. After adding $+4c_{N,2}^\alpha$ and using Lemma 3.5 (eq. (3.9)):

$$N^{-\gamma}\langle H_4(\langle\nabla\rangle^\alpha \tilde{u}_N; c_{N,1}^\alpha) + 4c_{N,2}^\alpha, 1\rangle \to 0 \quad \text{a.s.}$$

Therefore $\tilde{u} = u + \psi \in A^{\alpha,\gamma}$ a.s., i.e., $(T_\psi^*\mu)(A^{\alpha,\gamma}) = 1$. $\square$

**Root cause.** The HKN functional uses only the frequency-truncated field $P_N\phi$, and the correction $c_{N,2}^\alpha$ is a constant depending on the noise structure (through $Z$ and $Y$), not on $\psi$. Adding a smooth shift only modifies $v \to v + \psi$, which is in the "regular" part that vanishes after $N^{-\gamma}$ scaling. There is no unmollified term to create a deterministic divergence under the shift.

By contrast, Hairer's functional (Part B) includes the unmollified term $-be^n\langle\Phi, \psi\rangle$, which produces the deterministic divergence $-be^{n/4}\|\psi\|_{L^2}^2$ under the shift.

| Feature | Hairer's functional (Part B) | HKN set (Part A) |
|---------|------------------------------|-------------------|
| Mollification | Super-exponential ($e^{-e^n}$) | Polynomial ($P_N$) |
| Scaling | $e^{-3n/4}$ | $N^{-\gamma}$ |
| Unmollified term | $-be^n\Phi$ (YES) | None |
| Separates $\mu$ from $\mu_0$ | ✓ | ✓ |
| Separates $\mu$ from $T_\psi^*\mu$ | **✓** | **✗** |

---

## Appendix B: Partial Lean 4 Verification

The abstract measure-theoretic skeleton of this proof has been formally verified in Lean 4 + Mathlib. The file `FirstProof/P01_StochasticPhi4.lean` verifies the following components:

1. **Separating set criterion** (`mutuallySingular_of_separating_set`): If there exists a measurable set $A$ with $\mu(A^c) = 0$ and $\nu(A) = 0$, then $\mu \perp \nu$. This is the abstract skeleton of the entire proof: the set $A_\psi$ from Part B plays this role.

2. **Axiomatized analytic inputs**: The $\Phi^4_3$ measure, the shift map $T_\psi$, and the separating set $A_\psi$ are axiomatized (since the Φ⁴₃ measure is not yet formalized in Mathlib). The two key analytic inputs — $\mu(A_\psi^c) = 0$ (from Hairer's note) and $(T_\psi^*\mu)(A_\psi) = 0$ (from the Hermite shift analysis in Part B) — are stated as axioms.

3. **Main theorem** (`phi43_shift_mutuallySingular`): From the axiomatized inputs, the conclusion $\mu \perp T_\psi^*\mu$ is derived by applying the separating set criterion. This verifies that the logical structure of the proof is correct: the two analytic inputs (full measure and null measure) are sufficient to conclude mutual singularity.

**Scope and limitations.** The analytic content — construction of $A_\psi$ via Hairer's functional, the Barashkov–Gubinelli decomposition, the Hermite shift formula, and the variance estimates — is beyond current Mathlib capabilities. The Lean file verifies only the measure-theoretic shell.

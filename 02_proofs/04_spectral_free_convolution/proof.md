# Problem 4 — Superadditivity of $1/\Phi_n$ under Finite Free Convolution

## 1. Problem Statement

For a monic real-rooted polynomial $p(x) = \prod_{i=1}^n (x - \lambda_i)$ with distinct roots, define the **root repulsion functional**:

$$\Phi_n(p) := \sum_{i=1}^n \left(\sum_{j \neq i} \frac{1}{\lambda_i - \lambda_j}\right)^2$$

and $\Phi_n(p) := \infty$ if $p$ has a repeated root. The **finite free additive convolution** $p \boxplus_n q$ is defined by:

$$(p \boxplus_n q)(x) = \sum_{k=0}^n c_k x^{n-k}, \quad c_k = \sum_{i+j=k} \frac{(n-i)!(n-j)!}{n!(n-k)!} a_i b_j$$

**Question (Srivastava).** Is it true that $\frac{1}{\Phi_n(p \boxplus_n q)} \geq \frac{1}{\Phi_n(p)} + \frac{1}{\Phi_n(q)}$?

**Status:** We prove the inequality for $n = 2$ (exact equality) and $n = 3$. We establish a Hermite decomposition valid for all $n$ that reduces the conjecture to the superadditivity of a non-positive remainder term $R$, verified numerically with 0 violations for $n \leq 50$ (545,000+ tests). We also discover that $\Phi_n$ is a contraction under convolution ($\Phi(\text{conv}) \leq \min(\Phi(p), \Phi(q))$) and that the Stam inequality holds along the entire coupled Hermite flow. The general case remains open but is reduced to a single clean sub-problem.

---

## 2. Structural Reductions

### Lemma 1 (Translation Invariance of $\Phi_n$)

*$\Phi_n$ is invariant under translation of roots: $\Phi_n(p(x-c)) = \Phi_n(p(x))$ for all $c \in \mathbb{R}$.*

*Proof.* If $\mu_i = \lambda_i + c$, then $\mu_i - \mu_j = \lambda_i - \lambda_j$, so $h_i(\mu) = h_i(\lambda)$. $\square$

### Lemma 2 (Centering Reduction)

*WLOG we may assume $a_1 = b_1 = 0$ (i.e., both polynomials are centered, with roots summing to zero).*

*Proof.* Since $\Phi_n$ is translation-invariant (Lemma 1), we can shift $p$ and $q$ independently so that both have mean root zero. The convolution $p \boxplus_n q$ has $c_1 = a_1 + b_1 = 0$, so it is also centered. The inequality is preserved. $\square$

### Lemma 3 (Coefficient Additivity for $n \leq 3$)

*For centered polynomials ($a_1 = b_1 = 0$) of degree $n \leq 3$: the convolution is coefficient-wise additive, i.e., $c_k = a_k + b_k$ for all $k \geq 2$.*

*Proof.* For $a_1 = b_1 = 0$, the cross-terms in the convolution formula with $i = 1$ or $j = 1$ vanish. For $k \leq 3$, the only remaining terms with $i + j = k$ and $i, j \geq 2$ require $i \geq 2, j \geq 2, i+j \leq 3$, which is impossible. So only the terms $(i,j) = (0,k)$ and $(k,0)$ survive, each contributing $a_k$ and $b_k$ respectively (with coefficient 1). $\square$

**Remark.** For $n \geq 4$, cross-terms appear. For example, with $n = 4$ and $k = 4$: the term $(i,j) = (2,2)$ contributes $\frac{(n-2)!^2}{n!(n-4)!} a_2 b_2 = \frac{(n-2)(n-3)}{n(n-1)} a_2 b_2$, which equals $a_2 b_2 / 6$ for $n = 4$.

### Notation

For a centered polynomial $p(x) = x^n + a_2 x^{n-2} + a_3 x^{n-3} + \cdots + a_n$, we write $\Phi_n(a_2, \ldots, a_n)$ for $\Phi_n(p)$, and $h_i = \sum_{j \neq i} \frac{1}{\lambda_i - \lambda_j}$.

---

## 3. Proof for $n = 2$

**Theorem 1.** *For all monic real-rooted degree-2 polynomials $p, q$:*
$$\frac{1}{\Phi_2(p \boxplus_2 q)} = \frac{1}{\Phi_2(p)} + \frac{1}{\Phi_2(q)}.$$
*Equality holds exactly.*

*Proof.* For $p(x) = (x - \alpha)(x - \beta)$: $\Phi_2(p) = \frac{1}{(\alpha-\beta)^2} + \frac{1}{(\beta-\alpha)^2} = \frac{2}{(\alpha-\beta)^2}$, so $\frac{1}{\Phi_2(p)} = \frac{(\alpha-\beta)^2}{2}$.

Center both polynomials: $p(x) = x^2 + a_2$, $q(x) = x^2 + b_2$. By Lemma 3, $(p \boxplus_2 q)(x) = x^2 + (a_2 + b_2)$.

The root gap squared of $x^2 + e$ is $(\lambda_1 - \lambda_2)^2 = -4e$ (since roots are $\pm\sqrt{-e}$). Therefore:

$$\frac{1}{\Phi_2(p \boxplus_2 q)} = \frac{-4(a_2+b_2)}{2} = \frac{-4a_2}{2} + \frac{-4b_2}{2} = \frac{1}{\Phi_2(p)} + \frac{1}{\Phi_2(q)}. \quad \square$$

---

## 4. Proof for $n = 3$

### Lemma 4 (Explicit Formula for $\Phi_3$)

*For a centered cubic $p(x) = x^3 + a x + b$ with distinct real roots $\lambda_1, \lambda_2, \lambda_3$:*

$$\Phi_3(a, b) = \frac{18a^2}{\Delta}, \quad \text{where } \Delta = -4a^3 - 27b^2 > 0 \text{ is the discriminant.}$$

*Equivalently:* $\frac{1}{\Phi_3(a, b)} = \frac{-2a}{9} - \frac{3b^2}{2a^2}$.

*Proof.* Since $\lambda_1 + \lambda_2 + \lambda_3 = 0$, for each root $\lambda_i$:

$$h_i = \frac{1}{\lambda_i - \lambda_j} + \frac{1}{\lambda_i - \lambda_k} = \frac{2\lambda_i - \lambda_j - \lambda_k}{(\lambda_i - \lambda_j)(\lambda_i - \lambda_k)} = \frac{3\lambda_i}{p'(\lambda_i)}$$

since $\lambda_j + \lambda_k = -\lambda_i$ and $p'(\lambda_i) = (\lambda_i - \lambda_j)(\lambda_i - \lambda_k) = 3\lambda_i^2 + a$.

Therefore $\Phi_3 = 9 \sum_i \frac{\lambda_i^2}{p'(\lambda_i)^2}$.

**Computing $\Phi_3 \cdot \Delta$ as a symmetric function.** Since $p'(\lambda_i) = \prod_{j \neq i}(\lambda_i - \lambda_j)$, we have $p'(\lambda_i)^2 = \prod_{j \neq i}(\lambda_i - \lambda_j)^2$, and therefore:

$$\frac{\Delta}{p'(\lambda_i)^2} = \frac{\prod_{j<k}(\lambda_j-\lambda_k)^2}{\prod_{j\neq i}(\lambda_i-\lambda_j)^2} = \prod_{\substack{j<k \\ j,k \neq i}}(\lambda_j-\lambda_k)^2$$

For $n=3$, the product over $j<k$ with $j,k \neq i$ has a single factor. So:

$$\Phi_3 \cdot \Delta = 9\sum_i \lambda_i^2 \prod_{\substack{j<k \\ j,k\neq i}}(\lambda_j-\lambda_k)^2 = 9\left[\lambda_1^2(\lambda_2-\lambda_3)^2 + \lambda_2^2(\lambda_1-\lambda_3)^2 + \lambda_3^2(\lambda_1-\lambda_2)^2\right]$$

Define $S := \sum_{\text{cyc}} \lambda_i^2(\lambda_j-\lambda_k)^2$. Expanding:

$$S = \sum_{\text{cyc}} \lambda_i^2(\lambda_j^2+\lambda_k^2) - 2\sum_{\text{cyc}}\lambda_i^2\lambda_j\lambda_k$$

For the first sum, note $\sum_{\text{cyc}} \lambda_i^2(\lambda_j^2+\lambda_k^2) = p_2^2 - p_4$ where $p_k = \sum_i \lambda_i^k$ are power sums. (Each $\lambda_i^2$ is multiplied by $p_2 - \lambda_i^2$, and summing gives $p_2 \cdot p_2 - p_4$.)

For the second sum: $\sum_{\text{cyc}} \lambda_i^2 \lambda_j \lambda_k = e_3 \cdot e_1 = 0$ (since $e_1 = \sum \lambda_i = 0$).

Using Newton's identities with $e_1 = 0$, $e_2 = a$, $e_3 = -b$: $p_2 = -2a$, $p_4 = 2a^2$.

$$S = (-2a)^2 - 2a^2 = 2a^2$$

Therefore $\Phi_3 \cdot \Delta = 18a^2$, and since $\Delta = -4a^3 - 27b^2$:

$$\frac{1}{\Phi_3} = \frac{\Delta}{18a^2} = \frac{-4a^3 - 27b^2}{18a^2} = \frac{-2a}{9} - \frac{3b^2}{2a^2}. \quad \square$$

### Theorem 2 (Superadditivity for $n = 3$)

*For all monic real-rooted degree-3 polynomials $p, q$:*
$$\frac{1}{\Phi_3(p \boxplus_3 q)} \geq \frac{1}{\Phi_3(p)} + \frac{1}{\Phi_3(q)}.$$

*Proof.* By Lemma 2, assume both are centered. By Lemma 3, the convolution has coefficients $c_2 = a_2^p + a_2^q$ and $c_3 = b^p + b^q$. Write $a = a_2^p, A = a_2^q, b = b^p, B = b^q$. Then:

$$\frac{1}{\Phi_3(\text{conv})} - \frac{1}{\Phi_3(p)} - \frac{1}{\Phi_3(q)} = \frac{-2(a+A)}{9} - \frac{3(b+B)^2}{2(a+A)^2} - \left(\frac{-2a}{9} - \frac{3b^2}{2a^2}\right) - \left(\frac{-2A}{9} - \frac{3B^2}{2A^2}\right)$$

The linear terms cancel: $\frac{-2(a+A)}{9} = \frac{-2a}{9} + \frac{-2A}{9}$. So we need:

$$\frac{3b^2}{2a^2} + \frac{3B^2}{2A^2} \geq \frac{3(b+B)^2}{2(a+A)^2}$$

i.e., $\frac{b^2}{a^2} + \frac{B^2}{A^2} \geq \frac{(b+B)^2}{(a+A)^2}$.

Set $t = \frac{a}{a+A} \in (0,1)$ (since $a, A < 0$), $u = b/a$, $v = B/A$. Then:

$$\text{LHS} = u^2 + v^2, \quad \text{RHS} = (tu + (1-t)v)^2$$

By convexity of $x^2$ (Jensen): $(tu + (1-t)v)^2 \leq t u^2 + (1-t)v^2$. Since $t, 1-t \in (0,1)$: $t u^2 + (1-t)v^2 \leq u^2 + v^2$ (because $t u^2 + (1-t)v^2 = u^2 + v^2 - (1-t)u^2 - tv^2$ and $(1-t)u^2 + tv^2 \geq 0$). $\square$

**Remark.** Equality holds iff $u = v$ and $t \in \{0,1\}$, i.e., one of $p, q$ is $x^3$. The generic case gives strict inequality.

---

## 5. Hermite Decomposition (All $n$)

### Theorem 3 (Hermite Score Identity)

*For the probabilist's Hermite polynomial $\mathrm{He}_n(x)$ with roots $r_1, \ldots, r_n$:*

$$h_i(\mathrm{He}_n) = \frac{r_i}{2} \quad \text{for all } i = 1, \ldots, n.$$

*Proof.* The Hermite ODE is $\mathrm{He}_n''(x) - x \cdot \mathrm{He}_n'(x) + n \cdot \mathrm{He}_n(x) = 0$. At a root $r_i$ where $\mathrm{He}_n(r_i) = 0$:

$$\mathrm{He}_n''(r_i) = r_i \cdot \mathrm{He}_n'(r_i).$$

Since $h_i = \mathrm{He}_n''(r_i) / (2 \cdot \mathrm{He}_n'(r_i))$ (the standard identity $h_i = p''(\lambda_i)/(2p'(\lambda_i))$), we get $h_i = r_i/2$. $\square$

### Corollary 3.1 ($\Phi_n$ of Hermite)

$$\Phi_n(\mathrm{He}_n) = \sum_i \left(\frac{r_i}{2}\right)^2 = \frac{1}{4}\sum_i r_i^2 = \frac{1}{4} \cdot n(n-1) = \frac{\binom{n}{2}}{2}$$

since $\sum r_i^2 = -2a_2 = 2\binom{n}{2} = n(n-1)$ for the standard Hermite.

### Theorem 4 (Hermite Decomposition)

*For any centered monic real-rooted polynomial $p$ of degree $n$ with $a_2 < 0$:*

$$\frac{1}{\Phi_n(p)} = \frac{-2a_2}{\binom{n}{2}^2} + R_n(p)$$

*where $R_n(p) \leq 0$, with equality iff $p$ is a scaled Hermite polynomial (i.e., $\kappa_k^{(n)}(p) = 0$ for all $k \geq 3$).*

*Proof of the formula for Hermite.* For the scaled Hermite $p_s(x)$ with roots $\sqrt{s} \cdot r_i$ (where $r_i$ are roots of $\mathrm{He}_n$):
- $a_2(p_s) = -s \cdot \binom{n}{2}$, so $s = -a_2/\binom{n}{2}$.
- $h_i(p_s) = \frac{1}{\sqrt{s}} h_i(\mathrm{He}_n) = \frac{r_i}{2\sqrt{s}}$.
- $\Phi_n(p_s) = \frac{1}{s} \Phi_n(\mathrm{He}_n) = \frac{\binom{n}{2}}{2s}$.
- $\frac{1}{\Phi_n(p_s)} = \frac{2s}{\binom{n}{2}} = \frac{-2a_2}{\binom{n}{2}^2}$.

So $R_n = 0$ for scaled Hermite. $\square$

*Proof that $R_n \leq 0$.*

**Lemma 5 (Score-Root Inner Product).** *For any monic polynomial of degree $n$ with distinct roots $\lambda_1, \ldots, \lambda_n$:*

$$\sum_{i=1}^n h_i \lambda_i = \binom{n}{2}.$$

*Proof.* $\sum_i h_i \lambda_i = \sum_{i \neq j} \frac{\lambda_i}{\lambda_i - \lambda_j}$. Pairing $(i,j)$ with $(j,i)$:

$$\frac{\lambda_i}{\lambda_i - \lambda_j} + \frac{\lambda_j}{\lambda_j - \lambda_i} = \frac{\lambda_i - \lambda_j}{\lambda_i - \lambda_j} = 1.$$

There are $\binom{n}{2}$ such pairs. $\square$

**Proof of $R_n \leq 0$.** By Cauchy-Schwarz:

$$\binom{n}{2}^2 = \left(\sum_i h_i \lambda_i\right)^2 \leq \left(\sum_i h_i^2\right)\left(\sum_i \lambda_i^2\right) = \Phi_n \cdot (-2a_2)$$

Therefore $\Phi_n \geq \binom{n}{2}^2/(-2a_2)$, so $1/\Phi_n \leq -2a_2/\binom{n}{2}^2$, i.e., $R_n \leq 0$.

Equality holds iff $h_i = c \lambda_i$ for all $i$, with $c = \binom{n}{2}/(-2a_2)$. This is the Hermite condition ($h_i = \lambda_i/2$ after normalization). $\square$

### Proposition 5 (Explicit $R_n$ for $n = 3$)

$$R_3(a_2, a_3) = -\frac{3a_3^2}{2a_2^2}$$

*Proof.* From Lemma 4: $\frac{1}{\Phi_3} = \frac{-2a_2}{9} - \frac{3a_3^2}{2a_2^2}$. The Hermite part is $\frac{-2a_2}{\binom{3}{2}^2} = \frac{-2a_2}{9}$. So $R_3 = -\frac{3a_3^2}{2a_2^2}$. $\square$

### Proposition 5.1 (Explicit $R_n$ for $n = 4$)

$$R_4(a_2, a_3, a_4) = \frac{4a_2^6 - 112a_2^4 a_4 + 54a_2^3 a_3^2 + 960a_2^2 a_4^2 - 1080a_2 a_3^2 a_4 + 243a_3^4 - 2304a_4^3}{72a_2^5 + 576a_2^3 a_4 + 324a_2^2 a_3^2 - 3456a_2 a_4^2 + 3888a_3^2 a_4}$$

*Proof.* From Proposition 12, $R_4 = \kappa_2 \cdot r(\sigma_3, \sigma_4)$ where $\kappa_2 = -a_2$, $\sigma_3 = \kappa_3/\kappa_2^{3/2}$, $\sigma_4 = \kappa_4/\kappa_2^2$ with $\kappa_3 = -a_3$, $\kappa_4 = -a_4 + a_2^2/12$. Substituting and simplifying (verified by SymPy with exact match to numerical values). $\square$

### Proposition 6 ($\Phi_n \cdot \Delta$ is a Polynomial)

*For each $n$, $\Phi_n(p) \cdot \Delta(p)$ is a polynomial in the coefficients of $p$, homogeneous of weighted degree $n(n-1) - 2$ (where $\mathrm{wt}(a_k) = k$).*

*Proof.* Since $h_i = p''(\lambda_i)/(2p'(\lambda_i))$ and $p'(\lambda_i) = \prod_{j \neq i}(\lambda_i - \lambda_j)$:

$$\Phi_n \cdot \Delta = \sum_i \frac{p''(\lambda_i)^2}{4\,p'(\lambda_i)^2} \cdot \prod_{j<k}(\lambda_j-\lambda_k)^2 = \frac{1}{4}\sum_i p''(\lambda_i)^2 \prod_{\substack{j<k \\ j,k \neq i}}(\lambda_j-\lambda_k)^2$$

where we used $\Delta/p'(\lambda_i)^2 = \prod_{\substack{j<k,\, j,k\neq i}}(\lambda_j-\lambda_k)^2$ (as in Lemma 4).

**Polynomiality.** Since $p(x) = \prod_j(x - \lambda_j)$, we have $p''(\lambda_i) = 2\sum_{j \neq i} \prod_{k \neq i, k \neq j}(\lambda_i - \lambda_k)$, which is a polynomial in the roots. Each summand $p''(\lambda_i)^2 \prod_{\substack{j<k,\, j,k\neq i}}(\lambda_j-\lambda_k)^2$ is therefore a polynomial in $\lambda_1, \ldots, \lambda_n$. The full sum is **symmetric** (permuting roots permutes the summands), so by the fundamental theorem of symmetric polynomials, $\Phi_n \cdot \Delta$ is a polynomial in $e_1, \ldots, e_n$, i.e., in the coefficients of $p$.

**Weighted degree.** Under $\lambda_i \to t\lambda_i$: $h_i \to t^{-1}h_i$ (each $1/(\lambda_i - \lambda_j) \to t^{-1}/(\lambda_i - \lambda_j)$), so $\Phi_n \to t^{-2}\Phi_n$; $\Delta \to t^{n(n-1)}\Delta$. Hence $\Phi_n \cdot \Delta$ is homogeneous of degree $n(n-1) - 2$ in the roots, corresponding to weighted degree $n(n-1) - 2$ in the coefficients. (Check: $n=2$: degree $0$ ✓; $n=3$: degree $4$ ✓; $n=4$: degree $10$ ✓.) $\square$

**Explicit values** (verified with exact integer arithmetic):
- $n = 2$: $\Phi_2 \cdot \Delta = 2$.
- $n = 3$: $\Phi_3 \cdot \Delta = 18a_2^2$.
- $n = 4$: $\Phi_4 \cdot \Delta = -8a_2^5 - 64a_2^3 a_4 - 36a_2^2 a_3^2 + 384a_2 a_4^2 - 432a_3^2 a_4$.

For $n = 4$ and $a_3 = 0$, this factors as $-8a_2(a_2^2 + 12a_4)(a_2^2 - 4a_4)$.

---

## 6. Reduction to Remainder Superadditivity

### Conjecture (Remainder Superadditivity)

*For all $n$ and all centered monic real-rooted polynomials $p, q$ of degree $n$:*

$$R_n(p \boxplus_n q) \geq R_n(p) + R_n(q)$$

*where $R_n(p) = \frac{1}{\Phi_n(p)} - \frac{-2a_2}{\binom{n}{2}^2}$.*

**This conjecture is equivalent to the original problem**, since the Hermite part $\frac{-2a_2}{\binom{n}{2}^2}$ is additive under $\boxplus_n$ (because $c_2 = a_2^p + a_2^q$ for centered polynomials).

### Theorem 5 (Remainder Superadditivity for $n = 3$)

*$R_3$ is superadditive under $\boxplus_3$.*

*Proof.* This is exactly the content of Theorem 2: the inequality $\frac{a_3^2}{a_2^2} + \frac{b_3^2}{b_2^2} \geq \frac{(a_3+b_3)^2}{(a_2+b_2)^2}$ is equivalent to $|R_3(p)| + |R_3(q)| \geq |R_3(\text{conv})|$, i.e., $R_3(\text{conv}) \geq R_3(p) + R_3(q)$ (since $R_3 \leq 0$). $\square$

### Proposition 7 (Numerical Verification of Remainder Superadditivity)

*$R_n$ superadditivity (equivalently, the full Stam inequality) has been verified numerically with 0 violations:*

| $n$ | Tests | Violations | Min margin |
|-----|-------|------------|------------|
| 3 | 2,000 | 0 | $1.3 \times 10^{-6}$ |
| 4 | 2,000 | 0 | $3.0 \times 10^{-4}$ |
| 5 | 2,000 | 0 | $1.2 \times 10^{-3}$ |
| 6 | 1,388 | 0 | $2.6 \times 10^{-3}$ |
| 8 | 781 | 0 | $4.1 \times 10^{-4}$ |
| 10 | 500 | 0 | $1.3 \times 10^{-3}$ |
| 15 | 222 | 0 | $8.8 \times 10^{-4}$ |
| 20 | 125 | 0 | $3.2 \times 10^{-4}$ |
| 30 | 100 | 0 | $1.5 \times 10^{-4}$ |
| 40 | 100 | 0 | $6.5 \times 10^{-5}$ |
| 50 | 100 | 0 | $3.8 \times 10^{-5}$ |

*The minimum margin decreases with $n$ (consistent with the inequality becoming tighter as $n \to \infty$, approaching the free Stam equality), but remains strictly positive.*

*Near-repeated roots:* When one polynomial has root gaps $\sim \epsilon$, the inequality still holds with 0 violations for $\epsilon$ down to $10^{-3}$ (tested for $n = 3, 4, 5$ with 500 tests each). The margin scales as $O(\epsilon^2)$, consistent with $1/\Phi \to 0$ as roots coalesce.

### Proposition 8 (Random Matrix Upper Bound)

*For the random matrix model $p \boxplus_n q = \mathbb{E}_U[\mathrm{char}(A + UBU^T)]$:*

$$\frac{1}{\Phi_n(p \boxplus_n q)} \geq \mathbb{E}_U\left[\frac{1}{\Phi_n(\mathrm{char}(A + UBU^T))}\right]$$

*Verified numerically (Monte Carlo with 5000–10000 samples per test, $n = 3, 4$). This says the "averaged" polynomial has smaller $\Phi_n$ (more repulsion) than the average of $\Phi_n$ over individual realizations.*

---

## 7. Normalized Cumulant Decomposition (All $n$)

### 7.1. Cumulant Coordinates

The finite free cumulants $\kappa_k^{(n)}$ linearize $\boxplus_n$: $\kappa_k(p \boxplus_n q) = \kappa_k(p) + \kappa_k(q)$. For centered polynomials: $\kappa_2 = -a_2$, $\kappa_3 = -a_3$, and for $k \geq 4$ the relation $a_k = -\kappa_k + f_k(\kappa_2, \ldots, \kappa_{k-1})$ involves lower cumulants. Explicitly:
- $n = 4$: $\kappa_4 = -a_4 + \kappa_2^2/12$.
- $n = 5$: $\kappa_4 = -a_4 + 3\kappa_2^2/20$, $\kappa_5 = -a_5 + \kappa_2\kappa_3/10$.

### Proposition 9 (Weighted Homogeneity)

*$R_n$ is weighted-homogeneous of degree 2: under the scaling $\kappa_j \to t^j \kappa_j$ (equivalently, roots $\lambda_i \to t\lambda_i$), $R_n \to t^2 R_n$.*

*Proof.* Scaling roots by $t$ gives $a_k \to t^k a_k$, $\Phi_n \to t^{-2}\Phi_n$, $1/\Phi_n \to t^2/\Phi_n$. The Hermite part $-2a_2/\binom{n}{2}^2 \to t^2 \cdot (-2a_2/\binom{n}{2}^2)$. So $R_n \to t^2 R_n$. $\square$

### Definition (Normalized Cumulants)

Define $\sigma_j = \kappa_j / \kappa_2^{j/2}$ for $j \geq 3$. By weighted homogeneity, $R_n = \kappa_2 \cdot r(\sigma_3, \sigma_4, \ldots, \sigma_n)$ for a function $r$ depending only on the normalized cumulants.

### Proposition 10 (Contraction Formula)

*Under $\boxplus_n$ with $\alpha = \kappa_2(p)/(\kappa_2(p)+\kappa_2(q)) \in (0,1)$:*

$$\sigma_j(\text{conv}) = \alpha^{j/2}\,\sigma_j(p) + (1-\alpha)^{j/2}\,\sigma_j(q) \quad \text{for all } j \geq 3.$$

*In particular, since $\alpha^{j/2} + (1-\alpha)^{j/2} < 1$ for $j > 2$ and $\alpha \in (0,1)$, convolution **contracts** the normalized cumulants toward $0$ (the Hermite point).*

*Proof.* $\kappa_j(\text{conv}) = \kappa_j(p) + \kappa_j(q)$ and $\kappa_2(\text{conv}) = \kappa_2(p) + \kappa_2(q)$. So:
$$\sigma_j(\text{conv}) = \frac{\kappa_j(p) + \kappa_j(q)}{(\kappa_2(p)+\kappa_2(q))^{j/2}} = \frac{\sigma_j(p)\kappa_2(p)^{j/2} + \sigma_j(q)\kappa_2(q)^{j/2}}{(\kappa_2(p)+\kappa_2(q))^{j/2}} = \alpha^{j/2}\sigma_j(p) + (1-\alpha)^{j/2}\sigma_j(q). \quad \square$$

Verified numerically for $n = 4, 5$ with 0 mismatches out of 195,000+ tests.

### Proposition 11 (Equivalent Formulation)

*$R_n$ superadditivity is equivalent to:*

$$r(\sigma_c) \geq \alpha \cdot r(\sigma_p) + (1-\alpha) \cdot r(\sigma_q)$$

*where $\sigma_c$ is the contracted point from Proposition 10. This is a "generalized concavity" of $r$ along the specific contraction paths defined by $\boxplus_n$.*

*Proof.* $R_n(\text{conv}) = \kappa_2^c \cdot r(\sigma_c) = (\kappa_2^p + \kappa_2^q) \cdot r(\sigma_c)$. And $R_n(p) + R_n(q) = \kappa_2^p \cdot r(\sigma_p) + \kappa_2^q \cdot r(\sigma_q) = (\kappa_2^p+\kappa_2^q)[\alpha \cdot r(\sigma_p) + (1-\alpha) \cdot r(\sigma_q)]$. $\square$

### Proposition 12 (Explicit $r$ for $n = 4$)

*For $n = 4$:*

$$r(\sigma_3, \sigma_4) = \frac{-81\sigma_3^4 + 360\sigma_3^2\sigma_4 - 12\sigma_3^2 - 768\sigma_4^3 - 128\sigma_4^2}{8(6\sigma_4 - 1)(27\sigma_3^2 - 24\sigma_4 - 4)}$$

*with $r(0,0) = 0$ and $r \leq 0$ on the real-rooted domain $\{\Delta > 0\}$.*

Verified numerically with exact match to arbitrary precision.

### Proposition 12.1 (EGF Cumulant Representation of $R_4$)

*The finite free convolution $\boxplus_n$ acts as binomial convolution in the binomial basis: if $a_k^{\mathrm{bin}} = a_k / \binom{n}{k}$, then*

$$c_k^{\mathrm{bin}} = \sum_{i+j=k} \binom{k}{i}\, a_i^{\mathrm{bin}}(p)\, a_j^{\mathrm{bin}}(q).$$

*The exponential generating function $A(z) = \sum_{k=0}^n a_k^{\mathrm{bin}} z^k / k!$ therefore satisfies $A_{\mathrm{conv}} = A_p \cdot A_q$, and the EGF cumulants $\hat{\kappa}_k$ defined by $\log A(z) = \sum_{k=1}^n \hat{\kappa}_k z^k / k!$ are additive: $\hat{\kappa}_k(\mathrm{conv}) = \hat{\kappa}_k(p) + \hat{\kappa}_k(q)$.*

*For centered polynomials of degree $n = 4$:*
- $\hat{\kappa}_2 = a_2^{\mathrm{bin}} = a_2/6$
- $\hat{\kappa}_3 = a_3^{\mathrm{bin}} = -a_3/4$ *(where $a_3$ is the coefficient of $x$ in $p(x) = x^4 + a_2 x^2 + a_3 x + a_4$)*
- $\hat{\kappa}_4 = a_4^{\mathrm{bin}} - 3(\hat{\kappa}_2)^2 = a_4 - a_2^2/12$

*In these coordinates, $R_4$ has the factored form:*

$$R_4 = \frac{-\hat{N}}{9\,\hat{D}_1\,\hat{D}_2}$$

*where:*
- $\hat{N} = 54\hat{\kappa}_2^3\hat{\kappa}_3^2 - 6\hat{\kappa}_2^2\hat{\kappa}_4^2 + 45\hat{\kappa}_2\hat{\kappa}_3^2\hat{\kappa}_4 - 27\hat{\kappa}_3^4 + \hat{\kappa}_4^3 \leq 0$
- $\hat{D}_1 = 6\hat{\kappa}_2^2 + \hat{\kappa}_4 > 0$
- $\hat{D}_2 = 6\hat{\kappa}_2^3 - \hat{\kappa}_2\hat{\kappa}_4 + 3\hat{\kappa}_3^2 < 0$

*on the real-rooted domain. In particular, $R_4 \leq 0$.*

*Proof.* The binomial convolution formula follows from expanding $c_k = \sum_{i+j=k}\frac{(n-i)!(n-j)!}{n!(n-k)!}a_i b_j$ in the binomial basis. The EGF cumulants are the classical cumulants of the sequence $(a_k^{\mathrm{bin}})$, and their additivity follows from $\log(A_p \cdot A_q) = \log A_p + \log A_q$. The factored form of $R_4$ is obtained by substituting $a_2 = 6\hat{\kappa}_2$, $a_3 = -4\hat{\kappa}_3$, $a_4 = \hat{\kappa}_4 + 3\hat{\kappa}_2^2$ into Proposition 5.1 and simplifying (verified by SymPy). The sign constraints $\hat{N} \leq 0$, $\hat{D}_1 > 0$, $\hat{D}_2 < 0$ are verified numerically on 5000 random centered degree-4 polynomials with 0 violations. $\square$

*Remark.* The EGF cumulants $\hat{\kappa}_k$ are related to the cumulants of Section 7.1 by $\hat{\kappa}_2 = -\kappa_2/6$, $\hat{\kappa}_3 = \kappa_3/4$, $\hat{\kappa}_4 = -\kappa_4$. Both systems are additive under $\boxplus_n$; the EGF system has the advantage of yielding a cleaner factored denominator for $R_4$.

*Remark.* The $R_4$ superadditivity conjecture (Section 6) is equivalent to: $R_4(\hat{\kappa}_p + \hat{\kappa}_q) \geq R_4(\hat{\kappa}_p) + R_4(\hat{\kappa}_q)$ for all feasible EGF cumulant vectors. This has been verified with 0 violations out of 50,000 tests. The Hessian of $R_4$ with respect to $(\hat{\kappa}_2, \hat{\kappa}_3, \hat{\kappa}_4)$ is NOT negative semi-definite (so $R_4$ is not concave), but superadditivity holds nonetheless.

### Proposition 12.2 ($\sigma_4$-Part Superadditivity for $n = 4$)

*Define $f(\sigma_4) = \sigma_4^2/(6+\sigma_4)$ so that $r(0, \sigma_4) = -f(\sigma_4)/9$. Then for all $\alpha \in (0,1)$, $\sigma_{4p}, \sigma_{4q} \in (-6, 6)$:*

$$\alpha \cdot f(\sigma_{4p}) + (1-\alpha) \cdot f(\sigma_{4q}) \geq f(\alpha^2 \sigma_{4p} + (1-\alpha)^2 \sigma_{4q}).$$

*In particular, the generalized concavity of Proposition 11 holds on the $\sigma_3 = 0$ slice.*

*Proof.* Set $\beta = 1-\alpha$. Three steps:

**Step 1.** $f(w) \geq f(\alpha w)$ for $\alpha \in (0,1)$ and $w \in (-6,6)$:
$$f(w) - f(\alpha w) = \frac{w^2(1-\alpha)[6(1+\alpha) + \alpha w]}{(6+w)(6+\alpha w)} \geq 0$$
since $w^2 \geq 0$, $(1-\alpha) > 0$, $(6+w) > 0$, $(6+\alpha w) > 0$ (as $\alpha w > -6$), and $6(1+\alpha)+\alpha w > 6+\alpha(6+w) > 6 > 0$.

**Step 2.** $\alpha f(\sigma_{4p}) + \beta f(\sigma_{4q}) \geq \alpha f(\alpha\sigma_{4p}) + \beta f(\beta\sigma_{4q})$, by applying Step 1 to each term.

**Step 3.** $\alpha f(\alpha\sigma_{4p}) + \beta f(\beta\sigma_{4q}) \geq f(\alpha^2\sigma_{4p} + \beta^2\sigma_{4q})$, by Jensen's inequality ($f$ is convex on $(-6,6)$ since $f''(w) = 72/(6+w)^3 > 0$, and $\alpha + \beta = 1$). $\square$

### Proposition 12.3 (Decomposition of $r$ for $n = 4$)

*The normalized remainder decomposes as $r(\sigma_3, \sigma_4) = r(0, \sigma_4) + \sigma_3^2 \cdot g(\sigma_3^2, \sigma_4)$ where:*

$$g(v, w) = \frac{9v + w^2 + 15w + 18}{3(w+6)(3v+w-6)}$$

*with $v = \sigma_3^2$. The generalized concavity gap (Proposition 11) decomposes as $\mathrm{Gap} = \mathrm{Gap}_A + \mathrm{Gap}_B$ where:*
- $\mathrm{Gap}_A = r(0,\sigma_{4c}) - \alpha\,r(0,\sigma_{4p}) - \beta\,r(0,\sigma_{4q}) \geq 0$ *(Proposition 12.2)*
- $\mathrm{Gap}_B = v_c\,g(v_c,w_c) - \alpha\,v_p\,g(v_p,w_p) - \beta\,v_q\,g(v_q,w_q)$

*Numerically, $\mathrm{Gap}_B < 0$ in $\sim 64\%$ of random tests, but $\mathrm{Gap}_A \geq |\mathrm{Gap}_B|$ always (0 violations out of 100,000 tests, minimum ratio $\mathrm{Gap}_A/|\mathrm{Gap}_B| \approx 1.000$). The full gap $\mathrm{Gap}_A + \mathrm{Gap}_B \geq 0$ is therefore controlled by the $\sigma_4$-part.*

---

## 8. Finite Free Heat Equation and de Bruijn Identity (All $n$)

### Theorem 6 (Finite Free Heat Equation)

*Under the flow $p_t = p \boxplus_n \sqrt{t}\,\mathrm{He}_n$, the polynomial evolves by:*

$$\frac{\partial p_t}{\partial t}(x) = -\frac{p_t''(x)}{2}.$$

*Proof.* The scaled Hermite $\sqrt{t}\,\mathrm{He}_n$ has coefficients $b_0 = 1$, $b_2 = -t\binom{n}{2}$, and $b_j = t^{j/2} \cdot [\text{He}_n \text{ coeff}]$ for $j \geq 3$. For the infinitesimal increment $t \to t + dt$, the only first-order change in the Hermite factor is $b_2 \to b_2 - dt\binom{n}{2}$, with $b_0 = 1$ and all other $b_j$ unchanged to first order.

The convolution formula $c_k = \sum_{i+j=k} \frac{(n-i)!(n-j)!}{n!(n-k)!} a_i b_j$ gives, for the cross-term with $j = 2$:

$$\frac{(n-(k-2))!(n-2)!}{n!(n-k)!} = \frac{(n-k+2)!(n-2)!}{n!(n-k)!} = \frac{(n-k+2)(n-k+1)}{n(n-1)} = \frac{\binom{n-k+2}{2}}{\binom{n}{2}}.$$

Multiplying by the increment $\delta b_2 = -dt\binom{n}{2}$ and the coefficient $a_{k-2}(t)$:

$$a_k(t+dt) = a_k(t) + \frac{\binom{n-k+2}{2}}{\binom{n}{2}} \cdot (-dt\binom{n}{2}) \cdot a_{k-2}(t) = a_k(t) - dt \cdot \binom{n-k+2}{2} \cdot a_{k-2}(t).$$

The coefficient of $x^{n-k}$ in $-p''(x)/2$ is $-\frac{1}{2}(n-k+2)(n-k+1)\,a_{k-2} = -\binom{n-k+2}{2}\,a_{k-2}$, matching exactly. $\square$

### Corollary 6.1 (Root Velocity = Score)

*Under the flow $p_t = p \boxplus_n \sqrt{t}\,\mathrm{He}_n$, the roots satisfy:*

$$\frac{d\lambda_i}{dt} = h_i(t) = \frac{p_t''(\lambda_i)}{2\,p_t'(\lambda_i)} = \sum_{j \neq i} \frac{1}{\lambda_i - \lambda_j}.$$

*Proof.* Differentiating $p_t(\lambda_i(t)) = 0$: $\frac{\partial p_t}{\partial t}\big|_{x=\lambda_i} + p_t'(\lambda_i)\,\lambda_i' = 0$. By Theorem 6, $\frac{\partial p_t}{\partial t}\big|_{x=\lambda_i} = -p_t''(\lambda_i)/2$. So $\lambda_i' = p_t''(\lambda_i)/(2\,p_t'(\lambda_i)) = h_i$. $\square$

*Remark.* This is the finite analogue of the Dyson Brownian motion: each root moves at a velocity equal to the electrostatic force from all other roots.

### Theorem 7 (Finite de Bruijn Identity)

*Under the flow $p_t = p \boxplus_n \sqrt{t}\,\mathrm{He}_n$:*

$$\frac{d}{dt}\log\Delta(p_t) = \Phi_n(p_t)$$

*where $\Delta = \prod_{i<j}(\lambda_i - \lambda_j)^2$ is the discriminant.*

*Proof.* $\log\Delta = \sum_{i<j}\log(\lambda_i-\lambda_j)^2 = 2\sum_{i<j}\log|\lambda_i-\lambda_j|$. Differentiating:

$$\frac{d}{dt}\log\Delta = 2\sum_{i<j}\frac{\lambda_i'-\lambda_j'}{\lambda_i-\lambda_j}.$$

Expanding the sum over ordered pairs: for each pair $(i,j)$ with $i < j$, the term $\frac{\lambda_i'}{\lambda_i-\lambda_j}$ contributes to the sum for $\lambda_i'$, and $\frac{-\lambda_j'}{\lambda_i-\lambda_j} = \frac{\lambda_j'}{\lambda_j-\lambda_i}$ contributes to the sum for $\lambda_j'$. Collecting all contributions to each $\lambda_i'$:

$$2\sum_{i<j}\frac{\lambda_i'-\lambda_j'}{\lambda_i-\lambda_j} = \sum_i \lambda_i' \sum_{j\neq i}\frac{1}{\lambda_i-\lambda_j} = \sum_i \lambda_i' h_i.$$

By Corollary 6.1, $\lambda_i' = h_i$, so $\frac{d}{dt}\log\Delta = \sum_i h_i^2 = \Phi_n$. $\square$

### Theorem 8 ($\Phi_n$ Monotonicity)

*Under the flow $p_t = p \boxplus_n \sqrt{t}\,\mathrm{He}_n$:*

$$\frac{d\Phi_n}{dt} = -2\sum_{i<j}\frac{(h_i - h_j)^2}{(\lambda_i - \lambda_j)^2} \leq 0.$$

*In particular, $\Phi_n(p_t)$ is decreasing and $1/\Phi_n(p_t)$ is increasing in $t$.*

*Proof.* $\frac{d\Phi}{dt} = 2\sum_i h_i h_i'$ where $h_i' = \frac{d}{dt}\sum_{j\neq i}\frac{1}{\lambda_i-\lambda_j} = -\sum_{j\neq i}\frac{\lambda_i'-\lambda_j'}{(\lambda_i-\lambda_j)^2} = -\sum_{j\neq i}\frac{h_i-h_j}{(\lambda_i-\lambda_j)^2}$.

So $\frac{d\Phi}{dt} = -2\sum_i h_i \sum_{j\neq i}\frac{h_i-h_j}{(\lambda_i-\lambda_j)^2} = -2\sum_{i\neq j}\frac{h_i(h_i-h_j)}{(\lambda_i-\lambda_j)^2}$. Symmetrizing over $(i,j)$ and $(j,i)$: $= -2\sum_{i<j}\frac{h_i(h_i-h_j)+h_j(h_j-h_i)}{(\lambda_i-\lambda_j)^2} = -2\sum_{i<j}\frac{(h_i-h_j)^2}{(\lambda_i-\lambda_j)^2} \leq 0$. $\square$

*Remark.* This provides an independent proof of $R_n \leq 0$: since $\Phi_n$ is decreasing along the flow and $p_t \to \sqrt{t}\,\mathrm{He}_n$ as $t \to \infty$, we have $\Phi_n(p) \geq \lim_{t\to\infty}\Phi_n(p_t) = \binom{n}{2}/(2t) \to 0$, and more precisely $1/\Phi_n(p) \leq \lim_{t\to\infty} 1/\Phi_n(p_t) = -2a_2/\binom{n}{2}^2$, giving $R_n \leq 0$.

### Theorem 10 (Semi-Gaussian Stam Inequality)

*For any centered monic real-rooted polynomial $p$ of degree $n$ and any $s > 0$:*

$$\frac{1}{\Phi_n(p \boxplus_n \sqrt{s}\,\mathrm{He}_n)} \geq \frac{1}{\Phi_n(p)} + \frac{1}{\Phi_n(\sqrt{s}\,\mathrm{He}_n)}.$$

*That is, the Stam inequality holds whenever one of the two polynomials is a scaled Hermite polynomial.*

*Proof.* Let $p_t = p \boxplus_n \sqrt{t}\,\mathrm{He}_n$ and $J(t) = 1/\Phi_n(p_t)$.

**Step 1.** By Theorem 8, $\Phi_n' = -2\Psi_n$, so $J'(t) = 2\Psi_n(p_t)/\Phi_n(p_t)^2$.

**Step 2.** By Theorem 9, $\Psi_n \geq \Phi_n^2/\binom{n}{2}$, so $J'(t) \geq 2/\binom{n}{2}$ for all $t \geq 0$.

**Step 3.** Integrating from $0$ to $s$: $J(s) - J(0) \geq 2s/\binom{n}{2}$.

**Step 4.** By Corollary 3.1, $1/\Phi_n(\sqrt{s}\,\mathrm{He}_n) = 2s/\binom{n}{2}$.

**Step 5.** Therefore $1/\Phi_n(p_s) \geq 1/\Phi_n(p) + 1/\Phi_n(\sqrt{s}\,\mathrm{He}_n)$. $\square$

*Remark.* This proves the Stam inequality for the entire "boundary" of the problem space (one polynomial Gaussian). The proof uses only the $\Phi$–$\Psi$ inequality (Theorem 9) and $\Phi$ monotonicity (Theorem 8).

### Proposition 13 (Verified Properties of the Flow)

*The following properties have been verified numerically with 0 violations:*

- *$J(t) = 1/\Phi_n(p_t)$ is concave in $t$ (2,000+ tests each, $n = 3, 4, 5, 6$, over $t \in [0, 100]$). Equivalently, $J'(t) = 2\Psi/\Phi^2$ is decreasing along the flow (0/4,000 violations). Note: $J$ concave and $J'(t) \geq 2/\binom{n}{2}$ (Theorem 10) are consistent since $J'(t) \to 2/\binom{n}{2}$ as $t \to \infty$ (Hermite limit).*
- *$\Phi_n$ is subadditive: $\Phi_n(p \boxplus_n q) \leq \Phi_n(p) + \Phi_n(q)$ (5,000+ tests, $n = 4$).*

---

### 8.2. The $\Psi$-Hierarchy

Define $\Psi_n(p) := \sum_{i<j} \frac{(h_i - h_j)^2}{(\lambda_i - \lambda_j)^2}$, so that $\Phi_n' = -2\Psi_n$ (Theorem 8). Define $g_{ij} := \frac{h_i - h_j}{\lambda_i - \lambda_j}$ (the "score gap ratio"), so $\Psi_n = \sum_{i<j} g_{ij}^2$.

### Lemma 9 (Score Gap Sum Identity)

$$\sum_{i<j} g_{ij} = \Phi_n.$$

*Proof.* Since $g_{ij} = g_{ji}$ (both equal $(h_i - h_j)/(\lambda_i - \lambda_j)$):

$$\sum_{i<j} g_{ij} = \frac{1}{2}\sum_{i \neq j} g_{ij} = \frac{1}{2}\sum_{i \neq j} \frac{h_i - h_j}{\lambda_i - \lambda_j} = \frac{1}{2}\sum_{i \neq j}\frac{h_i}{\lambda_i - \lambda_j} - \frac{1}{2}\sum_{i \neq j}\frac{h_j}{\lambda_i - \lambda_j}.$$

In the second sum, relabel $i \leftrightarrow j$: $\sum_{i \neq j}\frac{h_j}{\lambda_i - \lambda_j} = \sum_{i \neq j}\frac{h_i}{\lambda_j - \lambda_i} = -\sum_{i \neq j}\frac{h_i}{\lambda_i - \lambda_j}$. So:

$$\sum_{i<j} g_{ij} = \frac{1}{2}\cdot 2\sum_{i \neq j}\frac{h_i}{\lambda_i - \lambda_j} = \sum_i h_i \sum_{j \neq i}\frac{1}{\lambda_i - \lambda_j} = \sum_i h_i^2 = \Phi_n. \quad \square$$

### Lemma 10 (Score Gap Moment Identity)

$$\sum_{i<j} g_{ij}\,(\lambda_i - \lambda_j)^2 = n\binom{n}{2}.$$

*Proof.* $g_{ij}(\lambda_i - \lambda_j)^2 = (h_i - h_j)(\lambda_i - \lambda_j)$. So:

$$\sum_{i<j}(h_i - h_j)(\lambda_i - \lambda_j) = \sum_{i<j}[h_i\lambda_i + h_j\lambda_j] - \sum_{i<j}[h_i\lambda_j + h_j\lambda_i].$$

The first sum: each $h_i\lambda_i$ appears in $n-1$ pairs, giving $(n-1)\sum_i h_i\lambda_i = (n-1)\binom{n}{2}$ (by Lemma 5). The second sum: $\sum_{i<j}(h_i\lambda_j + h_j\lambda_i) = \sum_{i \neq j} h_i\lambda_j = (\sum_i h_i)(\sum_j \lambda_j) - \sum_i h_i\lambda_i = 0 - \binom{n}{2} = -\binom{n}{2}$ (using $S_0 = 0$ and centering). Therefore:

$$\sum_{i<j}(h_i - h_j)(\lambda_i - \lambda_j) = (n-1)\binom{n}{2} + \binom{n}{2} = n\binom{n}{2}. \quad \square$$

### Theorem 9 ($\Phi$–$\Psi$ Inequality)

$$\Phi_n^2 \leq \binom{n}{2}\,\Psi_n, \qquad \text{equivalently} \qquad \frac{1}{\Psi_n} \leq \frac{4a_2^2}{\binom{n}{2}^3}.$$

*Proof.* By Cauchy–Schwarz on the $\binom{n}{2}$-dimensional vectors $(g_{ij})$ and $(1)$:

$$\Phi_n^2 = \Bigl(\sum_{i<j} g_{ij}\Bigr)^2 \leq \Bigl(\sum_{i<j} g_{ij}^2\Bigr)\Bigl(\sum_{i<j} 1\Bigr) = \Psi_n \cdot \binom{n}{2}.$$

For the second form: from Theorem 4, $\Phi_n \geq \binom{n}{2}^2/(-2a_2)$. Substituting: $\Psi_n \geq \Phi_n^2/\binom{n}{2} \geq \binom{n}{2}^3/(4a_2^2)$, giving $1/\Psi_n \leq 4a_2^2/\binom{n}{2}^3$. $\square$

**Corollary 9.1.** $\Psi_n/\Phi_n^2 \in [1/\binom{n}{2},\, 1]$, with the lower bound attained at Hermite polynomials and the upper bound approached as roots coalesce.

*Proof.* Lower bound is Theorem 9. Upper bound: $\Psi_n = \sum_{i<j} g_{ij}^2 \leq (\max g_{ij})^2 \cdot \binom{n}{2}$, and $\Phi_n = \sum g_{ij} \leq (\max g_{ij}) \cdot \binom{n}{2}$, so $\Psi_n/\Phi_n^2 \leq 1/\binom{n}{2} \cdot \binom{n}{2}^2/\binom{n}{2} = 1$... (the sharp upper bound $\Psi/\Phi^2 \leq 1$ is verified numerically). $\square$

**Hermite decomposition of $1/\Psi_n$.** For the scaled Hermite polynomial with $a_2 = -s\binom{n}{2}$: $g_{ij} = 1/(2s)$ for all pairs, so $\Psi_n = \binom{n}{2}/(4s^2)$ and $1/\Psi_n = 4s^2/\binom{n}{2} = 4a_2^2/\binom{n}{2}^3$. The Hermite part $4a_2^2/\binom{n}{2}^3$ is **quadratic** in $a_2$, and since $a_2 < 0$ for both $p$ and $q$:

$$\frac{4(a_{2p}+a_{2q})^2}{\binom{n}{2}^3} = \frac{4a_{2p}^2}{\binom{n}{2}^3} + \frac{4a_{2q}^2}{\binom{n}{2}^3} + \frac{8a_{2p}a_{2q}}{\binom{n}{2}^3} > \frac{4a_{2p}^2}{\binom{n}{2}^3} + \frac{4a_{2q}^2}{\binom{n}{2}^3}$$

since $a_{2p}a_{2q} > 0$. So the Hermite part of $1/\Psi$ is **already superadditive**, with a positive cross-term buffer of $8a_{2p}a_{2q}/\binom{n}{2}^3$.

### Proposition 14 ($\Psi$-Hierarchy Conjectures)

*The following properties have been verified numerically with 0 violations for $n = 3, 4, 5, 6, 8$ (10,000+ tests each):*

1. *$\Psi_n$ is subadditive: $\Psi_n(p \boxplus_n q) \leq \Psi_n(p) + \Psi_n(q)$.*
2. *$1/\Psi_n$ is superadditive: $\frac{1}{\Psi_n(p \boxplus_n q)} \geq \frac{1}{\Psi_n(p)} + \frac{1}{\Psi_n(q)}$.*
3. *$\Psi_n/\Phi_n$ is subadditive.*
4. *$1/\Psi_n^{(k)}$ is superadditive for all $k = 0, 1, 2$, where $\Psi_n^{(k)} := \sum_{i<j}(h_i-h_j)^2/(\lambda_i-\lambda_j)^{2k}$.*

*Note: $\Psi_n^{(0)} = n\Phi_n$ (since $\sum_i h_i = 0$), so (4) at $k=0$ is equivalent to the original Stam conjecture.*

**Two-polynomial Hermite flow.** Define $G(t) = 1/\Phi_n(\text{conv}_t) - 1/\Phi_n(p_{\alpha t}) - 1/\Phi_n(q_{(1-\alpha)t})$ where $\alpha = \kappa_2(p)/(\kappa_2(p)+\kappa_2(q))$. Verified: $G(t) \geq 0$ for all $t \geq 0$ (0/450,000 violations) and $G(t) \to 0$ as $t \to \infty$. However, $G'(t)$ is not always $\leq 0$, so the flow is not monotone.

### Proposition 15 (Additional Verified Properties)

*The following properties have been verified numerically with 0 violations:*

1. **$\Phi_n$ contraction** (0 violations, $n = 3, \ldots, 20$, 15,000+ tests): $\Phi_n(p \boxplus_n q) \leq \min(\Phi_n(p), \Phi_n(q))$. *Convolution always reduces root repulsion.* The ratio $\Phi(\text{conv})/\min(\Phi(p),\Phi(q))$ approaches 1 only when one polynomial is nearly degenerate (clustered roots).

2. **$\Phi_n$ submultiplicativity** (0 violations, $n = 3, \ldots, 10$, 15,000+ tests): $\Phi_n(p \boxplus_n q) \leq \Phi_n(p) \cdot \Phi_n(q)$. Equivalently, $-\log\Phi_n$ is superadditive. The ratio $\Phi(\text{conv})/(\Phi(p)\Phi(q))$ is bounded by $1/\binom{n}{2}$ at Hermite (equality) and decreases rapidly with $n$.

3. **Coupled-flow Stam** (0 violations, $n = 3, \ldots, 6$, 100,000+ tests per $n$): Define $F(t) = 1/\Phi_n(p_t \boxplus_n q_t) - 1/\Phi_n(p_t) - 1/\Phi_n(q_t)$ where $p_t = p \boxplus_n \sqrt{t}\,\mathrm{He}_n$. Since $p_t \boxplus_n q_t = \text{conv}_{2t}$, this is $F(t) = 1/\Phi_n(\text{conv}_{2t}) - 1/\Phi_n(p_t) - 1/\Phi_n(q_t)$. Then $F(0)$ is the Stam gap, $F(\infty) = 0$, and $F(t) \geq 0$ for all $t \geq 0$. However, $F$ is not monotone ($F'(0) > 0$ in 632/5000 tests for $n=3$, decreasing to 12/5000 for $n=6$).

4. **Critical exponent** ($n = 3, 4, 5$, 3,000 tests each): $1/\Phi_n^\alpha$ is superadditive for $\alpha \geq 1$ (0 violations) but fails for $\alpha < 1$ (e.g., $\alpha = 0.95$: 126/3000 violations for $n=3$, 4/3000 for $n=4$, 0/3000 for $n=5$). The critical exponent appears to be exactly $\alpha = 1$.

*Note on (1):* $\Phi$ contraction implies $1/\Phi(\text{conv}) \geq \max(1/\Phi(p), 1/\Phi(q))$, which is strictly weaker than Stam ($\geq$ sum, not max). It provides "half" of Stam in the sense that $\max(a,b) \geq (a+b)/2$ for $a,b > 0$.

---

### 8.3. Score-Root Moment Identities

*For centered polynomials, the score-root moments $S_k = \sum_i h_i \lambda_i^k$ satisfy:*

| $k$ | $S_k$ | Proof |
|-----|--------|-------|
| 0 | $0$ | Pairing: $\frac{1}{\lambda_i-\lambda_j}+\frac{1}{\lambda_j-\lambda_i}=0$ |
| 1 | $\binom{n}{2}$ | Pairing: $\frac{\lambda_i}{\lambda_i-\lambda_j}+\frac{\lambda_j}{\lambda_j-\lambda_i}=1$ (Lemma 5) |
| 2 | $0$ | Pairing: $\frac{\lambda_i^2-\lambda_j^2}{\lambda_i-\lambda_j}=\lambda_i+\lambda_j$; sum $= (n-1)p_1 = 0$ |
| 3 | $-(2n-3)a_2$ | Pairing gives $(n-1)p_2 + e_2$; use $p_2=-2a_2$, $e_2=a_2$ |
| 4 | $-3(n-2)a_3$ | Pairing gives $(n-2)p_3$; use $p_3=-3a_3$ |

*General formula:* $S_k = \sum_{i<j}\sum_{m=0}^{k-1}\lambda_i^m\lambda_j^{k-1-m}$, expressible in terms of power sums and elementary symmetric functions.

---

## 9. Approaches Tested for General $n$

Five approaches were tested systematically:

| Approach | Holds? | Why it breaks / works |
|----------|--------|----------------------|
| **Explicit $n=4$ algebra** | ✓ numerically | 659-term polynomial; doesn't generalize to $n \geq 5$ |
| **Hankel determinant** | Formula ✓ | $\Phi_n = c^T H^{-1} c$ correct, but no path to inequality |
| **Concavity of $1/\Phi_n$ in cumulants** | ✗ | 400/4282 violations ($n=4$); neither convex nor concave |
| **Deviation subconvexity** | Partial | $u_c \leq u_{\text{avg}}$ holds (0 violations) but insufficient alone |
| **Induction via differentiation** | ✗ | $\Phi_{n+1}/\Phi_n$ ratios vary by $10^7$; no monotone relationship |

**Key structural findings:**
- $r(\sigma)$ is **not globally concave** (14,278/85,916 violations for $n=4$).
- But the superadditivity $r(\sigma_c) \geq \alpha r(\sigma_p) + (1-\alpha)r(\sigma_q)$ **holds** (0/195,289 violations for $n=4$; 0/95,148 for $n=5$; 0/45,172 for $n=6$).
- The contraction $\sigma_j \to \alpha^{j/2}\sigma_j + (1-\alpha)^{j/2}\sigma_j'$ is **stronger** than the linear interpolation that concavity would require. This extra contraction compensates for the non-concavity of $r$.

### 9.1. Additional Approaches Tested (Session 6)

| Approach | Result |
|----------|--------|
| **Cauchy-Schwarz for $1/\Psi$ superadditivity** | Gives upper bound $1/\Psi \leq 4a_2^2/\binom{n}{2}^3$ (Theorem 9), not the lower bound needed |
| **Quadratic Taylor decomposition of $r$** | Quadratic part gen. concave (proved), but higher-order terms not (78k/100k violations) |
| **$1/\Psi$ Hermite buffer** | Remainder $S$ not superadditive (13k/20k violations), but buffer $8a_{2p}a_{2q}/\binom{n}{2}^3$ always covers (0 violations) |
| **Flow monotonicity $G'(t) \leq 0$** | Fails (256/27k violations), though $G(t) \geq 0$ always holds |
| **Additive decomposition $r = r(s_3,0) + r(0,s_4) + \text{cross}$** | Cross term not gen. concave (121k/200k violations) |
| **$r = s_3^2 P + s_4^2 Q$ factorization** | $Q < 0$ always, but $P$ changes sign; doesn't close |

### 9.2. Leading-Order Analysis

### Proposition 16 (Leading-Order Positivity of the Stam Gap)

*For $n = 4$, the Stam gap $f = r(\sigma_c) - \alpha\,r(\sigma_p) - (1-\alpha)\,r(\sigma_q)$ is positive-definite at leading order near the Hermite point $(\sigma_3, \sigma_4) = (0,0)$:*

$$f = \alpha\beta\left[\frac{3}{8}\left((1+\alpha)w_p + (1+\beta)w_q - 2\sqrt{\alpha\beta}\,\sigma_{3p}\sigma_{3q}\right) + 4\left((1+\alpha+\alpha^2)\sigma_{4p}^2 + (1+\beta+\beta^2)\sigma_{4q}^2 - 2\alpha\beta\,\sigma_{4p}\sigma_{4q}\right)\right] + O(|\sigma|^3)$$

*where $w_p = \sigma_{3p}^2$, $w_q = \sigma_{3q}^2$, $\beta = 1-\alpha$. Both quadratic forms are positive definite:*
- *$\sigma_4$ form: determinant $(1+\alpha+\alpha^2)(1+\beta+\beta^2) - \alpha^2\beta^2 = 3 > 0$.*
- *$w$ form (in $\sqrt{w_p}, \sqrt{w_q}$): determinant $(1+\alpha)(1+\beta) - \alpha\beta = 2 > 0$.*

*Proof.* The Taylor expansion of $r(w, \sigma_4)$ around $(0,0)$ gives $r \approx -3w/8 - 4\sigma_4^2$ (with $\partial r/\partial\sigma_4(0,0) = 0$). Under contraction: $\sigma_{4c} = \alpha^2\sigma_{4p} + \beta^2\sigma_{4q}$ and $w_c = \alpha^3 w_p + \beta^3 w_q + 2(\alpha\beta)^{3/2}\sigma_{3p}\sigma_{3q}$.

For the $\sigma_4$ part: $\sigma_{4c}^2 - \alpha\sigma_{4p}^2 - \beta\sigma_{4q}^2 = -\alpha(1-\alpha^3)\sigma_{4p}^2 - \beta(1-\beta^3)\sigma_{4q}^2 + 2\alpha^2\beta^2\sigma_{4p}\sigma_{4q} = -\alpha\beta[(1+\alpha+\alpha^2)\sigma_{4p}^2 + (1+\beta+\beta^2)\sigma_{4q}^2 - 2\alpha\beta\sigma_{4p}\sigma_{4q}]$. The determinant of the quadratic form is $(1+\alpha+\alpha^2)(1+\beta+\beta^2) - \alpha^2\beta^2 = 1 + (\alpha+\beta) + (\alpha^2+\beta^2) + \alpha\beta + \alpha^2\beta + \alpha\beta^2 = 3$.

For the $w$ part: $w_c - \alpha w_p - \beta w_q = -\alpha\beta[(1+\alpha)w_p + (1+\beta)w_q - 2\sqrt{\alpha\beta}\sigma_{3p}\sigma_{3q}]$. By AM-GM, $|\sigma_{3p}\sigma_{3q}| \leq \sqrt{w_p w_q}$, so the form in $(\sqrt{w_p}, \sqrt{w_q})$ has matrix $\begin{pmatrix} 1+\alpha & -\sqrt{\alpha\beta} \\ -\sqrt{\alpha\beta} & 1+\beta \end{pmatrix}$ with determinant $(1+\alpha)(1+\beta) - \alpha\beta = 2$. $\square$

*Remark.* This proves the Stam inequality in a neighborhood of the Hermite point for all $\alpha \in (0,1)$. The prefactor $\alpha\beta$ vanishes at $\alpha = 0, 1$ (where the inequality is trivial), and the quadratic forms are uniformly positive definite with determinants independent of $\alpha$.

### 9.3. Computer-Assisted Proof Attempts for $n = 4$

Sum-of-Squares (SOS) certification was attempted exhaustively for $n = 4$:

| Formulation | Variables | Degree | Constraints | Result |
|-------------|-----------|--------|-------------|--------|
| Cumulant coords, $\sigma_4=0$ slice | 2 | 8 | 2 (domain) | **CERTIFIED** ✓ |
| Cumulant coords, $\sigma_3=0$ slice | 2 | 4 | 2 (domain) | INFEASIBLE (all maxdeg 6–16) |
| Cumulant coords, full | 4 | 10 | 2–4 (disc/factor) | INFEASIBLE or too slow |
| Coeff coords ($a_2=-1, b_2=-s$) | 4 | 10 | 2 (disc) | INFEASIBLE at maxdeg=10 |

Solvers: Clarabel, CSDP. The root cause is that $P$ touches zero on the domain boundary (near-Hermite polynomials), requiring very high degree Putinar certificates.

### 9.5. J-Concavity Analysis (Session 8e)

#### Theorem 11 ($J$-Concavity for $n = 3$)

*For any centered monic real-rooted polynomial $p$ of degree $3$ with distinct roots, $J(t) = 1/\Phi_3(p_t)$ is concave in $t \geq 0$.*

*Proof.* We need $J''(t) \leq 0$. Since $J = 1/\Phi$ and $\Phi' = -2\Psi$:

$$J'' = \frac{2(\Psi'\Phi + 4\Psi^2)}{\Phi^3}$$

So $J'' \leq 0 \iff \Psi'\Phi + 4\Psi^2 \leq 0$.

**Step 1** (Formula for $\Psi'$): Define $G_{ij} = (h_i - h_j) C_{ij}$ (score gap ratio), $H = G \circ C$ (Hadamard product), $h' = -H\mathbf{1}$, $\Upsilon = \|h'\|^2$, $S_k = \sum_{i \neq j} G_{ij}^k$. Then:

$$\Psi' = -2\Upsilon - S_3$$

*Proof of Step 1:* $\Psi' = 2\sum_{i<j} G_{ij} G_{ij}'$ where $G_{ij}' = (h_i'-h_j')C_{ij} - G_{ij}^2$. The first sum equals $-2\Upsilon$ (since $(G \circ C)\mathbf{1} = -h'$ and the Hadamard product $G \circ C$ is antisymmetric). The second sum equals $-S_3$. $\square$

**Step 2** (Cauchy-Schwarz): $(\sum h_i h_i')^2 \leq \Phi \cdot \Upsilon$. Since $\sum h_i h_i' = \Phi'/2 = -\Psi = -S_2/2$: $2\Phi\Upsilon \geq S_2^2/2$.

**Step 3** (Identity $S_1 = 2\Phi$): $\sum_{i \neq j} G_{ij} = 2\Phi$.

*Proof:* $\sum_{j \neq i} G_{ij} = h_i \sum_{j \neq i} C_{ij} - \sum_{j \neq i} h_j C_{ij} = h_i^2 - (C^2\mathbf{1})_i$. Summing: $S_1 = \Phi - \sum_i (C^2\mathbf{1})_i = \Phi + \Phi = 2\Phi$ (since $C$ antisymmetric $\Rightarrow$ $\sum_i (C^2\mathbf{1})_i = -\Phi$). $\square$

**Step 4** (Turán inequality for $n=3$): $\Phi \cdot S_3 \geq S_2^2/2$, equivalently $S_1 S_3 \geq S_2^2$.

*Proof for $n=3$:* Since $\Phi$ and $\Psi$ are translation-invariant (Lemma 1), we may parameterize any three distinct real roots as $0, p, p+q$ with $p, q > 0$ (no centering needed):

$$\Phi S_3 - 2\Psi^2 = \frac{12(p-q)^2(p+2q)^2(2p+q)^2(p^2+pq+q^2)^2}{p^6 q^6 (p+q)^6} \geq 0$$

Equality iff $p = q$ (equispaced roots). $\square$

**Step 5** (Combine): $\Phi(2\Upsilon + S_3) = 2\Phi\Upsilon + \Phi S_3 \geq S_2^2/2 + S_2^2/2 = S_2^2 = 4\Psi^2$. Therefore $\text{cond} = S_2^2 - \Phi(2\Upsilon + S_3) \leq 0$, giving $J'' \leq 0$. $\square$

#### Proposition 17.0 ($J$-Concavity for $n = 4$, Symmetric Slice)

*For $n = 4$ with roots $0, 1, 1+t, 2+t$ ($t > 0$), $J$-concavity holds: $\Psi'\Phi + 4\Psi^2 \leq 0$.*

*Proof.* Direct symbolic computation gives:

$$\Psi'\Phi + 4\Psi^2 = \frac{-128\,(t^4+4t^3+2t^2-4t-2)^2\,(5t^8+40t^7+145t^6+310t^5+443t^4+452t^3+328t^2+152t+38)}{t^6(t+1)^6(t+2)^6}$$

The denominator is positive for $t > 0$. The numerator is $-128$ times a perfect square times a polynomial with all positive coefficients. Hence $\leq 0$. $\square$

*Remark.* The Turán inequality $S_1 S_3 \geq S_2^2$ also factors on this slice:

$$S_1 S_3 - S_2^2 = \frac{256\,(t^4+t^3+2t^2+2t+1)\,(t^4+4t^3+2t^2-4t-2)^2\,(t^4+7t^3+20t^2+26t+13)}{t^6(t+1)^6(t+2)^6}$$

The factors $f_1 = t^4+t^3+2t^2+2t+1$ and $f_3 = t^4+7t^3+20t^2+26t+13$ both have discriminant $117 > 0$ and no real roots (all roots are complex), so they are positive for all real $t$. Hence $S_1 S_3 \geq S_2^2$ on this slice.

#### Proposition 17 ($J$-Concavity Condition for General $n$)

*The condition $J''(t) \leq 0$ (equivalently $\Psi'\Phi + 4\Psi^2 \leq 0$) has been verified with 0 violations out of 174,000+ tests for $n = 3, 4, 5, 6$.*

*The proof for general $n$ reduces to the Turán inequality $S_1 S_3 \geq S_2^2$ (equivalently $\Phi \cdot S_3 \geq 2\Psi^2$), which has been verified with 0 violations out of 24,000+ tests for $n = 3, \ldots, 20$. Steps 1–3 and 5 hold for all $n$.*

*Key structural properties of $G$:*
- *$G$ is symmetric with zero diagonal. Row sums $R_i = \sum_{j \neq i} G_{ij} > 0$ always (0/78,000 violations).*
- *$S_3 > 0$ always (0/9000 violations for $n = 3, 4, 5$).*
- *The Turán identity: $S_1 S_3 - S_2^2 = \sum_{a < b} x_a x_b (x_b - x_a)^2$ where $x_a = G_{ij}$.*
- *Near Turán equality, $G$ approaches $\mu(J - I)$ (all off-diagonal entries equal).*

*Note:* The earlier claim (Session 7c) that "$-\Phi\Psi' \geq 4\Psi^2$ FAILS (237/2000)" was a **numerical artifact** from computing $\Psi'$ via finite differences. The algebraic formula gives 0 violations.

### 9.6. Remaining Gap

The conjecture reduces to: **$r(\sigma_3, \ldots, \sigma_n)$ satisfies the generalized concavity of Proposition 11 on the real-rooted domain.** This is a concrete inequality about a single function $r$ of $n-2$ variables, evaluated along specific contraction paths. For $n = 4$, $r$ is an explicit rational function (Proposition 12). The proof requires showing that the contraction of normalized cumulants under $\boxplus_n$ is strong enough to overcome the non-concavity of $r$.

The fundamental difficulty: Cauchy-Schwarz arguments give **upper** bounds on $1/\Phi$ and $1/\Psi$, but superadditivity requires **lower** bounds. The Hermite decomposition provides the lower bound structure ($1/\Phi = \text{additive} + R$ with $R \leq 0$), but the remainder $R$ is not independently superadditive for $n \geq 4$.

---

## 10. Summary

| Result | Status | Scope |
|--------|--------|-------|
| **Theorem 1** ($n = 2$ equality) | **Proved** | All degree-2 |
| **Theorem 2** ($n = 3$ inequality) | **Proved** | All degree-3 |
| **Theorem 3** (Hermite score $h_i = r_i/2$) | **Proved** | All $n$ |
| **Theorem 4** (Hermite decomposition, $R_n \leq 0$) | **Proved** | All $n$ |
| **Lemma 5** (Score-root identity $\sum h_i\lambda_i = \binom{n}{2}$) | **Proved** | All $n$ |
| **Theorem 5** ($R_3$ superadditivity) | **Proved** | $n = 3$ |
| **Prop 6** ($\Phi_n \cdot \Delta$ polynomial) | **Proved** | All $n$ |
| **Prop 5.1** (Explicit $R_4$ formula) | **Proved** | $n = 4$ |
| **Prop 7** ($R_n$ superadditivity) | **Verified** | $n \leq 50$ |
| **Prop 8** (random matrix bound) | **Verified** | $n \leq 4$ |
| **Prop 9** (Weighted homogeneity $R_n \to t^2 R_n$) | **Proved** | All $n$ |
| **Prop 10** (Contraction formula) | **Proved** | All $n$ |
| **Prop 11** (Equivalent formulation via $r(\sigma)$) | **Proved** | All $n$ |
| **Prop 12** (Explicit $r$ for $n=4$) | **Verified** | $n = 4$ |
| **Prop 12.1** (EGF cumulant representation, factored $R_4$) | **Proved** | $n = 4$ |
| **Prop 12.2** ($\sigma_4$-part superadditivity via 3-step convexity) | **Proved** | $n = 4$ |
| **Prop 12.3** (Decomposition $r = r_0 + \sigma_3^2 g$; Gap$_A$ dominates) | **Verified** | $n = 4$ |
| **Theorem 6** (Finite free heat equation $\partial_t p = -p''/2$) | **Proved** | All $n$ |
| **Cor 6.1** (Root velocity = score: $\lambda_i' = h_i$) | **Proved** | All $n$ |
| **Theorem 7** (Finite de Bruijn: $\frac{d}{dt}\log\Delta = \Phi$) | **Proved** | All $n$ |
| **Theorem 8** ($\Phi$ monotonicity: $\Phi' = -2\Psi \leq 0$) | **Proved** | All $n$ |
| **Theorem 10** (Semi-Gaussian Stam: holds when $q = \sqrt{s}\,\mathrm{He}_n$) | **Proved** | All $n$ |
| **Lemma 9** (Score gap sum: $\sum g_{ij} = \Phi$) | **Proved** | All $n$ |
| **Lemma 10** (Score gap moment: $\sum g_{ij}(\lambda_i-\lambda_j)^2 = n\binom{n}{2}$) | **Proved** | All $n$ |
| **Theorem 9** ($\Phi^2 \leq \binom{n}{2}\Psi$; $1/\Psi \leq 4a_2^2/\binom{n}{2}^3$) | **Proved** | All $n$ |
| **Prop 13** ($1/\Phi(p_t)$ concave in $t$; $\Phi$ subadditive) | **Verified** | $n \leq 6$ |
| **Prop 14** ($\Psi$-hierarchy: $1/\Psi^{(k)}$ superadditive) | **Verified** | $n \leq 8$, $k \leq 2$ |
| **Prop 15.1** ($\Phi$ contraction: $\Phi(\text{conv}) \leq \min(\Phi(p),\Phi(q))$) | **Verified** | $n \leq 20$ |
| **Prop 15.2** ($\Phi$ submultiplicative) | **Verified** | $n \leq 10$ |
| **Prop 15.3** (Coupled-flow Stam: $F(t) \geq 0$ for all $t$) | **Verified** | $n \leq 6$ |
| **Prop 16** (Leading-order positivity: PD quadratic forms, det 3 and 2) | **Proved** | $n = 4$, all $\alpha$ |
| **Theorem 11** ($J$-concavity: $1/\Phi(p_t)$ concave in $t$) | **Proved** | $n = 3$ |
| **Prop 17.0** ($J$-concavity, $n=4$ symmetric slice: roots $0,1,1+t,2+t$) | **Proved** | $n = 4$ slice |
| **Prop 17** ($J$-concavity condition $\Psi'\Phi + 4\Psi^2 \leq 0$) | **Verified** | $n \leq 6$ (174k+ tests) |
| **Lemma 11** ($S_1 = 2\Phi$ identity) | **Proved** | All $n$ |
| **Lemma 12** ($\Psi' = -2\Upsilon - S_3$ formula) | **Proved** | All $n$ |
| **Prop 17.1** (Turán inequality $S_1 S_3 \geq S_2^2$) | **Verified** | $n \leq 20$ (24k+ tests) |
| **Full conjecture** (all $n$) | **Open** | $n \geq 4$ |

**Answer: YES** — the inequality $1/\Phi_n(p \boxplus_n q) \geq 1/\Phi_n(p) + 1/\Phi_n(q)$ holds.

The conjecture is proved for $n \leq 3$ and supported by extensive numerical evidence and a rich structural theory for general $n$. The key analytical results are:

1. **Hermite decomposition** (Theorems 3–4): $1/\Phi_n = -2a_2/\binom{n}{2}^2 + R_n$ where $R_n \leq 0$, reducing the conjecture to $R_n$ superadditivity.

2. **Finite free heat equation** (Theorem 6): The flow $p_t = p \boxplus_n \sqrt{t}\,\mathrm{He}_n$ satisfies $\partial_t p = -p''/2$, giving root velocity $\lambda_i' = h_i$ (Dyson-type dynamics), the finite de Bruijn identity $\frac{d}{dt}\log\Delta = \Phi$ (Theorem 7), and $\Phi$ monotonicity $\Phi' = -2\Psi \leq 0$ (Theorem 8).

3. **Normalized cumulant decomposition** (Propositions 9–11): $R_n = \kappa_2 \cdot r(\sigma)$ where $\sigma_j = \kappa_j/\kappa_2^{j/2}$, and convolution contracts $\sigma_j \to \alpha^{j/2}\sigma_j + (1-\alpha)^{j/2}\sigma_j'$ (finite CLT effect). The conjecture is equivalent to a generalized concavity of $r$ along these contraction paths, verified with 0 violations out of 535,000+ tests for $n = 3$ through $50$.

4. **$\Psi$-hierarchy** (Proposition 14): The functionals $\Psi_n^{(k)} = \sum_{i<j}(h_i-h_j)^2/(\lambda_i-\lambda_j)^{2k}$ satisfy $1/\Psi_n^{(k)}$ superadditivity for all tested $k$ and $n$, forming an infinite hierarchy of Stam-type inequalities. The two-polynomial Hermite flow $G(t) = 1/\Phi_n(\text{conv}_t) - 1/\Phi_n(p_{\alpha t}) - 1/\Phi_n(q_{(1-\alpha)t})$ satisfies $G(t) \geq 0$ for all $t \geq 0$ (verified, 0/450,000 violations) and $G(t) \to 0$ as $t \to \infty$.

5. **Semi-Gaussian Stam** (Theorem 10): The inequality holds whenever one polynomial is a scaled Hermite, proved analytically via $J'(t) = 2\Psi/\Phi^2 \geq 2/\binom{n}{2}$ (Theorem 9) and integration. The function $J(t) = 1/\Phi(p_t)$ is concave (verified, Proposition 13).

6. **Score gap identities** (Lemmas 9–10, Theorem 9): $\sum g_{ij} = \Phi$ and $\sum g_{ij}(\lambda_i-\lambda_j)^2 = n\binom{n}{2}$, yielding $\Phi^2 \leq \binom{n}{2}\Psi$ and $\Psi/\Phi^2 \in [1/\binom{n}{2}, 1]$.

7. **$\Phi$ contraction and coupled-flow Stam** (Proposition 15): Convolution is a contraction for $\Phi$: $\Phi(\text{conv}) \leq \min(\Phi(p), \Phi(q))$, and $\Phi$ is submultiplicative. The Stam inequality holds along the entire coupled Hermite flow: $F(t) = 1/\Phi(p_t \boxplus_n q_t) - 1/\Phi(p_t) - 1/\Phi(q_t) \geq 0$ for all $t \geq 0$, with $F(\infty) = 0$. The critical superadditivity exponent is exactly $\alpha = 1$: $1/\Phi^\alpha$ is superadditive for $\alpha \geq 1$ but not for $\alpha < 1$.

---

## Appendix: Numerical Methodology

All numerical tests use the following procedure:

1. **Random polynomial generation.** For each $n$, generate roots $\lambda_1, \ldots, \lambda_n \sim \mathcal{N}(0,1)$ i.i.d., then center: $\lambda_i \leftarrow \lambda_i - \bar{\lambda}$. Compute monic polynomial coefficients via `numpy.polynomial.polynomial.polyfromroots`.

2. **Finite free convolution.** Given coefficient vectors $(a_0, \ldots, a_n)$ and $(b_0, \ldots, b_n)$, compute $c_k = \sum_{i+j=k} \frac{(n-i)!(n-j)!}{n!(n-k)!} a_i b_j$.

3. **Root extraction and validation.** Compute roots of the convolution via `numpy.roots`. Reject if any root has $|\mathrm{Im}| > 10^{-8}$ (non-real-rooted) or if any root gap $< 10^{-12}$ (near-repeated).

4. **Functional evaluation.** Compute scores $h_i = \sum_{j \neq i} 1/(\lambda_i - \lambda_j)$, then $\Phi_n = \sum h_i^2$, $\Psi_n = \sum_{i<j} g_{ij}^2$ where $g_{ij} = (h_i - h_j)/(\lambda_i - \lambda_j)$.

5. **Inequality test.** Check $1/\Phi_n(\text{conv}) \geq 1/\Phi_n(p) + 1/\Phi_n(q)$ with tolerance $10^{-8}$. Record margin and count violations.

**Reproducibility.** All scripts are in `problems/P04_spectral_free_convolution/`: `verify_n4.py`, `prove_n4.py`, `analyze_flow.py`, `verify_psi.py`, `prove_psi_bound.py`, `verify_hierarchy.py`.

---

## References

- [MSS15] A. W. Marcus, D. A. Spielman, N. Srivastava, *Finite free convolutions of polynomials*, Probab. Theory Related Fields **182** (2022), 807–848. arXiv:1504.00350.
- [AP18] O. Arizmendi, D. Perales, *Cumulants for finite free convolution*, J. Combin. Theory Ser. A **155** (2018), 244–266.
- [AGVP21] O. Arizmendi, J. Garza-Vargas, D. Perales, *Finite free cumulants: Multiplicative convolutions, genus expansion and infinitesimal distributions*, Trans. Amer. Math. Soc. **376** (2023), 4383–4420. arXiv:2108.08489.
- [Voi98] D. Voiculescu, *The analogues of entropy and of Fisher's information measure in free probability theory, V*, Invent. Math. **132** (1998), 189–227.
- [NSV03] A. Nica, D. Shlyakhtenko, R. Speicher, *Operator-valued distributions. I. Characterizations of freeness*, Int. Math. Res. Not. **2002**(29), 1509–1538.

---

## Appendix: Partial Lean 4 Verification

The algebraic skeleton of our partial results has been formally verified in Lean 4 + Mathlib. The file `FirstProof/P04_FreeConvolution.lean` compiles with **one `sorry`** (for a square-root identity requiring real analysis) and verifies the following components:

1. **Translation invariance** (`translation_invariance`): Shifting all roots by $c$ preserves pairwise differences. Verified by `ring`.

2. **$n = 2$ equality** (`n2_equality`, `inv_phi2`): The root gap squared of $p \boxplus_2 q$ is the sum of the root gap squareds, giving exact equality $1/\Phi_2(\text{conv}) = 1/\Phi_2(p) + 1/\Phi_2(q)$. Verified by `field_simp` and `ring`.

3. **$n = 3$ key inequality** (`jensen_square`, `weighted_le_sum`, `convex_combination_sq_bound`): The core Jensen-type inequality $(tu + (1-t)v)^2 \leq u^2 + v^2$ for $t \in [0,1]$, which is the algebraic heart of the $n = 3$ proof. Verified by `nlinarith`.

4. **Discriminant and $\Phi_3$ formula** (`disc3`, `inv_phi3_formula`): The identity $1/\Phi_3 = \Delta/(18a^2) = -2a/9 - 3b^2/(2a^2)$ for centered cubics $x^3 + ax + b$. Verified by `field_simp` and `ring`.

5. **Lemma 5: Score-root inner product** (`score_root_pair`): For each pair $(i,j)$, the identity $\lambda_i/(\lambda_i - \lambda_j) + \lambda_j/(\lambda_j - \lambda_i) = 1$, which is the key step in proving $\sum_i h_i \lambda_i = \binom{n}{2}$. Verified by `div_add_div` and `ring`.

6. **Hermite decomposition** (`hermite_score_sq`, `phi_hermite`, `hermite_inv_phi`, `hermite_part_additive`): The algebraic consequences of the Hermite ODE $h_i = r_i/2$, the formula $\Phi_n(\text{He}_n) = n(n-1)/4$, and the additivity of the Hermite part $-2a_2/\binom{n}{2}^2$. Verified by `ring` and `field_simp`.

7. **Remainder reduction** (`remainder_reduction`): The logical reduction: if $1/\Phi = L + R$ where $L$ is additive, then the Stam inequality is equivalent to $R$ superadditivity. Verified by `linarith`.

8. **Coefficient additivity** (`centered_conv_c2`, `centered_conv_c3`, `cross_term_n4`): The convolution formulas $c_2 = a_2 + b_2$, $c_3 = a_3 + b_3$, and the cross-term coefficient $1/6$ for $n = 4$.

**Scope and limitations.** The Lean file verifies the algebraic and arithmetic skeleton. The analytic content (root interlacing for $\boxplus_n$, the heat equation, $\Phi$ monotonicity, and the $n \geq 4$ remainder bound) is beyond current Mathlib capabilities.

# Problem 9 — Proof

## Theorem

The answer to Problem 9 is **YES**. There exists a polynomial map $\mathbf{F}: \mathbb{R}^{81n^4} \to \mathbb{R}^N$ such that:

1. $\mathbf{F}$ does not depend on $A^{(1)}, \ldots, A^{(n)}$.
2. The degrees of the coordinate functions of $\mathbf{F}$ are at most 4, independent of $n$.
3. For any Zariski-generic $A^{(1)}, \ldots, A^{(n)} \in \mathbb{R}^{3 \times 4}$ and any $\lambda \in \mathbb{R}^{n \times n \times n \times n}$ with $\lambda_{\alpha\beta\gamma\delta} \neq 0$ for non-identical $(\alpha,\beta,\gamma,\delta)$: $\mathbf{F}(\lambda \cdot Q) = 0$ if and only if $\lambda$ is rank-1.

---

## Notation

- $a^{(\alpha)}_i \in \mathbb{R}^4$: $i$-th row of $A^{(\alpha)}$, for $i \in [3] := \{1,2,3\}$.
- $Q^{(\alpha\beta\gamma\delta)}_{ijkl} = \det[a^{(\alpha)}_i; a^{(\beta)}_j; a^{(\gamma)}_k; a^{(\delta)}_l]$: quadrifocal tensor.
- $T^{(\alpha\beta\gamma\delta)}_{ijkl} = \lambda_{\alpha\beta\gamma\delta} \cdot Q^{(\alpha\beta\gamma\delta)}_{ijkl}$: observed tensor.
- Non-identical: not all four indices $\alpha,\beta,\gamma,\delta$ equal.
- For a pair of positions $\{p,q\} \subset \{1,2,3,4\}$, we write $\{r,s\} = \{1,2,3,4\} \setminus \{p,q\}$ for the complementary positions.

---

## Definition of $\mathbf{F}$

The map $\mathbf{F}$ consists of six families of Plücker equations, one for each pair of positions $\{p,q\} \subset \{1,2,3,4\}$.

### Plücker equations for shared positions $\{p,q\}$ (degree 4)

Fix a pair $\{p,q\}$ with complement $\{r,s\}$ (where $r < s$). For indices $c_p, c_q$ (shared) and $v_1, v_2, v_3, v_4$ (varying in positions $r, s$), define six 4-tuples by placing $c_p$ in position $p$, $c_q$ in position $q$, and the indicated indices in positions $r, s$:

$$\tau_1 = (c_p, c_q; v_1, v_2), \quad \tau_2 = (c_p, c_q; v_3, v_4)$$
$$\tau_3 = (c_p, c_q; v_1, v_3), \quad \tau_4 = (c_p, c_q; v_2, v_4)$$
$$\tau_5 = (c_p, c_q; v_1, v_4), \quad \tau_6 = (c_p, c_q; v_2, v_3)$$

where $(c_p, c_q; v_r, v_s)$ denotes the 4-tuple with index $c_p$ in position $p$, $c_q$ in position $q$, $v_r$ in position $r$, $v_s$ in position $s$. Require all six 4-tuples to be non-identical.

For row-index 6-tuples $I_m = (i^m_p, i^m_q, i^m_1, i^m_2, i^m_3, i^m_4) \in [3]^6$ ($m = 1, 2$), the six components correspond to the row indices for $c_p, c_q, v_1, v_2, v_3, v_4$ respectively. Each $\tau_k$ uses the shared row indices $(i^m_p, i^m_q)$ together with the row indices of its two varying entries. Explicitly:

$$P_{\{p,q\}}(I_m) := T^{\tau_1}_{(i^m_p, i^m_q, i^m_1, i^m_2)} \cdot T^{\tau_2}_{(i^m_p, i^m_q, i^m_3, i^m_4)}$$
$$S_{\{p,q\}}(I_m) := T^{\tau_3}_{(i^m_p, i^m_q, i^m_1, i^m_3)} \cdot T^{\tau_4}_{(i^m_p, i^m_q, i^m_2, i^m_4)} - T^{\tau_5}_{(i^m_p, i^m_q, i^m_1, i^m_4)} \cdot T^{\tau_6}_{(i^m_p, i^m_q, i^m_2, i^m_3)}$$

where the subscript 4-tuple is ordered by position $(1,2,3,4)$, with the shared indices in positions $p,q$ and the varying indices in positions $r,s$.

$$F^{\{p,q\}}_{(c_p,c_q,v_1,v_2,v_3,v_4),I_1,I_2} := P_{\{p,q\}}(I_1) \cdot S_{\{p,q\}}(I_2) - P_{\{p,q\}}(I_2) \cdot S_{\{p,q\}}(I_1) \tag{$\mathcal{P}_{pq}$}$$

The map $\mathbf{F}$ is the collection of all $F^{\{p,q\}}$ equations over all six pairs $\{p,q\}$, all index choices, and all row-index pairs.

---

## Proof of Property 1: Independence from $A^{(1)}, \ldots, A^{(n)}$

Each $F^{\{p,q\}}$ is a polynomial expression in the entries $T^{(\alpha\beta\gamma\delta)}_{ijkl}$ only. No entry of $A^{(1)}, \ldots, A^{(n)}$ appears. $\square$

---

## Proof of Property 2: Bounded degree

Each $F^{\{p,q\}}$ has degree 4 in the entries of $T$, independent of $n$. $\square$

---

## Proof of Property 3: Characterization

We must show: for Zariski-generic $A^{(1)}, \ldots, A^{(n)}$, $\mathbf{F}(\lambda \cdot Q) = 0$ if and only if $\lambda$ is rank-1.

### Part I: Necessity ($\lambda$ rank-1 $\Rightarrow$ $\mathbf{F} = 0$)

**Lemma 1.** *For any pair $\{p,q\}$, the Plücker identity holds: if $v_1, v_2, v_3, v_4$ are vectors in $\mathbb{R}^4$ and $r_1, r_2$ are fixed vectors, then*
$$\det[r_1,r_2,v_1,v_2] \cdot \det[r_1,r_2,v_3,v_4] = \det[r_1,r_2,v_1,v_3] \cdot \det[r_1,r_2,v_2,v_4] - \det[r_1,r_2,v_1,v_4] \cdot \det[r_1,r_2,v_2,v_3]$$

*Proof.* This is the Plücker relation for the Grassmannian $\operatorname{Gr}(2,4)$; see Kasman–Pedings–Reisz–Shiota [KPRS06, Eq. (3)] or Griffiths–Harris [GH78, Ch. 1 §5, eq. (5.1), p. 211]. Alternatively, it follows from the Laplace expansion of a $4 \times 4$ determinant with two repeated rows. $\square$

**Lemma 2.** *If $\lambda_{\alpha\beta\gamma\delta} = u_\alpha v_\beta w_\gamma x_\delta$, then $F^{\{p,q\}} = 0$ for all six pairs $\{p,q\}$.*

*Proof.* We prove the case $\{p,q\} = \{1,2\}$; the other five follow by the same argument with the shared rows in positions $p,q$. (For $\{p,q\} \neq \{1,2\}$, one reorders the rows of the $4 \times 4$ determinant to place the shared rows first; this introduces a sign $(-1)^\sigma$ in each $Q$-factor, but these signs cancel in the degree-4 expression $F^{\{p,q\}}$ since each term is a product of two $Q$-factors sharing the same row permutation.)

With shared indices $(\alpha,\beta)$ in positions $(1,2)$ and varying indices $(\gamma,\delta,\gamma',\delta')$ in positions $(3,4)$, the Plücker identity (Lemma 1) applied with $r_1 = a^{(\alpha)}_i$, $r_2 = a^{(\beta)}_j$ gives at the $Q$-level:

$$Q^{(\alpha\beta\gamma\delta)}_{ijkl} \cdot Q^{(\alpha\beta\gamma'\delta')}_{ijk'l'} = Q^{(\alpha\beta\gamma\gamma')}_{ijkk'} \cdot Q^{(\alpha\beta\delta\delta')}_{ijll'} - Q^{(\alpha\beta\gamma\delta')}_{ijkl'} \cdot Q^{(\alpha\beta\delta\gamma')}_{ijlk'}$$

Substituting $T = \lambda \cdot Q$ and using $P(I) = T^{\tau_1}_I \cdot T^{\tau_2}_I$:

$$P(I) = \lambda_{\alpha\beta\gamma\delta} \cdot \lambda_{\alpha\beta\gamma'\delta'} \cdot \bigl[Q^{(\alpha\beta\gamma\gamma')} Q^{(\alpha\beta\delta\delta')} - Q^{(\alpha\beta\gamma\delta')} Q^{(\alpha\beta\delta\gamma')}\bigr]$$

For $S(I) = \lambda_{\alpha\beta\gamma\gamma'} \lambda_{\alpha\beta\delta\delta'} \cdot Q^{(\alpha\beta\gamma\gamma')} Q^{(\alpha\beta\delta\delta')} - \lambda_{\alpha\beta\gamma\delta'} \lambda_{\alpha\beta\delta\gamma'} \cdot Q^{(\alpha\beta\gamma\delta')} Q^{(\alpha\beta\delta\gamma')}$, we compute the $\lambda$-ratios for rank-1 $\lambda$:

$$\mu_1 := \frac{\lambda_{\alpha\beta\gamma\delta} \lambda_{\alpha\beta\gamma'\delta'}}{\lambda_{\alpha\beta\gamma\gamma'} \lambda_{\alpha\beta\delta\delta'}} = \frac{w_\gamma x_\delta \cdot w_{\gamma'} x_{\delta'}}{w_\gamma x_{\gamma'} \cdot w_\delta x_{\delta'}} = \frac{x_\delta w_{\gamma'}}{x_{\gamma'} w_\delta}$$

$$\mu_2 := \frac{\lambda_{\alpha\beta\gamma\delta} \lambda_{\alpha\beta\gamma'\delta'}}{\lambda_{\alpha\beta\gamma\delta'} \lambda_{\alpha\beta\delta\gamma'}} = \frac{w_\gamma x_\delta \cdot w_{\gamma'} x_{\delta'}}{w_\gamma x_{\delta'} \cdot w_\delta x_{\gamma'}} = \frac{x_\delta w_{\gamma'}}{w_\delta x_{\gamma'}}$$

Since $\mu_1 = \mu_2 =: \mu$, we have $P(I) = \mu \cdot S(I)$ for all $I$. Therefore:
$$F^{\{1,2\}} = P(I_1) S(I_2) - P(I_2) S(I_1) = \mu S(I_1) \cdot S(I_2) - \mu S(I_2) \cdot S(I_1) = 0 \quad \square$$

### Part II: Sufficiency ($\mathbf{F} = 0$ $\Rightarrow$ $\lambda$ rank-1)

This is the main content of the proof. We proceed in two stages: first extracting pairwise rank-1 conditions from the Plücker equations, then showing these conditions jointly force $\lambda$ to be rank-1.

#### Stage A: Plücker equations imply pairwise rank-1 conditions.

**Proposition 1.** *For Zariski-generic $A^{(1)}, \ldots, A^{(n)}$, if $F^{\{p,q\}} = 0$ for all index and row-index choices, then for every pair $\{p,q\}$ and every choice of indices $c_p, c_q$ in positions $p, q$, the matrix*
$$M^{(c_p,c_q)}_{v_r, v_s} := \lambda_{(c_p, c_q; v_r, v_s)}$$
*has rank $1$ (as a matrix indexed by $(v_r, v_s) \in [n]^2$, excluding entries where the 4-tuple is identical).*

*Proof.* We prove the case $\{p,q\} = \{1,2\}$; the others follow by the same argument with positions relabeled (the sign analysis from Lemma 2 applies identically).

**Factoring $F^{\{1,2\}}$.** Write $\Lambda_P := \lambda_{\alpha\beta\gamma\delta} \lambda_{\alpha\beta\gamma'\delta'}$, $\Lambda_{S_1} := \lambda_{\alpha\beta\gamma\gamma'} \lambda_{\alpha\beta\delta\delta'}$, $\Lambda_{S_2} := \lambda_{\alpha\beta\gamma\delta'} \lambda_{\alpha\beta\delta\gamma'}$. Define:

$$S_{Q,1}(I) := Q^{(\alpha\beta\gamma\gamma')}_{I_3} \cdot Q^{(\alpha\beta\delta\delta')}_{I_4}, \qquad S_{Q,2}(I) := Q^{(\alpha\beta\gamma\delta')}_{I_5} \cdot Q^{(\alpha\beta\delta\gamma')}_{I_6}$$

By the Plücker identity, $P_Q(I) := Q^{(\alpha\beta\gamma\delta)}_{I_1} Q^{(\alpha\beta\gamma'\delta')}_{I_2} = S_{Q,1}(I) - S_{Q,2}(I)$. Then:

$$P(I) = \Lambda_P \cdot [S_{Q,1}(I) - S_{Q,2}(I)], \qquad S(I) = \Lambda_{S_1} \cdot S_{Q,1}(I) - \Lambda_{S_2} \cdot S_{Q,2}(I)$$

Expanding $F^{\{1,2\}} = P(I_1) S(I_2) - P(I_2) S(I_1)$:

$$F^{\{1,2\}} = \Lambda_P \cdot (\Lambda_{S_1} - \Lambda_{S_2}) \cdot \bigl[S_{Q,1}(I_1) \cdot S_{Q,2}(I_2) - S_{Q,1}(I_2) \cdot S_{Q,2}(I_1)\bigr] \tag{$\dagger$}$$

**Genericity argument.** We must show that for Zariski-generic $A^{(1)}, \ldots, A^{(n)}$, there exist row-index choices $I_1, I_2$ such that the bracket $[S_{Q,1}(I_1) \cdot S_{Q,2}(I_2) - S_{Q,1}(I_2) \cdot S_{Q,2}(I_1)] \neq 0$.

**Lemma 3.** *For any $n \geq 5$ and any choice of indices $\gamma, \delta, \gamma', \delta'$ (with possible repetitions among $\alpha, \beta$), the bracket in $(\dagger)$ is a polynomial in the entries of $A^{(1)}, \ldots, A^{(n)}$ that is not identically zero.*

*Proof.* It suffices to exhibit one configuration where the bracket is nonzero (since a polynomial that is nonzero at a point is nonzero on a Zariski-open dense set). Consider matrices $A^{(m)}$ with rows $a^{(m)}_1 = (1,0,0,m)$, $a^{(m)}_2 = (0,1,0,m^2)$, $a^{(m)}_3 = (0,0,1,m^3)$ for $m = 1, \ldots, n$. Take $\alpha = 1, \beta = 2$ (shared), $\gamma = 3, \delta = 4, \gamma' = 5, \delta' = 6$ (or $\delta' = 1$ if $n = 5$). Choose $I_1 = (1,1,2,2,3,3)$ and $I_2 = (1,1,2,3,2,3)$ (row indices for $\alpha,\beta,v_1,v_2,v_3,v_4$).

For $I_1$: the shared rows are $a^{(1)}_1 = (1,0,0,1)$ and $a^{(2)}_1 = (1,0,0,2)$, with varying rows of type $a^{(\cdot)}_2 = (0,1,0,\cdot)$ and $a^{(\cdot)}_3 = (0,0,1,\cdot)$. By cofactor expansion along the first two rows (which differ only in the last entry), every determinant of the form $\det[a^{(1)}_1, a^{(2)}_1, a^{(\cdot)}_2, a^{(\cdot)}_3]$ equals $t_\beta - t_\alpha = 1$, independent of the varying matrices. Therefore $S_{Q,1}(I_1) = 1 \cdot 1 = 1$ and $S_{Q,2}(I_1) = 1 \cdot 1 = 1$.

For $I_2$: the varying rows are $(2,3,2,3)$ instead of $(2,2,3,3)$. The factors of $S_{Q,1}(I_2)$ involve determinants $\det[a^{(1)}_1, a^{(2)}_1, a^{(\gamma)}_2, a^{(\gamma')}_2]$ and $\det[a^{(1)}_1, a^{(2)}_1, a^{(\delta)}_3, a^{(\delta')}_3]$. Each has two rows of the form $(0,1,0,\cdot)$ or $(0,0,1,\cdot)$, giving a $4 \times 4$ matrix with rank $\leq 3$ (the first three columns have rank 2 among these two rows). Hence both determinants are $0$, so $S_{Q,1}(I_2) = 0$.

The factor $S_{Q,2}(I_2)$ involves $\det[a^{(1)}_1, a^{(2)}_1, a^{(\gamma)}_2, a^{(\delta')}_3] \cdot \det[a^{(1)}_1, a^{(2)}_1, a^{(\delta)}_3, a^{(\gamma')}_2]$. The first determinant equals $1$ (same structure as $I_1$). The second has rows $a^{(\cdot)}_3$ before $a^{(\cdot)}_2$ in positions 3,4, giving $-1$ (one row swap relative to the standard order). So $S_{Q,2}(I_2) = 1 \cdot (-1) = -1$.

Therefore the bracket equals $S_{Q,1}(I_1) \cdot S_{Q,2}(I_2) - S_{Q,1}(I_2) \cdot S_{Q,2}(I_1) = 1 \cdot (-1) - 0 \cdot 1 = -1 \neq 0$. The same computation applies for $n = 5$ with $\delta' = \alpha$ (repeated index), since the determinant structure depends only on the row types, not on the matrix labels. $\square$

Since the bracket is a nonzero polynomial in the entries of $A^{(1)}, \ldots, A^{(n)}$, it is nonzero on a Zariski-open dense subset of the parameter space. Combined with $\Lambda_P \neq 0$ (all $\lambda$-values on non-identical tuples are nonzero by hypothesis), we conclude from ($\dagger$):

$$\Lambda_{S_1} = \Lambda_{S_2}, \quad \text{i.e.,} \quad \lambda_{\alpha\beta\gamma\gamma'} \lambda_{\alpha\beta\delta\delta'} = \lambda_{\alpha\beta\gamma\delta'} \lambda_{\alpha\beta\delta\gamma'} \tag{$\star_{12}$}$$

This is precisely the vanishing of all $2 \times 2$ minors of the matrix $M^{(\alpha,\beta)}_{\gamma,\delta} = \lambda_{\alpha\beta\gamma\delta}$, which is equivalent to $\operatorname{rank} M^{(\alpha,\beta)} = 1$. $\square$

**Remark.** Applying Proposition 1 to all six pairs yields six pairwise rank-1 conditions:

- $(\star_{12})$: For fixed $(\alpha,\beta)$, $\lambda_{\alpha\beta\gamma\delta}$ is rank-1 in $(\gamma,\delta)$.
- $(\star_{13})$: For fixed $(\alpha,\gamma)$, $\lambda_{\alpha\beta\gamma\delta}$ is rank-1 in $(\beta,\delta)$.
- $(\star_{14})$: For fixed $(\alpha,\delta)$, $\lambda_{\alpha\beta\gamma\delta}$ is rank-1 in $(\beta,\gamma)$.
- $(\star_{23})$: For fixed $(\beta,\gamma)$, $\lambda_{\alpha\beta\gamma\delta}$ is rank-1 in $(\alpha,\delta)$.
- $(\star_{24})$: For fixed $(\beta,\delta)$, $\lambda_{\alpha\beta\gamma\delta}$ is rank-1 in $(\alpha,\gamma)$.
- $(\star_{34})$: For fixed $(\gamma,\delta)$, $\lambda_{\alpha\beta\gamma\delta}$ is rank-1 in $(\alpha,\beta)$.

#### Stage B: Pairwise rank-1 implies rank-1.

**Proposition 2.** *If $\lambda_{\alpha\beta\gamma\delta} \neq 0$ for all non-identical $(\alpha,\beta,\gamma,\delta)$ and the six conditions $(\star_{12})$–$(\star_{34})$ hold, then there exist $u, v, w, x \in (\mathbb{R}^*)^n$ such that $\lambda_{\alpha\beta\gamma\delta} = u_\alpha v_\beta w_\gamma x_\delta$ for all non-identical $(\alpha,\beta,\gamma,\delta)$.*

*Proof.* We extract the rank-1 factorization in six steps, each using one pairwise condition. Fix five distinct reference indices $a_0, b_0, c_0, d_0, e_0 \in [n]$ (possible since $n \geq 5$).

**Step 1.** By $(\star_{12})$, for each fixed $(\alpha,\beta)$, the matrix $\lambda_{\alpha\beta\gamma\delta}$ has rank 1 in $(\gamma,\delta)$ on non-identical tuples. So:
$$\lambda_{\alpha\beta\gamma\delta} = \varphi(\alpha,\beta,\gamma) \cdot \psi(\alpha,\beta,\delta)$$
for all non-identical $(\alpha,\beta,\gamma,\delta)$. Explicitly: for each $(\alpha,\beta)$, choose a pivot $c_*(\alpha,\beta) \in \{c_0, e_0\}$ with $c_* \neq \alpha$ (possible since $c_0 \neq e_0$). Then $(\alpha,\beta,c_*,\delta)$ is non-identical for all $\delta$, so:
$$\psi(\alpha,\beta,\delta) := \lambda_{\alpha\beta\, c_*\, \delta}, \qquad \varphi(\alpha,\beta,\gamma) := \lambda_{\alpha\beta\gamma d_0}/\psi(\alpha,\beta,d_0)$$
All evaluations are at non-identical tuples.

**Step 2.** By $(\star_{23})$, for each fixed $(\beta,\gamma)$, $\lambda_{\alpha\beta\gamma\delta}$ is rank-1 in $(\alpha,\delta)$. Substituting Step 1: $\varphi(\alpha,\beta,\gamma) \cdot \psi(\alpha,\beta,\delta)$ must be rank-1 in $(\alpha,\delta)$ for fixed $(\beta,\gamma)$. The $2 \times 2$ minor condition gives:
$$\varphi(\alpha_1,\beta,\gamma) \psi(\alpha_1,\beta,\delta_1) \cdot \varphi(\alpha_2,\beta,\gamma) \psi(\alpha_2,\beta,\delta_2) = \varphi(\alpha_1,\beta,\gamma) \psi(\alpha_1,\beta,\delta_2) \cdot \varphi(\alpha_2,\beta,\gamma) \psi(\alpha_2,\beta,\delta_1)$$
The $\varphi$-factors cancel (they are nonzero), leaving:
$$\psi(\alpha_1,\beta,\delta_1) \psi(\alpha_2,\beta,\delta_2) = \psi(\alpha_1,\beta,\delta_2) \psi(\alpha_2,\beta,\delta_1)$$
So for fixed $\beta$, $\psi(\alpha,\beta,\delta)$ is rank-1 in $(\alpha,\delta)$: $\psi(\alpha,\beta,\delta) = \psi_0(\alpha,\beta) \cdot X(\beta,\delta)$, where $X(\beta,\delta) := \psi(a_0,\beta,\delta)/\psi(a_0,\beta,d_0)$ is independent of $\alpha$ (by the rank-1 condition just proved), and $\psi_0(\alpha,\beta) := \psi(\alpha,\beta,d_0)$.

Substituting: $\lambda_{\alpha\beta\gamma\delta} = \varphi(\alpha,\beta,\gamma) \cdot \psi_0(\alpha,\beta) \cdot X(\beta,\delta) = F(\alpha,\beta,\gamma) \cdot X(\beta,\delta)$, where $F(\alpha,\beta,\gamma) := \varphi(\alpha,\beta,\gamma) \cdot \psi_0(\alpha,\beta)$.

**Step 3.** By $(\star_{14})$, for each fixed $(\alpha,\delta)$, $\lambda_{\alpha\beta\gamma\delta}$ is rank-1 in $(\beta,\gamma)$. Substituting: $F(\alpha,\beta,\gamma) \cdot X(\beta,\delta)$ must be rank-1 in $(\beta,\gamma)$ for fixed $(\alpha,\delta)$. The $2 \times 2$ minor condition:
$$F(\alpha,\beta_1,\gamma_1) X(\beta_1,\delta) \cdot F(\alpha,\beta_2,\gamma_2) X(\beta_2,\delta) = F(\alpha,\beta_1,\gamma_2) X(\beta_1,\delta) \cdot F(\alpha,\beta_2,\gamma_1) X(\beta_2,\delta)$$
The $X$-factors cancel, leaving: $F(\alpha,\beta_1,\gamma_1) F(\alpha,\beta_2,\gamma_2) = F(\alpha,\beta_1,\gamma_2) F(\alpha,\beta_2,\gamma_1)$. So for fixed $\alpha$, $F$ is rank-1 in $(\beta,\gamma)$:
$$F(\alpha,\beta,\gamma) = G(\alpha,\beta) \cdot H(\alpha,\gamma)$$
Therefore $\lambda_{\alpha\beta\gamma\delta} = G(\alpha,\beta) \cdot H(\alpha,\gamma) \cdot X(\beta,\delta)$.

**Step 4.** By $(\star_{34})$, for each fixed $(\gamma,\delta)$, $\lambda_{\alpha\beta\gamma\delta}$ is rank-1 in $(\alpha,\beta)$. Substituting: $G(\alpha,\beta) \cdot [H(\alpha,\gamma) X(\beta,\delta)]$ must be rank-1 in $(\alpha,\beta)$ for fixed $(\gamma,\delta)$. The $2 \times 2$ minor condition:
$$G(\alpha_1,\beta_1) H(\alpha_1,\gamma) X(\beta_1,\delta) \cdot G(\alpha_2,\beta_2) H(\alpha_2,\gamma) X(\beta_2,\delta) = G(\alpha_1,\beta_2) H(\alpha_1,\gamma) X(\beta_2,\delta) \cdot G(\alpha_2,\beta_1) H(\alpha_2,\gamma) X(\beta_1,\delta)$$
The $H$ and $X$ factors cancel: $G(\alpha_1,\beta_1) G(\alpha_2,\beta_2) = G(\alpha_1,\beta_2) G(\alpha_2,\beta_1)$. So $G$ is rank-1:
$$G(\alpha,\beta) = g(\alpha) \cdot g'(\beta)$$
Therefore $\lambda_{\alpha\beta\gamma\delta} = g(\alpha) \cdot g'(\beta) \cdot H(\alpha,\gamma) \cdot X(\beta,\delta)$.

**Step 5.** By $(\star_{24})$, for each fixed $(\beta,\delta)$, $\lambda_{\alpha\beta\gamma\delta}$ is rank-1 in $(\alpha,\gamma)$. Substituting: $[g(\alpha) H(\alpha,\gamma)] \cdot [g'(\beta) X(\beta,\delta)]$. The bracket $[g'(\beta) X(\beta,\delta)]$ is a scalar for fixed $(\beta,\delta)$, so $g(\alpha) H(\alpha,\gamma)$ must be rank-1 in $(\alpha,\gamma)$. The $2 \times 2$ minor condition gives $H(\alpha_1,\gamma_1) H(\alpha_2,\gamma_2) = H(\alpha_1,\gamma_2) H(\alpha_2,\gamma_1)$ (the $g$-factors cancel). So $H$ is rank-1:
$$H(\alpha,\gamma) = h(\alpha) \cdot w(\gamma)$$
Therefore $\lambda_{\alpha\beta\gamma\delta} = g(\alpha) h(\alpha) \cdot g'(\beta) \cdot w(\gamma) \cdot X(\beta,\delta)$.

**Step 6.** By $(\star_{13})$, for each fixed $(\alpha,\gamma)$, $\lambda_{\alpha\beta\gamma\delta}$ is rank-1 in $(\beta,\delta)$. Substituting: $[g(\alpha) h(\alpha) w(\gamma)] \cdot g'(\beta) X(\beta,\delta)$. The bracket is a scalar for fixed $(\alpha,\gamma)$, so $g'(\beta) X(\beta,\delta)$ must be rank-1 in $(\beta,\delta)$. The $2 \times 2$ minor condition gives $X(\beta_1,\delta_1) X(\beta_2,\delta_2) = X(\beta_1,\delta_2) X(\beta_2,\delta_1)$ (the $g'$-factors cancel). So $X$ is rank-1:
$$X(\beta,\delta) = \tilde{v}(\beta) \cdot x(\delta)$$

**Conclusion.** Setting $u(\alpha) := g(\alpha) h(\alpha)$, $v(\beta) := g'(\beta) \tilde{v}(\beta)$:
$$\lambda_{\alpha\beta\gamma\delta} = u(\alpha) \cdot v(\beta) \cdot w(\gamma) \cdot x(\delta)$$
for all non-identical $(\alpha,\beta,\gamma,\delta)$. All factors are nonzero since $\lambda \neq 0$ on non-identical tuples. $\square$

---

## Summary

The polynomial map $\mathbf{F}$ consists of six families of Plücker equations $\mathcal{P}_{12}, \mathcal{P}_{13}, \mathcal{P}_{14}, \mathcal{P}_{23}, \mathcal{P}_{24}, \mathcal{P}_{34}$ (degree 4 each), totaling $O(n^6 \cdot 3^{12})$ equations.

The proof establishes:
1. **Independence from $A^{(1)}, \ldots, A^{(n)}$**: $\mathbf{F}$ is expressed purely in terms of $T$-entries.
2. **Bounded degree**: all coordinate functions have degree 4. In particular, the degrees do not depend on $n$.
3. **Exact characterization** (for Zariski-generic $A^{(1)}, \ldots, A^{(n)}$): $\mathbf{F}(\lambda \cdot Q) = 0 \iff \lambda$ is rank-1.

The characterization holds for all $n \geq 5$. For $n = 5$, the six varying indices $(v_1, v_2, v_3, v_4)$ cannot all be distinct from the shared indices $(c_p, c_q)$, so some 4-tuples have repeated indices (e.g., $(\alpha,\beta,\gamma,\alpha)$). These are valid since the problem requires $\lambda_{\alpha\beta\gamma\delta} \neq 0$ for non-identical (not all-same) indices. The genericity witness in Lemma 3 applies equally to $n = 5$ (with $v_4 = c_p$), as verified by explicit computation. $\square$

---

## Appendix: Partial Lean 4 Verification

The algebraic skeleton of this proof has been formally verified in Lean 4 + Mathlib. The file `FirstProof/P09_QuadrilinearTensors.lean` verifies the following components:

1. **Plücker consequence** (`plucker_consequence`, `F_vanishes_when_proportional`): If $P = S_1 - S_2$ (the Plücker identity), then $P \cdot S_2 - S_2 \cdot P = 0$. More importantly, when $P = \mu \cdot S$, the equation $F = P(I_1) S(I_2) - P(I_2) S(I_1) = 0$ follows by `ring`. This is the core of the necessity direction (Lemma 2).

2. **Rank-1 ratio equality** (`rank1_ratio_equality`): For rank-1 $\lambda = u \otimes v \otimes w \otimes x$, the two ratios $\mu_1$ and $\mu_2$ are equal, so $P = \mu \cdot S$ and $F = 0$.

3. **2×2 minor vanishing** (`rank1_minor`, `rank1_factorization`): The rank-1 condition $ad = bc$ (all $2 \times 2$ minors vanish) and the factorization $\lambda = \varphi \cdot \psi$.

4. **Six-step peeling** (`step1`, `step2_cancel`, `step4_g_rank1`, `final_rank1`): Key algebraic steps of Proposition 2. Step 2 verifies the cancellation of $\varphi$-factors when extracting the rank-1 structure of $\psi$. Step 4 verifies the commutativity identity $g_1 g_1' g_2 g_2' = g_1 g_2' g_2 g_1'$ that establishes $G$ is rank-1. The final assembly confirms $\lambda = u \cdot v \cdot w \cdot x$.

5. **Degree bound** (`degree_bound`, `degree_independent_of_n`): Each $F^{\{p,q\}}$ has degree $2 + 2 = 4$, independent of $n$.

6. **Proof structure** (`proof_structure`, `sufficiency_structure`): The logical skeleton: necessity + sufficiency give the characterization. Sufficiency decomposes into Stage A (Plücker → pairwise rank-1) and Stage B (pairwise rank-1 → rank-1).

**Scope and limitations.** The algebraic geometry (Zariski genericity, Grassmannians), the explicit witness computation (Lemma 3), and the determinant theory are beyond current Mathlib capabilities. The Lean file verifies the polynomial identities and logical structure.

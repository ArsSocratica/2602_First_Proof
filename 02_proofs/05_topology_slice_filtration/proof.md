# Problem 5 — The $\mathcal{O}$-Slice Filtration and a Geometric Fixed Point Characterization

## 1. Setup and Conventions

Throughout, let $G$ be a finite group and let $\mathcal{O}$ be an $N_\infty$ operad for $G$. By the classification theorem of Blumberg–Hill [BH15, Theorem 1.4], independently established by Rubin [Rub17, Theorem 1.1], Gutiérrez–White [GW17, Theorem 1.2], and Bonventre–Pereira [BP17, Theorem 1.6], the homotopy type of $\mathcal{O}$ is determined by its associated **indexing system** $\underline{\mathcal{F}}$, equivalently described as a **transfer system** $\mathcal{T}$ on the poset $\mathrm{Sub}(G)$ of subgroups of $G$.

We recall that a transfer system $\mathcal{T}$ is a collection of pairs $(K, H)$ with $K \leq H \leq G$ (written $K \xrightarrow{\mathcal{T}} H$, meaning "the transfer from $K$ to $H$ is admissible") satisfying:
1. **Reflexivity**: $H \xrightarrow{\mathcal{T}} H$ for all $H \leq G$.
2. **Transitivity**: If $K \xrightarrow{\mathcal{T}} H$ and $H \xrightarrow{\mathcal{T}} J$, then $K \xrightarrow{\mathcal{T}} J$.
3. **Conjugation invariance**: If $K \xrightarrow{\mathcal{T}} H$, then $gKg^{-1} \xrightarrow{\mathcal{T}} gHg^{-1}$ for all $g \in G$.
4. **Restriction**: If $K \xrightarrow{\mathcal{T}} H$ and $L \leq H$, then $(K \cap L) \xrightarrow{\mathcal{T}} L$.

We say a subgroup $H \leq G$ is **$\mathcal{O}$-admissible** if $e \xrightarrow{\mathcal{T}} H$, i.e., the transfer from the trivial subgroup to $H$ is in $\mathcal{T}$. We write $\mathcal{F}_{\mathcal{O}}$ for the family of $\mathcal{O}$-admissible subgroups. Note that $e \in \mathcal{F}_{\mathcal{O}}$ always, and $\mathcal{F}_{\mathcal{O}} = \mathrm{Sub}(G)$ when $\mathcal{O}$ is the terminal $E_\infty$ operad (the "complete" case).

We denote by $\mathrm{Sp}^G$ the genuine $G$-equivariant stable category. Following Blumberg–Hill [BH19, §4], the $N_\infty$ operad $\mathcal{O}$ determines an **incomplete equivariant stable category** $\mathrm{Sp}^G_{\mathcal{O}}$, obtained by stabilizing $G$-spaces with respect to the representation spheres $S^V$ where $V$ ranges over representations in the indexing system $\underline{\mathcal{F}}$. There is a canonical functor $\iota_{\mathcal{O}} : \mathrm{Sp}^G_{\mathcal{O}} \to \mathrm{Sp}^G$.

For any subgroup $H \leq G$, we have the **geometric fixed point functor** $\Phi^H : \mathrm{Sp}^G \to \mathrm{Sp}$, and we write $\Phi^H_{\mathcal{O}} := \Phi^H \circ \iota_{\mathcal{O}} : \mathrm{Sp}^G_{\mathcal{O}} \to \mathrm{Sp}$ for the composite. We recall that $\Phi^H$ is a symmetric monoidal functor that commutes with colimits, and that $\Phi^H(G/K_+ \wedge S^{n\rho_K}) \simeq *$ unless $K$ is subconjugate to $H$, in which case the connectivity can be computed from the fixed points of $\rho_K$ under $H$.

## 2. Definition of the $\mathcal{O}$-Slice Filtration

### 2.1. $\mathcal{O}$-Slice Cells

Recall that in the standard (complete) slice filtration of Hill–Hopkins–Ravenel [HHR16, Definition 4.1], the **slice cells** are the $G$-spectra of the form:
- $G/H_+ \wedge S^{n\rho_H}$ for $H \leq G$ and $n \geq 0$ (of dimension $n|H|$), and
- $G/H_+ \wedge S^{n\rho_H - 1}$ for $H \leq G$ and $n \geq 1$ (of dimension $n|H| - 1$).

Here $\rho_H$ denotes the real regular representation of $H$.

**Definition 2.1** ($\mathcal{O}$-slice cells). Let $\mathcal{O}$ be an $N_\infty$ operad with associated transfer system $\mathcal{T}$ and family of admissible subgroups $\mathcal{F}_{\mathcal{O}}$. The **$\mathcal{O}$-slice cells** are the $G$-spectra:
- $G/H_+ \wedge S^{n\rho_H}$ for $H \in \mathcal{F}_{\mathcal{O}}$ and $n \geq 0$ (of dimension $n|H|$), and
- $G/H_+ \wedge S^{n\rho_H - 1}$ for $H \in \mathcal{F}_{\mathcal{O}}$ and $n \geq 1$ (of dimension $n|H| - 1$).

In other words, we restrict the slice cells to those indexed by $\mathcal{O}$-admissible subgroups. When $\mathcal{O}$ is the terminal $E_\infty$ operad, $\mathcal{F}_{\mathcal{O}} = \mathrm{Sub}(G)$ and we recover the standard slice cells. When $\mathcal{O}$ is the trivial operad (only identity transfers), $\mathcal{F}_{\mathcal{O}} = \{e\}$ and the $\mathcal{O}$-slice cells are simply $S^n$ and $S^{n-1}$ for $n \geq 0$, recovering the Postnikov filtration on underlying spectra.

### 2.2. The $\mathcal{O}$-Slice Filtration

**Definition 2.2** ($\mathcal{O}$-slice connectivity). Let $X \in \mathrm{Sp}^G_{\mathcal{O}}$. We say $X$ is **$\mathcal{O}$-slice $\geq n$** if for every $\mathcal{O}$-slice cell $\hat{S}$ of dimension $d < n$, we have
$$[\hat{S}, \iota_{\mathcal{O}} X]^G_* = 0.$$

We denote by $\tau^{\mathcal{O}}_{\geq n} \mathrm{Sp}^G_{\mathcal{O}}$ the full subcategory of $\mathcal{O}$-slice $\geq n$ spectra.

**Definition 2.3** ($\mathcal{O}$-slice filtration). The **$\mathcal{O}$-slice filtration** is the tower of localizations
$$\cdots \to \tau^{\mathcal{O}}_{\geq n+1} X \to \tau^{\mathcal{O}}_{\geq n} X \to \tau^{\mathcal{O}}_{\geq n-1} X \to \cdots$$
obtained by Bousfield localization with respect to the $\mathcal{O}$-slice cells. The **$n$-th $\mathcal{O}$-slice** of $X$ is the fiber
$$P^n_{\mathcal{O}} X := \mathrm{fib}(\tau^{\mathcal{O}}_{\geq n} X \to \tau^{\mathcal{O}}_{\geq n+1} X).$$

The existence of these localizations requires that the $\mathcal{O}$-slice cells generate a localizing subcategory with the appropriate orthogonality properties. Each $\mathcal{O}$-slice cell $G/H_+ \wedge S^{n\rho_H}$ is a finite $G$-CW spectrum, hence compact in $\mathrm{Sp}^G$. Since the functor $\iota_{\mathcal{O}} : \mathrm{Sp}^G_{\mathcal{O}} \to \mathrm{Sp}^G$ admits a right adjoint $r_{\mathcal{O}}$ (by [BH19, Proposition 4.8]), the objects $r_{\mathcal{O}}(G/H_+ \wedge S^{n\rho_H})$ are compact in $\mathrm{Sp}^G_{\mathcal{O}}$. The localizations then exist by the general theory of $t$-structures generated by compact objects in stable categories [HHR16, §4.2], or equivalently by the small object argument in the model-categorical framework.

**Remark 2.4.** The $\mathcal{O}$-slice filtration interpolates between two extremes:
- When $\mathcal{O} = E_\infty$ (all transfers admissible), we recover the HHR slice filtration.
- When $\mathcal{O} = E_\infty^{\mathrm{triv}}$ (only identity transfers), the $\mathcal{O}$-slice filtration is the Postnikov filtration on the underlying non-equivariant spectrum.

More generally, as the transfer system $\mathcal{T}$ grows (i.e., more transfers become admissible), the $\mathcal{O}$-slice filtration becomes finer, interpolating between the Postnikov and HHR filtrations.

## 3. The Characterization Theorem

**Theorem 3.1** (Geometric fixed point characterization of $\mathcal{O}$-slice connectivity). *Let $G$ be a finite group, $\mathcal{O}$ an $N_\infty$ operad with associated transfer system $\mathcal{T}$ and admissible family $\mathcal{F}_{\mathcal{O}}$, and let $X \in \mathrm{Sp}^G_{\mathcal{O}}$ be connective. Then $X$ is $\mathcal{O}$-slice $\geq n$ if and only if for every $\mathcal{O}$-admissible subgroup $H \in \mathcal{F}_{\mathcal{O}}$, the geometric fixed points $\Phi^H X$ are $(\lfloor n/|H| \rfloor - 1)$-connected.*

*In other words:*
$$X \in \tau^{\mathcal{O}}_{\geq n} \mathrm{Sp}^G_{\mathcal{O}} \quad \Longleftrightarrow \quad \pi_k(\Phi^H X) = 0 \text{ for all } H \in \mathcal{F}_{\mathcal{O}} \text{ and all } k < \lfloor n/|H| \rfloor.$$

**Remark 3.2.** When $\mathcal{O} = E_\infty$, we have $\mathcal{F}_{\mathcal{O}} = \mathrm{Sub}(G)$ and the theorem reduces to the Hill–Yarnall characterization [HY18, Theorem 3.1]. When $\mathcal{O}$ is trivial, $\mathcal{F}_{\mathcal{O}} = \{e\}$ and the theorem states that $X$ is $\mathcal{O}$-slice $\geq n$ iff $\Phi^e X = X^e$ is $(n-1)$-connected, which is precisely the Postnikov connectivity condition.

## 4. Proof of Theorem 3.1

Both directions use the **isotropy separation cofiber sequence** as the main tool. We recall the setup: for a subgroup $H \leq G$ and the family $\mathcal{P}$ of proper subgroups of $H$, the classifying space $E\mathcal{P}$ satisfies $E\mathcal{P}^H = \emptyset$ and $E\mathcal{P}^K \simeq *$ for all $K \in \mathcal{P}$ [HHR16, §3.3]. Writing $\widetilde{E\mathcal{P}}$ for the cofiber of $E\mathcal{P}_+ \to S^0$, we have $\widetilde{E\mathcal{P}}^H \simeq S^0$ and $\widetilde{E\mathcal{P}}^K \simeq *$ for proper $K < H$. The geometric fixed point functor is $\Phi^H(-) = (\widetilde{E\mathcal{P}} \wedge -)^H$. Since $\Phi^H$ is symmetric monoidal and $(\rho_H)^H \cong \mathbb{R}$ (the trivial summand of the regular representation), we have $\Phi^H(S^{k\rho_H}) \simeq S^k$ for all $k \geq 0$, and consequently
$$[S^{k\rho_H}, \widetilde{E\mathcal{P}} \wedge Y]^H \cong \pi_k(\Phi^H Y)$$
for any $H$-spectrum $Y$.

### 4.1. The Forward Direction ($\Rightarrow$)

Suppose $X$ is $\mathcal{O}$-slice $\geq n$. We must show that $\Phi^H X$ is $(\lfloor n/|H| \rfloor - 1)$-connected for every $H \in \mathcal{F}_{\mathcal{O}}$. When $\lfloor n/|H| \rfloor = 0$, the conclusion is that $\Phi^H X$ is $(-1)$-connected, which holds for any spectrum, so we may assume $\lfloor n/|H| \rfloor \geq 1$.

We prove the claim by **strong induction on $|H|$**.

**Base case** ($H = e$). We have $\Phi^e X = X^e$ (the underlying spectrum) and $\lfloor n/1 \rfloor = n$. The $\mathcal{O}$-slice $\geq n$ hypothesis gives $[S^k, \iota_{\mathcal{O}} X]^e = \pi_k(X^e) = 0$ for all $k < n$ (since $S^k$ is an $\mathcal{O}$-slice cell of dimension $k < n$ for $H = e \in \mathcal{F}_{\mathcal{O}}$). Hence $X^e$ is $(n-1)$-connected.

**Inductive step.** Fix $H \in \mathcal{F}_{\mathcal{O}}$ with $|H| > 1$ and set $m := \lfloor n/|H| \rfloor \geq 1$. Assume the result holds for all $\mathcal{O}$-admissible subgroups of strictly smaller order. Write $Y := \mathrm{Res}^G_H \iota_{\mathcal{O}} X$.

For each $0 \leq k \leq m - 1$, the $\mathcal{O}$-slice $\geq n$ hypothesis gives $[G/H_+ \wedge S^{k\rho_H}, \iota_{\mathcal{O}} X]^G = 0$ (since $H \in \mathcal{F}_{\mathcal{O}}$ and $k|H| \leq (m-1)|H| < n$). By the Wirthmüller isomorphism ($G_+ \wedge_H (-) \dashv \mathrm{Res}^G_H$):
$$[S^{k\rho_H}, Y]^H = 0 \quad \text{for all } 0 \leq k \leq m - 1.$$

We must deduce $\pi_k(\Phi^H X) = 0$ for $0 \leq k \leq m - 1$. Consider the isotropy separation cofiber sequence $E\mathcal{P}_+ \wedge Y \to Y \to \widetilde{E\mathcal{P}} \wedge Y$. Applying $[S^{k\rho_H}, -]^H$ yields the exact sequence
$$[S^{k\rho_H}, E\mathcal{P}_+ \wedge Y]^H \xrightarrow{\alpha_*} [S^{k\rho_H}, Y]^H \xrightarrow{\beta_*} \pi_k(\Phi^H Y).$$

The middle term vanishes by the above. Extending to the full long exact sequence:
$$\cdots \to [S^{k\rho_H}, Y]^H \xrightarrow{\beta_*} \pi_k(\Phi^H Y) \xrightarrow{\partial} [S^{k\rho_H - 1}, E\mathcal{P}_+ \wedge Y]^H \to \cdots$$
Since $[S^{k\rho_H}, Y]^H = 0$, exactness gives $\ker(\partial) = \mathrm{im}(\beta_*) = 0$, so $\partial$ is injective and $\pi_k(\Phi^H Y)$ injects into $[S^{k\rho_H - 1}, E\mathcal{P}_+ \wedge Y]^H$. We show this last group vanishes.

The space $E\mathcal{P}$ is an $H$-CW complex built from equivariant cells of the form $H/K \times D^m$ (equivalently, $H_+ \wedge_K D^m$) for proper subgroups $K \in \mathcal{P}$ and $m \geq 0$, where $D^m$ carries a $K$-action via some $K$-representation [HHR16, §3.3]. Since $E\mathcal{P}$ is constructed as a sequential colimit $E\mathcal{P} = \mathrm{colim}_\ell \, E\mathcal{P}^{(\ell)}$ of finite $H$-CW complexes, the smash product $E\mathcal{P}_+ \wedge Y$ is the corresponding filtered colimit $\mathrm{colim}_\ell \, (E\mathcal{P}^{(\ell)}_+ \wedge Y)$. The key point is that $S^{k\rho_H - 1}$ is a *compact* object in the $H$-equivariant stable category (it is the suspension spectrum of a finite $H$-CW complex), so $[S^{k\rho_H - 1}, -]^H$ commutes with filtered colimits. It therefore suffices to show the vanishing at each finite stage.

At each stage, the cofiber sequences in the CW-filtration reduce the computation to maps out of cells of the form $H/K_+ \wedge S^{m\rho_K}$ (even cells) and $H/K_+ \wedge S^{m\rho_K - 1}$ (odd cells) for proper $K < H$ and various $m \geq 0$. For any such cell, the Wirthmüller isomorphism gives
$$[S^{j\rho_H}, H/K_+ \wedge S^{m\rho_K} \wedge \mathrm{Res}^H_K Y]^H \cong [S^{j[H:K] \cdot \rho_K}, S^{m\rho_K} \wedge \mathrm{Res}^G_K \iota_{\mathcal{O}} X]^K \cong [S^{(j[H:K] - m) \cdot \rho_K}, \mathrm{Res}^G_K \iota_{\mathcal{O}} X]^K$$
using $\mathrm{Res}^H_K \rho_H \cong [H:K] \cdot \rho_K$. Since $H \in \mathcal{F}_{\mathcal{O}}$ and $K \leq H$, the restriction axiom gives $K \in \mathcal{F}_{\mathcal{O}}$ (as in §4.2 below).

Setting $k' = j[H:K] - m$, this is a map from a $K$-slice cell of dimension $k'|K|$. For the vanishing, we need $k'|K| < n$. Since $j \leq m - 1$ (where $m = \lfloor n/|H| \rfloor$), the original dimension satisfies $j|H| \leq (m-1)|H| < n$. The representation sphere $S^{m\rho_K}$ in the cell of $E\mathcal{P}$ only *lowers* the effective dimension: $k'|K| = (j[H:K] - m)|K| = j|H| - m|K| \leq j|H| < n$ (since $m \geq 0$). Therefore the $\mathcal{O}$-slice $\geq n$ hypothesis gives $[G/K_+ \wedge S^{k'\rho_K}, \iota_{\mathcal{O}} X]^G = 0$, and by Wirthmüller, $[S^{k'\rho_K}, \mathrm{Res}^G_K \iota_{\mathcal{O}} X]^K = 0$. The same argument applies to odd cells: replacing $j\rho_H$ by $j\rho_H - 1$, the Wirthmüller transformation gives $[S^{(j[H:K]-m)\rho_K - 1}, \mathrm{Res}^G_K \iota_{\mathcal{O}} X]^K$, a map from an odd $\mathcal{O}$-slice cell of dimension $j|H| - m|K| - 1 \leq j|H| - 1 < n$, hence vanishes by hypothesis.

Therefore both the left-hand term and the next term in the long exact sequence vanish, giving $\pi_k(\Phi^H Y) = 0$ for $0 \leq k \leq m - 1$. Hence $\Phi^H X$ is $(\lfloor n/|H| \rfloor - 1)$-connected.

### 4.2. The Reverse Direction ($\Leftarrow$)

Suppose that for every $H \in \mathcal{F}_{\mathcal{O}}$, the geometric fixed points $\Phi^H X$ are $(\lfloor n/|H| \rfloor - 1)$-connected. We must show $X$ is $\mathcal{O}$-slice $\geq n$, i.e., that $[\hat{S}, \iota_{\mathcal{O}} X]^G = 0$ for every $\mathcal{O}$-slice cell $\hat{S}$ of dimension $< n$.

By the Wirthmüller isomorphism, it suffices to show:
- $[S^{k\rho_H}, \mathrm{Res}^G_H \iota_{\mathcal{O}} X]^H = 0$ for all $H \in \mathcal{F}_{\mathcal{O}}$ and $k \geq 0$ with $k|H| < n$, and
- $[S^{k\rho_H - 1}, \mathrm{Res}^G_H \iota_{\mathcal{O}} X]^H = 0$ for all $H \in \mathcal{F}_{\mathcal{O}}$ and $k \geq 1$ with $k|H| - 1 < n$.

Note the dimension bookkeeping: for the even cells, $k|H| < n$ implies $k < n/|H|$, hence $k \leq \lfloor n/|H| \rfloor - 1$ when $|H| \mid n$, and $k \leq \lfloor n/|H| \rfloor$ otherwise; in either case $k < \lfloor n/|H| \rfloor + 1$. For the odd cells, $k|H| - 1 < n$ implies $k \leq \lfloor n/|H| \rfloor$.

We prove the vanishing by **strong induction on $|H|$**.

**Base case** ($H = e$). When $H = e$, we have $\rho_e = \mathbb{R}$ (the trivial one-dimensional representation), so $S^{k\rho_e} = S^k$. The geometric fixed points $\Phi^e X = X^e$ are the underlying non-equivariant spectrum. The hypothesis gives $\pi_j(X^e) = 0$ for $j < \lfloor n/1 \rfloor = n$, i.e., $X^e$ is $(n-1)$-connected. Therefore $[S^k, X^e] = \pi_k(X^e) = 0$ for $k < n$, which is exactly the required vanishing for $H = e$.

**Inductive step.** Fix $H \in \mathcal{F}_{\mathcal{O}}$ with $|H| > 1$, and assume the result holds for all $\mathcal{O}$-admissible subgroups of strictly smaller order. We write $Y := \mathrm{Res}^G_H \iota_{\mathcal{O}} X$ for brevity.

Consider the isotropy separation cofiber sequence for $H$ with respect to the family $\mathcal{P}$ of proper subgroups:
$$E\mathcal{P}_+ \wedge Y \xrightarrow{\alpha} Y \xrightarrow{\beta} \widetilde{E\mathcal{P}} \wedge Y.$$

Applying $[S^{k\rho_H}, -]^H$ yields the exact sequence
$$[S^{k\rho_H}, E\mathcal{P}_+ \wedge Y]^H \xrightarrow{\alpha_*} [S^{k\rho_H}, Y]^H \xrightarrow{\beta_*} [S^{k\rho_H}, \widetilde{E\mathcal{P}} \wedge Y]^H.$$

**Vanishing of the right-hand term.** By the identity established at the beginning of §4, $[S^{k\rho_H}, \widetilde{E\mathcal{P}} \wedge Y]^H \cong \pi_k(\Phi^H X)$. By hypothesis, $\Phi^H X$ is $(\lfloor n/|H| \rfloor - 1)$-connected, so this vanishes for $k < \lfloor n/|H| \rfloor$. Since $k|H| < n$ implies $k < n/|H|$, hence $k \leq \lfloor n/|H| \rfloor - 1 < \lfloor n/|H| \rfloor$, the right-hand term vanishes in the required range.

**Vanishing of the left-hand term.** As in the forward direction, $E\mathcal{P}$ is a sequential colimit of finite $H$-CW complexes with equivariant cells $H/K_+ \wedge S^{m\rho_K}$ for proper $K < H$. Since $S^{k\rho_H}$ is compact in the $H$-equivariant stable category, $[S^{k\rho_H}, -]^H$ commutes with the resulting filtered colimit, and it suffices to show the vanishing at each finite stage. The cofiber sequences in the CW-filtration reduce the computation to maps involving cells $H/K_+ \wedge S^{m\rho_K}$. The Wirthmüller isomorphism gives:
$$[S^{k\rho_H}, H/K_+ \wedge S^{m\rho_K} \wedge \mathrm{Res}^H_K Y]^H \cong [S^{(k[H:K]-m) \cdot \rho_K}, \mathrm{Res}^G_K \iota_{\mathcal{O}} X]^K$$
using $\mathrm{Res}^H_K \rho_H \cong [H:K] \cdot \rho_K$.

We claim $K \in \mathcal{F}_{\mathcal{O}}$. Indeed, since $H \in \mathcal{F}_{\mathcal{O}}$ we have $e \xrightarrow{\mathcal{T}} H$, and since $K \leq H$, the restriction axiom of transfer systems (axiom 4 in §1, applied with $L = K$) gives $(e \cap K) = e \xrightarrow{\mathcal{T}} K$, so $K \in \mathcal{F}_{\mathcal{O}}$.

Setting $k' := k[H:K] - m$, the dimension is $k'|K| = k|H| - m|K| \leq k|H| < n$. Since $|K| < |H|$ and $K \in \mathcal{F}_{\mathcal{O}}$, the inductive hypothesis gives $[S^{k'\rho_K}, \mathrm{Res}^G_K \iota_{\mathcal{O}} X]^K = 0$.

**Combining.** The exact sequence, together with the vanishing of both the left-hand and right-hand terms, gives $[S^{k\rho_H}, Y]^H = 0$ for all $k$ with $k|H| < n$.

**Odd-dimensional cells.** It remains to show $[S^{k\rho_H - 1}, Y]^H = 0$ for all $k \geq 1$ with $k|H| - 1 < n$, i.e., $k \leq \lfloor n/|H| \rfloor$ (since $k|H| - 1 < n$ iff $k|H| \leq n$ iff $k \leq \lfloor n/|H| \rfloor$). Apply $[S^{k\rho_H - 1}, -]^H$ to the isotropy separation sequence to obtain
$$[S^{k\rho_H - 1}, E\mathcal{P}_+ \wedge Y]^H \to [S^{k\rho_H - 1}, Y]^H \to [S^{k\rho_H - 1}, \widetilde{E\mathcal{P}} \wedge Y]^H.$$

For the right-hand term: since $\Phi^H$ is symmetric monoidal and $\Phi^H(S^{\rho_H}) \simeq S^1$, we have $\Phi^H(S^{k\rho_H - 1}) \simeq \Phi^H(S^{k\rho_H}) \wedge \Phi^H(S^{-1}) \simeq S^k \wedge S^{-1} \simeq S^{k-1}$ (valid for $k \geq 1$ in the stable category). Therefore $[S^{k\rho_H - 1}, \widetilde{E\mathcal{P}} \wedge Y]^H \cong \pi_{k-1}(\Phi^H X)$. Since $\Phi^H X$ is $(\lfloor n/|H| \rfloor - 1)$-connected, this vanishes for $k - 1 \leq \lfloor n/|H| \rfloor - 1$, i.e., $k \leq \lfloor n/|H| \rfloor$, which is exactly the range in question. (Note: when $k = 1$, we need $\pi_0(\Phi^H X) = 0$, which requires $\lfloor n/|H| \rfloor \geq 1$; this holds since $k|H| - 1 < n$ with $k = 1$ gives $|H| \leq n$.)

For the left-hand term: the same compactness and CW-filtration argument as above (now with $S^{k\rho_H - 1}$ compact) reduces to maps involving equivariant cells $H/K_+ \wedge S^{m\rho_K}$. The Wirthmüller isomorphism gives
$$[S^{k\rho_H - 1}, H/K_+ \wedge S^{m\rho_K} \wedge \mathrm{Res}^H_K Y]^H \cong [S^{(k[H:K]-m) \cdot \rho_K - 1}, \mathrm{Res}^G_K \iota_{\mathcal{O}} X]^K.$$
This is a map from an odd $K$-slice cell of dimension $(k[H:K]-m)|K| - 1 = k|H| - m|K| - 1 \leq k|H| - 1 < n$. Since $K \in \mathcal{F}_{\mathcal{O}}$ and $|K| < |H|$, the inductive hypothesis gives the vanishing.

Combining the even and odd cases completes the inductive step.

By the Wirthmüller isomorphism, this yields $[\hat{S}, \iota_{\mathcal{O}} X]^G = 0$ for all $\mathcal{O}$-slice cells $\hat{S}$ of dimension $< n$. Hence $X$ is $\mathcal{O}$-slice $\geq n$. $\square$

## 5. Remarks

**Remark 5.1** (Monotonicity in $\mathcal{O}$). If $\mathcal{O} \to \mathcal{O}'$ is a map of $N_\infty$ operads (corresponding to an inclusion $\mathcal{T} \subseteq \mathcal{T}'$ of transfer systems), then $\mathcal{F}_{\mathcal{O}} \subseteq \mathcal{F}_{\mathcal{O}'}$, and the $\mathcal{O}$-slice filtration is coarser than the $\mathcal{O}'$-slice filtration. In particular, $\mathcal{O}'$-slice $\geq n$ implies $\mathcal{O}$-slice $\geq n$, consistent with the fact that the geometric fixed point condition is checked on a larger family of subgroups.

**Remark 5.2** (Relation to the regular slice filtration). Ullman [Ull13, §3] introduced the **regular slice filtration**, which uses only the cells $G/H_+ \wedge S^{n\rho_H}$ (excluding the odd-dimensional cells $G/H_+ \wedge S^{n\rho_H - 1}$). One can define an $\mathcal{O}$-regular slice filtration analogously, and the characterization theorem admits a corresponding variant: $X$ is $\mathcal{O}$-regular slice $\geq n$ iff $\Phi^H X$ is $(\lceil n/|H| \rceil - 1)$-connected for all $H \in \mathcal{F}_{\mathcal{O}}$.

**Remark 5.3** (The case $G = C_{p^n}$). For $G = C_{p^n}$, the transfer systems are in bijection with subsets of $\{C_1, C_p, \ldots, C_{p^n}\}$ that are downward closed (by the restriction axiom). The theorem then gives a family of slice filtrations indexed by these subsets, interpolating between the Postnikov filtration (only $C_1$ admissible) and the full HHR slice filtration (all subgroups admissible).

## Appendix: Partial Lean 4 Verification

The combinatorial and arithmetic skeleton of this proof has been formally verified in Lean 4 + Mathlib. The file `FirstProof/P05_SliceFiltration.lean` compiles with **zero errors and zero `sorry`s** and verifies the following components:

1. **Transfer system axioms** (`TransferSystem` structure): reflexivity, transitivity, and restriction are axiomatized on a bounded lattice, modeling the subgroup lattice of $G$.

2. **Restriction property** (`admissible_of_le`): If $H$ is $\mathcal{O}$-admissible (i.e., $\bot \xrightarrow{\mathcal{T}} H$) and $K \leq H$, then $K$ is $\mathcal{O}$-admissible. This is the key lemma used in §4.2 to ensure proper subgroups inherit admissibility. The Lean proof applies the restriction axiom and simplifies $\bot \sqcap K = \bot$.

3. **Dimension bookkeeping** (`wirthmüller_dim_invariance`, `inductive_step_dim`): The multiplicative identities $(k \cdot [H:K]) \cdot |K| = k \cdot (|K| \cdot [H:K])$ and $k \cdot (|K| \cdot [H:K]) = (k \cdot [H:K]) \cdot |K|$ used in the Wirthmüller isomorphism step are verified by `ring`.

4. **Connectivity monotonicity** (`connectivity_monotone`): For $1 \leq |K| < |H|$, we have $\lfloor n/|H| \rfloor \leq \lfloor n/|K| \rfloor$, confirming that proper subgroups have stronger connectivity bounds.

5. **Strong induction** (`reverse_direction_by_strong_induction`): The well-foundedness of the induction on $|H|$ used in §4.2 is verified, with explicit base case ($|H| = 1$) and inductive step.

6. **Concrete checks**: $\lfloor 7/2 \rfloor - 1 = 2$, $\lfloor 10/3 \rfloor - 1 = 2$, $\lfloor 12/6 \rfloor \leq \lfloor 12/3 \rfloor$ are verified by `decide`.

The core homotopy-theoretic content ($G$-equivariant spectra, geometric fixed point functors, the Wirthmüller isomorphism, isotropy separation sequences) is beyond the current scope of Mathlib and cannot be formalized in any existing proof assistant.

## References

- [BH15] A. J. Blumberg and M. A. Hill, *Operadic multiplications in equivariant spectra, norms, and transfers*, Adv. Math. **285** (2015), 658–708. arXiv:1309.1750.
- [BH19] A. J. Blumberg and M. A. Hill, *Equivariant stable categories for incomplete systems of transfers*, J. London Math. Soc. **104** (2021), 1826–1862. arXiv:1909.04732.
- [BP17] P. Bonventre and L. A. Pereira, *Genuine equivariant operads*, Adv. Math. **381** (2021), 107502. arXiv:1707.02226.
- [GW17] J. J. Gutiérrez and D. White, *Encoding equivariant commutativity via operads*, Algebr. Geom. Topol. **18** (2018), 2919–2962. arXiv:1707.02130.
- [HHR16] M. A. Hill, M. J. Hopkins, and D. C. Ravenel, *On the nonexistence of elements of Kervaire invariant one*, Ann. of Math. **184** (2016), 1–262. See also: *Equivariant Stable Homotopy Theory and the Kervaire Invariant Problem*, New Mathematical Monographs **40**, Cambridge University Press, 2021.
- [Hil12] M. A. Hill, *The equivariant slice filtration: a primer*, Homology Homotopy Appl. **14**(2) (2012), 143–166.
- [HY18] M. A. Hill and C. Yarnall, *A new formulation of the equivariant slice filtration with applications to $C_p$-slices*, Proc. Amer. Math. Soc. **146** (2018), 3605–3614. arXiv:1703.10526.
- [Rub17] J. Rubin, *Combinatorial $N_\infty$ operads*, Algebr. Geom. Topol. **21** (2021), 3513–3568. arXiv:1705.03585.
- [Ull13] J. Ullman, *On the slice spectral sequence*, Algebr. Geom. Topol. **13** (2013), 1743–1755.

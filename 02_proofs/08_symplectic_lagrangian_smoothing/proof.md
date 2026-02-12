# Problem 8 — Proof Draft (Revised, Session 4)

## Theorem

Let $K \subset \mathbb{R}^4$ be a polyhedral Lagrangian surface — that is, a finite 2-dimensional polyhedral complex embedded in $\mathbb{R}^4$ as a topological 2-manifold (possibly with boundary), whose faces are convex polygons each contained in a Lagrangian plane — with the property that exactly 4 faces meet at every vertex. Then $K$ has a Lagrangian smoothing: there exists a family $\{K_t\}_{t \in (0,1]}$ of smooth Lagrangian submanifolds forming a Hamiltonian isotopy, extending to a topological isotopy on $[0,1]$ with $K_0 = K$.

**Answer: YES.**

---

## Notation and Setup

Let $(\mathbb{R}^4, \omega)$ denote $\mathbb{R}^4$ with the standard symplectic form $\omega = \sum_{j=1}^2 dq_j \wedge dp_j$ (equivalently, $\omega = dx_1 \wedge dy_1 + dx_2 \wedge dy_2$ in coordinates $(x_j, y_j) = (q_j, p_j)$). We use the Liouville form $\lambda = -\sum_{j=1}^2 p_j\, dq_j$, so that $d\lambda = -\sum dp_j \wedge dq_j = \sum dq_j \wedge dp_j = \omega$. (Equivalently, $\lambda = \frac{1}{2}\sum_{j=1}^2 (q_j\, dp_j - p_j\, dq_j)$ differs from $-\sum p_j dq_j$ by an exact form.)

Let $K$ be a polyhedral Lagrangian surface with vertex set $V = \{v_1, \ldots, v_N\}$, edge set $E$, and face set $F$. Each face $f \in F$ is a convex polygon contained in a Lagrangian plane $\Pi_f \subset \mathbb{R}^4$. The valence-4 hypothesis means that for each $v \in V$, exactly 4 faces are incident to $v$.

Let $\delta = \frac{1}{3}\min\{|v_i - v_j| : v_i \neq v_j \in V\}$ be one-third the minimum inter-vertex distance.

---

## Step 1: Local Structure at a Valence-4 Vertex

**Lemma 1** (Vertex normal form). *Let $v \in V$ be a vertex of $K$ with incident faces $F_1, F_2, F_3, F_4$ in cyclic order. Then:*

*(a) There exist 4 edge directions $e_1, e_2, e_3, e_4 \in T_v\mathbb{R}^4$, spanning $\mathbb{R}^4$, where $e_k$ is the direction of the edge between $F_k$ and $F_{k+1}$ (mod 4). The face planes are $\Pi_k = \mathrm{span}(e_{k-1}, e_k)$, and the Lagrangian condition gives $\omega(e_k, e_{k+1}) = 0$ for all $k$ (mod 4).*

*(b) The 4 planes may all be distinct.*

*(c) (Canonical normal form.) After translation and a linear symplectomorphism, we may place $v$ at the origin and assume, in Darboux coordinates $(q_1, q_2, p_1, p_2)$ with $\omega = dq_1 \wedge dp_1 + dq_2 \wedge dp_2$:*
$$e_1 = \partial_{q_1},\quad e_2 = \partial_{q_2},\quad e_3 = a_1\,\partial_{q_1} + a_2\,\partial_{q_2} + \partial_{p_1},\quad e_4 = a_2\,\partial_{q_1} + b_2\,\partial_{q_2} + \partial_{p_2}$$
*where $a_1, a_2, b_2 \in \mathbb{R}$ are the moduli of the vertex configuration. In particular, $\Pi_2 = \{p = 0\}$.*

*Proof.*

**(a)** Since $K$ is a topological 2-manifold, $\text{Lk}(v, K) \cong S^1$ with 4 arcs. Consecutive faces $F_k, F_{k+1}$ share an edge in direction $e_k \in \Pi_k \cap \Pi_{k+1}$. Since $\Pi_k$ is 2-dimensional and contains $e_{k-1}$ and $e_k$, we get $\Pi_k = \text{span}(e_{k-1}, e_k)$. The Lagrangian condition $\omega|_{\Pi_k} = 0$ gives $\omega(e_{k-1}, e_k) = 0$.

**Spanning:** The 4 vectors $e_1, e_2, e_3, e_4$ span $\mathbb{R}^4$. If not, they lie in a subspace $W$ of dimension $\leq 3$. Each $\Pi_k = \text{span}(e_{k-1}, e_k) \subset W$. But a Lagrangian plane has dimension 2, and $\omega|_{\Pi_k} = 0$, so $\Pi_k$ is an isotropic subspace. In a 3-dimensional subspace $W \subset \mathbb{R}^4$, the restriction $\omega|_W$ has rank 2 (since $\omega$ is nondegenerate on $\mathbb{R}^4$ and $\dim W = 3$), so $W$ contains a unique isotropic line $\ell = \ker(\omega|_W)$ and every 2-dimensional isotropic subspace of $W$ must contain $\ell$. This would force $\ell \subset \Pi_k$ for all $k$, hence $\ell \subset \Pi_k \cap \Pi_{k+1} = \mathbb{R} e_k$ for all $k$, giving $e_1 \parallel e_2 \parallel e_3 \parallel e_4$ — contradicting the fact that consecutive faces are distinct (the link has 4 distinct arcs).

**(b)** Example: $e_1 = \partial_{q_1}$, $e_2 = \partial_{q_2}$, $e_3 = \partial_{p_1}$, $e_4 = \partial_{p_2}$ (i.e., $a_1 = a_2 = b_2 = 0$ in the normal form). One checks $\omega(e_k, e_{k+1}) = 0$ for all $k$ (mod 4). The planes $\Pi_1 = \text{span}(\partial_{p_2}, \partial_{q_1})$, $\Pi_2 = \text{span}(\partial_{q_1}, \partial_{q_2})$, $\Pi_3 = \text{span}(\partial_{q_2}, \partial_{p_1})$, $\Pi_4 = \text{span}(\partial_{p_1}, \partial_{p_2})$ are all distinct Lagrangian planes.

**(c)** We construct the normal form in three steps.

**Step (c.1):** Since $\Pi_2 = \text{span}(e_1, e_2)$ is a Lagrangian plane, there exists a linear symplectomorphism mapping $\Pi_2$ to $\{p = 0\}$. (The symplectic group $\text{Sp}(2n)$ acts transitively on the Lagrangian Grassmannian; see McDuff–Salamon [MS17], Lemma 2.1.4.)

**Step (c.2):** After Step (c.1), $e_1, e_2 \in \{p = 0\}$. Apply $\Phi_2 \in \text{GL}(2) \hookrightarrow \text{Sp}(4)$ (acting as $q \mapsto Aq$, $p \mapsto (A^{-T})p$) to place $e_1 = \partial_{q_1}$, $e_2 = \partial_{q_2}$.

**Step (c.3):** Write $e_3 = a_1\partial_{q_1} + a_2\partial_{q_2} + \alpha_1\partial_{p_1} + \alpha_2\partial_{p_2}$ and $e_4 = b_1\partial_{q_1} + b_2\partial_{q_2} + \beta_1\partial_{p_1} + \beta_2\partial_{p_2}$. We impose the four constraints:

- $\omega(e_2, e_3) = 0$: Since $\omega(\partial_{q_2}, \partial_{p_j}) = \delta_{2j}$, this gives $\alpha_2 = 0$.
- $\omega(e_4, e_1) = 0$: Since $\omega(\partial_{q_1}, \partial_{p_j}) = \delta_{1j}$, this gives $\beta_1 = 0$.
- $\omega(e_3, e_4) = 0$: Using $\omega(u,v) = \sum_j(u^{q_j}v^{p_j} - u^{p_j}v^{q_j})$, we get $a_1 \cdot 0 + a_2\beta_2 - \alpha_1 b_1 - 0 \cdot b_2 = a_2\beta_2 - \alpha_1 b_1 = 0$.
- Spanning: $e_1, e_2, e_3, e_4$ span $\mathbb{R}^4$ iff $\alpha_1 \neq 0$ and $\beta_2 \neq 0$.

(The fourth constraint $\omega(e_1, e_2) = 0$ is automatic since $e_1, e_2 \in \{p=0\}$.)

So $e_3 = (a_1, a_2, \alpha_1, 0)$ and $e_4 = (b_1, b_2, 0, \beta_2)$ with $a_2\beta_2 = \alpha_1 b_1$, $\alpha_1 \neq 0$, $\beta_2 \neq 0$.

Rescale $e_3 \mapsto e_3/\alpha_1$ and $e_4 \mapsto e_4/\beta_2$ (this does not change the planes $\Pi_k$). Now $\alpha_1 = \beta_2 = 1$, and the constraint becomes $b_1 = a_2$. Relabel $a_1/\alpha_1 \to a_1$, $a_2/\alpha_1 \to a_2$, $b_2/\beta_2 \to b_2$. The result is:
$$e_3 = a_1\,\partial_{q_1} + a_2\,\partial_{q_2} + \partial_{p_1}, \quad e_4 = a_2\,\partial_{q_1} + b_2\,\partial_{q_2} + \partial_{p_2}. \qquad \qed$$

**Remark on moduli.** The parameters $a_1, a_2, b_2$ are the moduli of the vertex. The special case $a_1 = a_2 = b_2 = 0$ gives $e_3 = \partial_{p_1}$, $e_4 = \partial_{p_2}$, so $\Pi_2 = \{p = 0\}$ and $\Pi_4 = \{q = 0\}$ are complementary. In general, $\Pi_4 = \text{span}(e_3, e_4)$ is a Lagrangian plane that is NOT complementary to $\Pi_2$.

---

## Step 2: Local Smoothing via Generating Functions

**Lemma 2** (Generating function description at a vertex). *In the canonical normal form of Lemma 1(c), the 4 sectors of $K$ near the vertex are the graph of $dg_v$ for a PL function $g_v: \mathbb{R}^2 \to \mathbb{R}$, provided the following transversality condition holds:*
$$a_1 \neq 0,\quad b_2 \neq 0,\quad \Delta := a_1 b_2 - a_2^2 \neq 0. \tag{$\star$}$$

*Proof.* In the normal form, the 4 edge directions are $e_1 = \partial_{q_1}$, $e_2 = \partial_{q_2}$, $e_3 = a_1\partial_{q_1} + a_2\partial_{q_2} + \partial_{p_1}$, $e_4 = a_2\partial_{q_1} + b_2\partial_{q_2} + \partial_{p_2}$. The projection $\pi: (q,p) \mapsto q$ restricted to each $\Pi_k$ is a linear map $\Pi_k \to \mathbb{R}^2$. This is an isomorphism iff $\Pi_k \cap \{q = 0\} = \{0\}$, i.e., $\Pi_k$ is transverse to the fibers. We check:

- $\Pi_2 = \{p = 0\}$: $\pi|_{\Pi_2}$ is the identity. ✅
- $\Pi_1 = \text{span}(e_1, e_4)$: $\pi(e_1) = (1,0)$, $\pi(e_4) = (a_2, b_2)$. Isomorphism iff $b_2 \neq 0$. ✅
- $\Pi_3 = \text{span}(e_2, e_3)$: $\pi(e_2) = (0,1)$, $\pi(e_3) = (a_1, a_2)$. Isomorphism iff $a_1 \neq 0$. ✅
- $\Pi_4 = \text{span}(e_3, e_4)$: $\pi(e_3) = (a_1, a_2)$, $\pi(e_4) = (a_2, b_2)$. Isomorphism iff $\Delta = a_1 b_2 - a_2^2 \neq 0$. ✅

When all four projections are isomorphisms, each $\Pi_k$ is the graph of a linear map $p = A_k q$: that is, $\Pi_k = \{(q, A_k q) : q \in \mathbb{R}^2\}$ for a unique symmetric matrix $A_k$ (symmetric because $\Pi_k$ is Lagrangian). The generating function is $h_k(q) = \frac{1}{2}q^T A_k q$, so $\nabla h_k = A_k q$ and $\Pi_k = \text{graph}(dh_k)$. We have $A_2 = 0$ (since $\Pi_2 = \{p = 0\}$). We compute the remaining $A_k$ by solving $p = A_k q$ on each plane.

On $\Pi_1 = \text{span}(e_1, e_4)$: a general point is $\alpha e_1 + \beta e_4 = (\alpha + \beta a_2, \beta b_2, 0, \beta)$, so $q = (\alpha + \beta a_2, \beta b_2)$ and $p = (0, \beta)$. From $q_2 = \beta b_2$ we get $\beta = q_2/b_2$, so $p_2 = q_2/b_2$ and $p_1 = 0$. Thus:
$$A_1 = \begin{pmatrix} 0 & 0 \\ 0 & 1/b_2 \end{pmatrix}.$$

On $\Pi_3 = \text{span}(e_2, e_3)$: a general point is $\alpha e_2 + \beta e_3 = (\beta a_1, \alpha + \beta a_2, \beta, 0)$, so $q = (\beta a_1, \alpha + \beta a_2)$ and $p = (\beta, 0)$. From $q_1 = \beta a_1$ we get $\beta = q_1/a_1$, so $p_1 = q_1/a_1$ and $p_2 = 0$. Thus:
$$A_3 = \begin{pmatrix} 1/a_1 & 0 \\ 0 & 0 \end{pmatrix}.$$

On $\Pi_4 = \text{span}(e_3, e_4)$: a general point is $\alpha e_3 + \beta e_4 = (\alpha a_1 + \beta a_2, \alpha a_2 + \beta b_2, \alpha, \beta)$, so $q = (\alpha a_1 + \beta a_2, \alpha a_2 + \beta b_2)$ and $p = (\alpha, \beta)$. Inverting: $\begin{pmatrix}\alpha \\ \beta\end{pmatrix} = \frac{1}{\Delta}\begin{pmatrix}b_2 & -a_2 \\ -a_2 & a_1\end{pmatrix}\begin{pmatrix}q_1 \\ q_2\end{pmatrix}$. Thus:
$$A_4 = \frac{1}{\Delta}\begin{pmatrix} b_2 & -a_2 \\ -a_2 & a_1 \end{pmatrix}.$$

Each sector $F_k$ (a cone in $\Pi_k$ bounded by two edge rays) projects to a sector $S_k$ in $q$-space, and on $S_k$ the surface $K$ is the graph of $dh_k$. We claim the 4 sectors $S_1, S_2, S_3, S_4$ tile a neighborhood of the origin in $\mathbb{R}^2$.

**Cyclic order of projected rays.** The 4 projected edge directions are $\pi(e_1) = (1,0)$, $\pi(e_2) = (0,1)$, $\pi(e_3) = (a_1, a_2)$, $\pi(e_4) = (a_2, b_2)$. Under condition $(\star)$, all four are nonzero. The link $\text{Lk}(v, K) \cong S^1$ maps continuously under $\pi$ to a closed curve in $\mathbb{R}^2 \setminus \{0\}$. Since $\pi|_{\Pi_k}$ is an isomorphism for each $k$ (by $(\star)$), the restriction of $\pi$ to each arc of the link is a homeomorphism onto its image. The projected link is therefore a piecewise-linear simple closed curve through the 4 rays $\mathbb{R}_{>0}\pi(e_k)$ in cyclic order. In particular, the 4 sectors $S_k$ (bounded by consecutive projected rays) tile a neighborhood of the origin. (If the projected rays were not in cyclic order, the projected link would have a self-intersection, contradicting the injectivity of $\pi$ on each face.)

Define $g_v: \mathbb{R}^2 \to \mathbb{R}$ by $g_v(q) = h_k(q)$ for $q \in S_k$. This is a piecewise-quadratic function with $K \cap U = \text{graph}(dg_v)$ in a neighborhood $U$ of $v$.

**Regularity of $g_v$:** On the boundary ray $\pi(e_k)$ between sectors $S_k$ and $S_{k+1}$, we have $\nabla h_k(\pi(e_k)) = A_k \pi(e_k)$ and $\nabla h_{k+1}(\pi(e_k)) = A_{k+1}\pi(e_k)$. Since $e_k \in \Pi_k \cap \Pi_{k+1}$, the $p$-component of $e_k$ equals both $A_k \pi(e_k)$ and $A_{k+1}\pi(e_k)$. Therefore $\nabla h_k = \nabla h_{k+1}$ along the ray $\pi(e_k)$, so $g_v$ is $C^1$ (not merely $C^0$). The discontinuity is in the second derivatives (the Hessians $A_k$ jump across crease lines). In particular, $g_v$ is Lipschitz with Lipschitz gradient. $\qed$

**Remark on condition $(\star)$.** If $(\star)$ fails, we choose a **different** Lagrangian plane $\Pi_0$ as the base for the cotangent identification $\mathbb{R}^4 \cong T^*\Pi_0$, instead of $\Pi_2 = \{p = 0\}$. The set of Lagrangian planes transverse to a given plane is open and dense in $\Lambda(2)$ (the Lagrangian Grassmannian), and a finite intersection of open dense sets is open dense. Therefore there exists $\Pi_0$ transverse to all four $\Pi_k$ simultaneously. Identifying $\mathbb{R}^4 \cong T^*\Pi_0$ via a linear symplectomorphism mapping $\Pi_0$ to the zero section, the argument of Lemma 2 applies verbatim (with $\Pi_0$ playing the role of $\{p = 0\}$).

**Proposition 1** (Local Lagrangian smoothing). *For each vertex $v \in V$ and each $\epsilon > 0$ sufficiently small, there exists a smooth Lagrangian surface $K_\epsilon^{(v)}$ in a neighborhood of $v$ such that:*
1. *$K_\epsilon^{(v)}$ agrees with $K$ outside $B(v, C\epsilon)$ for a constant $C$ depending on the vertex geometry.*
2. *$K_\epsilon^{(v)}$ is a smooth embedded Lagrangian surface.*
3. *$K_\epsilon^{(v)} \to K \cap B(v, R)$ in the Hausdorff topology as $\epsilon \to 0$.*
4. *$K_\epsilon^{(v)}$ is the graph of $dg_v^\epsilon$ for a smooth function $g_v^\epsilon: \mathbb{R}^2 \to \mathbb{R}$.*

*Proof.* By Lemma 2, after applying the canonical normal form and (if necessary) a further symplectomorphism to ensure $(\star)$, the surface $K$ near $v$ is the graph of $dg_v$ for a PL function $g_v$.

**Smoothing by mollification.** Let $\chi: \mathbb{R}^2 \to [0,\infty)$ be a smooth bump function with $\text{supp}(\chi) \subset B(0,1)$, $\int \chi = 1$, and $\chi_\epsilon(q) = \epsilon^{-2}\chi(q/\epsilon)$. Define:
$$g_v^\epsilon = g_v * \chi_\epsilon.$$

Since $g_v$ is PL (piecewise quadratic), $g_v^\epsilon$ is smooth for all $\epsilon > 0$. The graph $\text{graph}(dg_v^\epsilon) = \{(q, \nabla g_v^\epsilon(q))\}$ is automatically a smooth Lagrangian submanifold of $T^*\mathbb{R}^2 \cong \mathbb{R}^4$ (since $\omega|_{\text{graph}(dh)} = d(dh) = 0$ for any smooth $h$; more precisely, $\text{graph}(dh)^*\omega = \sum_j dq_j \wedge d(\partial_{q_j}h) = \sum_{j,k} \partial^2_{q_j q_k}h\, dq_j \wedge dq_k = 0$ by symmetry of the Hessian).

**Properties:**

(1) Outside $B(0, C\epsilon)$: if $q$ is at distance $> \epsilon$ from all crease lines of $g_v$, then $g_v$ is quadratic (hence smooth) near $q$, so $g_v * \chi_\epsilon = g_v$ near $q$. The crease lines emanate from the origin, so at distance $r$ from the origin, the distance to the nearest crease is $\geq cr$ for some $c > 0$. Thus $g_v^\epsilon = g_v$ for $|q| > \epsilon/c$, giving $C = 1/c$.

(2) Smoothness: $g_v^\epsilon$ is $C^\infty$ since it is a convolution of a locally Lipschitz function with a smooth mollifier.

**Embeddedness:** The map $q \mapsto (q, \nabla g_v^\epsilon(q))$ is an embedding since it is a graph over $\mathbb{R}^2$.

(3) Hausdorff convergence: since $g_v$ is $C^1$ with Lipschitz gradient (Lemma 2), standard mollification estimates give $\|\nabla g_v^\epsilon - \nabla g_v\|_{C^0} \leq C_1 \epsilon$ (the modulus of continuity of $\nabla g_v$ is $O(\epsilon)$ since the Hessian jumps are bounded). The Hausdorff distance between $\text{graph}(dg_v^\epsilon)$ and $\text{graph}(dg_v)$ is therefore $\leq C_2\epsilon$.

(4) By construction. $\qed$

**Remark.** The key point is that the graph of $dh$ is Lagrangian for **any** smooth function $h$, so the Lagrangian condition is automatic after mollification. This is the fundamental advantage of the generating function approach. The valence-4 condition ensures that the PL function $g_v$ exists (via Lemma 2), which requires the 4 face planes to project diffeomorphically onto a common base — guaranteed by the transversality condition $(\star)$ (achievable by choice of base plane).

---

## Step 3: Edge Smoothing

**Lemma 3** (Edge smoothing). *Along each edge $e$ of $K$ (away from vertex neighborhoods), the two adjacent faces share the edge direction and lie in Lagrangian planes $\Pi_i, \Pi_j$ with $\dim(\Pi_i \cap \Pi_j) \geq 1$. In a neighborhood of a point on $e$, $K$ is the graph of $dg_e$ for a PL convex function $g_e$ with a single crease. Mollification $g_e \mapsto g_e * \chi_\epsilon$ produces a smooth Lagrangian.*

*Proof.* Near a point on $e$ (away from vertices), identify $\mathbb{R}^4 \cong T^*\Pi_i$ with $\Pi_i$ as the zero section. We need $\Pi_j$ to be transverse to the fibers of $T^*\Pi_i$, i.e., $\Pi_i + \Pi_j = \mathbb{R}^4$. Since $\Pi_i$ and $\Pi_j$ are distinct Lagrangian planes sharing a line (the edge direction), $\dim(\Pi_i \cap \Pi_j) = 1$, so $\dim(\Pi_i + \Pi_j) = 2 + 2 - 1 = 3$. This is NOT all of $\mathbb{R}^4$. To fix this, we choose a base plane $\Pi_0$ transverse to both $\Pi_i$ and $\Pi_j$ (such $\Pi_0$ exists by the same open-density argument as in the Remark on $(\star)$). Identifying $\mathbb{R}^4 \cong T^*\Pi_0$, both $F_i$ and $F_j$ are graphs of linear 1-forms $dl_i$ and $dl_j$ over $\Pi_0$. The union $F_i \cup F_j$ near the edge is the graph of $dg_e$ where $g_e(q) = \min(l_i(q), l_j(q))$ (or $\max$, depending on orientation). Since $l_i$ and $l_j$ are linear functions agreeing on the projected edge line, $g_e$ is PL with a single crease. Mollification $g_e * \chi_\epsilon$ produces a smooth function whose graph is Lagrangian (graph of $dh$ is Lagrangian for any smooth $h$). $\qed$

---

## Step 4: Global Assembly

**Proposition 2** (Global smoothing). *For $\epsilon > 0$ sufficiently small, the local smoothings combine to give a globally well-defined smooth Lagrangian surface $K_\epsilon \subset \mathbb{R}^4$.*

*Proof.* Let $C_v$ be the constant from Proposition 1 for vertex $v$, and set $C_{\max} = \max_v C_v$. Choose $\epsilon < \delta / C_{\max}$. Then the modification regions $B(v_i, C_{v_i}\epsilon)$ are pairwise disjoint (since $C_{v_i}\epsilon < \delta \leq \frac{1}{3}|v_i - v_j|$ for $i \neq j$).

**Edge-vertex compatibility.** We must verify that the vertex smoothing (Proposition 1) and edge smoothing (Lemma 3) are compatible. Both are defined via generating functions, but using potentially different cotangent bundle identifications of $\mathbb{R}^4$:

- At vertex $v$: $K_\epsilon^{(v)} = \text{graph}(dg_v^\epsilon)$ in $T^*\Pi_0^{(v)}$ for a base plane $\Pi_0^{(v)}$.
- Along edge $e$: $K_\epsilon^{(e)} = \text{graph}(dg_e^\epsilon)$ in $T^*\Pi_0^{(e)}$ for a base plane $\Pi_0^{(e)}$ transverse to both adjacent face planes (Lemma 3).

(The cotangent identification is a computational device; the output of both constructions is a subset of $\mathbb{R}^4$, and compatibility is checked as subsets of $\mathbb{R}^4$.)

In the overlap region (near edge $e$, outside $B(v, C_v\epsilon)$ but inside the edge smoothing zone), both constructions agree with $K$ itself: the vertex smoothing equals $K$ outside $B(v, C_v\epsilon)$ (Proposition 1, property 1), and the edge smoothing equals $K$ away from the crease (which is the edge $e$ itself). On the flat faces (away from both edges and vertices), $K$ is already smooth and both constructions leave it unchanged.

The only potential issue is near an edge $e$, inside $B(v, C_v\epsilon)$: here the vertex smoothing is active and modifies the edge crease. But the vertex smoothing handles all creases within its ball (since $g_v^\epsilon = g_v * \chi_\epsilon$ smooths all crease lines of $g_v$ simultaneously). So the edge smoothing is only needed **outside** all vertex balls, where it operates on a single crease line — and there is no overlap with the vertex smoothing.

**Assembly:** Define $K_\epsilon$ by:
- In $B(v, C_v\epsilon)$ for each vertex $v$: use $K_\epsilon^{(v)} = \text{graph}(dg_v^\epsilon)$ from Proposition 1.
- Along each edge $e$, in the region $\{q : \text{dist}(q, e) < \epsilon\} \setminus \bigcup_v B(v, C_v\epsilon)$: use $\text{graph}(dg_e^\epsilon)$ from Lemma 3.
- On face interiors (distance $> \epsilon$ from all edges): keep $K$ unchanged.

**Smoothness at boundaries.** At the boundary of the edge-smoothing zone (distance $\epsilon$ from the crease), $g_e$ is already quadratic (hence smooth), so $g_e * \chi_\epsilon = g_e$ there — the mollified and unmollified definitions literally agree, and the transition is $C^\infty$. Similarly, at the boundary of each vertex ball $B(v, C_v\epsilon)$, $g_v^\epsilon = g_v$ (Proposition 1, property 1), so the vertex smoothing and the edge/face definitions agree exactly.

These three regions cover $K$, overlap only where all active constructions agree, and each piece is smooth. Therefore $K_\epsilon$ is globally well-defined and smooth. $\qed$

---

## Step 5: Hamiltonian Isotopy

**Theorem 1** (Main result). *The family $\{K_t\}_{t \in (0,1]}$ defined by $K_t = K_\epsilon$ with $\epsilon = t$ is a Hamiltonian isotopy of smooth Lagrangian submanifolds, extending to a topological isotopy on $[0,1]$ with $K_0 = K$.*

*Proof.*

**(a) Each $K_t$ is a smooth Lagrangian submanifold.** Follows from Proposition 2.

**(b) The family is a Hamiltonian isotopy for $t \in (0,1]$.**

The family $K_t$ varies smoothly in $t > 0$ (since $g_v^\epsilon$ and $g_e^\epsilon$ depend smoothly on $\epsilon$). The velocity of the isotopy defines a vector field $V_t$ along $K_t$. Since each $K_t$ is Lagrangian, the 1-form $\alpha_t := \iota_{V_t}\omega|_{K_t}$ is closed (by Cartan's formula: $\frac{d}{dt}\omega|_{K_t} = (d\alpha_t + \iota_{V_t}d\omega)|_{K_t} = d\alpha_t|_{K_t}$, and $\frac{d}{dt}\omega|_{K_t} = 0$ since each $K_t$ is Lagrangian; see McDuff–Salamon [MS17], Proposition 9.33).

To show $\alpha_t$ is exact (hence the isotopy is Hamiltonian), we show that the **cohomology class** $[\iota_t^*\lambda] \in H^1(K_t; \mathbb{R})$ is **independent of $t$**.

**Claim:** $\frac{d}{dt}[\iota_t^*\lambda] = 0$ in $H^1(K_t; \mathbb{R})$.

*Proof of claim.* Since $\omega = d\lambda$ and $\omega|_{K_t} = 0$, we have $d(\iota_t^*\lambda) = 0$, so $\iota_t^*\lambda$ is a closed 1-form on $K_t$. Its cohomology class is determined by its periods $\int_\gamma \iota_t^*\lambda$ over a basis of $H_1(K_t; \mathbb{Z})$.

The modification $K \leadsto K_t$ is supported in the union of small balls $B(v, C_v t)$ around vertices and thin tubes around edges. For $t$ small, these regions are contractible (each is a small disk neighborhood). Therefore, any closed curve $\gamma \subset K_t$ can be deformed (within $K_t$) to avoid the modification regions. On the unmodified part, $K_t = K$, so $\iota_t^*\lambda = \iota_0^*\lambda$ (where $\iota_0$ is the inclusion of $K$). Thus:
$$\int_\gamma \iota_t^*\lambda = \int_\gamma \iota_0^*\lambda$$
for all $[\gamma] \in H_1(K_t; \mathbb{Z})$, so $[\iota_t^*\lambda] = [\iota_0^*\lambda]$ is constant. $\qed$

It follows that $\alpha_t$ is exact. To see this precisely: since $[\iota_t^*\lambda]$ is constant, write $\iota_t^*\lambda = dS_t + \eta$ where $\eta$ is a fixed closed 1-form representing $[\iota_0^*\lambda]$ (independent of $t$) and $S_t$ is a smooth function on $K_t$ (depending smoothly on $t$). Differentiating $\iota_t^*\lambda = dS_t + \eta$ with respect to $t$ and using the identity $\frac{d}{dt}\iota_t^*\lambda = \alpha_t + d(\lambda(V_t) \circ \iota_t)$ (Cartan's magic formula applied to the pullback), we obtain $\alpha_t = d(\dot{S}_t - \lambda(V_t) \circ \iota_t)$, which is exact. The Hamiltonian is $H_t = \dot{S}_t - \lambda(V_t) \circ \iota_t$. (See McDuff–Salamon [MS17], Proposition 9.33.) The isotopy is therefore Hamiltonian.

**Remark (compact case).** If $K$ is a closed surface, then $H^1(K; \mathbb{R}) \neq 0$ and $K_t$ is NOT globally exact (by Gromov's theorem: no closed exact Lagrangian in $\mathbb{R}^{2n}$; see Gromov [Gr85], §2.3.B, or Audin–Lalonde–Polterovich [ALP94], Theorem 3.1). However, the Hamiltonian isotopy argument does **not** require global exactness — it only requires that $[\iota_t^*\lambda]$ is constant in $t$, which we proved above. The class $[\iota_0^*\lambda] \in H^1(K; \mathbb{R})$ may be nonzero, but it is the **same** nonzero class for all $t$.

**(c) Topological isotopy extending to $t = 0$.**

We construct an explicit continuous map $\Phi: K \times [0,1] \to \mathbb{R}^4$ with $\Phi(\cdot, 0) = \iota_0$ (inclusion of $K$) and $\Phi(\cdot, t)$ a homeomorphism onto $K_t$ for $t > 0$.

On the face interiors (away from edges and vertices), $K_t = K$, so $\Phi(x, t) = x$.

Near a vertex $v$: in the generating function picture, $K$ is $\text{graph}(dg_v)$ and $K_t$ is $\text{graph}(dg_v^t)$. Define $\Phi(q, \nabla g_v(q), t) = (q, \nabla g_v^t(q))$. This is continuous in $(q, t)$ since $g_v$ is $C^1$ with Lipschitz gradient (Lemma 2), and standard mollification estimates give $\|\nabla g_v^t - \nabla g_v\|_{C^0(B_R)} \leq C_R \cdot t$ for each $R > 0$ (the modulus of continuity of $\nabla g_v$ is $O(t)$ because the Hessian jumps are bounded). For $t > 0$, $\Phi(\cdot, t)$ is a homeomorphism (both $K$ and $K_t$ are graphs over the same $q$-domain). At $t = 0$, $\Phi(\cdot, 0) = \text{id}$.

Near edges: similarly, $\Phi(q, dg_e(q), t) = (q, dg_e^t(q))$.

These definitions are compatible on overlaps (where both equal the identity), so $\Phi$ is globally well-defined and continuous. $\qed$

---

## Step 6: Discussion of Potential Obstructions

### 6.1 Could the answer be NO?

The problem asks whether $K$ **necessarily** has a Lagrangian smoothing. We have constructed one, but we should verify that no hidden obstruction invalidates the construction.

**Embeddedness.** The smoothed surface $K_t$ is embedded (not just immersed) because it is globally the graph of a 1-form $dg_t$ over a 2-dimensional base (in each local chart). Graphs are automatically embedded. The global embeddedness follows from the fact that $K$ is embedded and the modification is $C^0$-small: for $t$ sufficiently small, $K_t$ is $C^0$-close to $K$ and hence embedded (by a standard transversality argument; see Hirsch [Hi76], Chapter 3, Theorem 1.4).

**Topology.** The smoothing preserves the homeomorphism type of $K$: at each vertex, the PL disk (cone on 4 arcs) is replaced by a smooth disk (the graph of a smooth function over the same domain). The map $\Phi(\cdot, t)$ is a homeomorphism for all $t \geq 0$.

**Maslov class.** The Maslov class $\mu \in H^1(K_t; \mathbb{Z})$ is an invariant of the smooth Lagrangian $K_t$, not an obstruction to its existence. On face/edge regions (Lagrangian graphs over $\{p=0\}$), the tangent plane is always transverse to the fiber, so the Maslov class vanishes there. The total Maslov class is determined by the combinatorics of $K$ and is independent of $t > 0$.

**Gromov's theorem.** No closed Lagrangian in $\mathbb{R}^{2n}$ is exact (Gromov [Gr85], §2.3.B). If $K$ is closed, $K_t$ is not exact. But our proof does not claim exactness — it only uses the constancy of $[\iota_t^*\lambda]$, which holds regardless.

### 6.2 Conclusion

No obstruction prevents the construction. The answer is **YES**: every polyhedral Lagrangian surface with exactly 4 faces at every vertex has a Lagrangian smoothing.

---

## References

- **[ALP94]** M. Audin, F. Lalonde, L. Polterovich, "Symplectic rigidity: Lagrangian submanifolds," in *Holomorphic Curves in Symplectic Geometry* (M. Audin, J. Lafontaine, eds.), Progress in Math. **117**, Birkhäuser, 1994, pp. 271–321. (Theorem 3.1: no closed exact Lagrangian in $\mathbb{R}^{2n}$.)
- **[Br19]** R. L. Bryant, answer to "Lagrangian surgery," MathOverflow, 2019. https://mathoverflow.net/a/332983. (Explicit parametric Lagrangian surgery construction. While not peer-reviewed, this provides a useful exposition of the Polterovich construction; the underlying result is [Po91].)
- **[Gr85]** M. Gromov, "Pseudo holomorphic curves in symplectic manifolds," *Invent. Math.* **82** (1985), 307–347. (§2.3.B: Lagrangian intersection theory.)
- **[Hi76]** M. W. Hirsch, *Differential Topology*, Graduate Texts in Mathematics **33**, Springer, 1976. (Chapter 3, Theorem 1.4: $C^0$-close embeddings.)
- **[Hk20]** J. Hicks, "Tropical Lagrangian hypersurfaces are unobstructed," *J. Topol.* **13** (2020), 1409–1454. arXiv:1911.02956. (Tropical-to-Lagrangian correspondence for hypersurfaces.)
- **[Ma19]** D. Matessi, "Lagrangian pairs of pants," *Int. Math. Res. Not.* **2019** (2019), 6295–6354. arXiv:1802.02993. (Lagrangian smoothing via generating functions on blown-up domains.)
- **[MS17]** D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford University Press, 2017. (Lemma 2.1.4: transitivity on Lagrangian Grassmannian. Proposition 9.33: Lagrangian isotopy and Hamiltonian condition.)
- **[Po91]** L. Polterovich, "The surgery of Lagrange submanifolds," *Geom. Funct. Anal.* **1** (1991), 198–210. (Original Lagrangian surgery construction.)

---

## Summary

The proof constructs the Lagrangian smoothing via generating functions and mollification:

1. **Normal form (Step 1, Lemma 1).** At each valence-4 vertex, 4 edge directions $e_1, \ldots, e_4$ span $\mathbb{R}^4$ with cyclic $\omega$-orthogonality. A canonical normal form is established by explicit linear algebra: $e_1 = \partial_{q_1}$, $e_2 = \partial_{q_2}$, $e_3 = a_1\partial_{q_1} + a_2\partial_{q_2} + \partial_{p_1}$, $e_4 = a_2\partial_{q_1} + b_2\partial_{q_2} + \partial_{p_2}$, with 3 real moduli $(a_1, a_2, b_2)$. Citation: [MS17], Lemma 2.1.4.

2. **Generating function (Step 2, Lemma 2).** After choosing a base Lagrangian plane transverse to all 4 face planes (always possible by open-density of transverse pairs), the 4 sectors of $K$ near $v$ are the graph of $dg_v$ for a PL (piecewise-quadratic) function $g_v$. The matrices $A_k$ are computed explicitly.

3. **Mollification (Step 2, Proposition 1).** Convolve $g_v$ with a mollifier: $g_v^\epsilon = g_v * \chi_\epsilon$. The graph of $dg_v^\epsilon$ is automatically a smooth embedded Lagrangian (since $\text{graph}(dh)^*\omega = 0$ for any smooth $h$, by symmetry of the Hessian). This resolves the vertex singularity.

4. **Edge smoothing (Step 3, Lemma 3).** Along edges, $K$ is the graph of a PL function with a single crease. The same mollification applies.

5. **Global assembly (Step 4, Proposition 2).** Vertex and edge smoothings are compatible: both are defined via generating functions, and they agree with $K$ in their overlap regions. The smoothed surface $K_\epsilon$ is globally well-defined and smooth.

6. **Hamiltonian isotopy (Step 5, Theorem 1).** The cohomology class $[\iota_t^*\lambda] \in H^1(K_t; \mathbb{R})$ is constant in $t$ (since the modification is supported in contractible regions). By [MS17], Proposition 9.33, constancy of this class implies the Lagrangian isotopy is Hamiltonian. The topological isotopy $\Phi: K \times [0,1] \to \mathbb{R}^4$ is constructed explicitly via the generating function parametrization.

The answer is **YES**. $\qed$

---

## Appendix: Partial Lean 4 Verification

The algebraic and geometric skeleton of this proof has been formally verified in Lean 4 + Mathlib. The file `FirstProof/P08_LagrangianSmoothing.lean` verifies the following components:

1. **Symplectic orthogonality** (`omega_e2_e3`, `omega_e3_e4`, `omega_e4_e1`): The four constraints $\omega(e_k, e_{k+1}) = 0$ in the canonical normal form. Each reduces to a polynomial identity verified by `ring`.

2. **Spanning** (`edge_matrix_det`, `constraint_b1_eq_a2`): The determinant of the edge matrix $[e_1 | e_2 | e_3 | e_4]$ equals $\alpha_1 \cdot \beta_2$ after normalization. After rescaling, the constraint $b_1 = a_2$ follows from $a_2 \beta_2 = \alpha_1 b_1$ with $\alpha_1 = \beta_2 = 1$.

3. **Generating function matrices** (`A1_entry`, `A3_entry`, `A4_det`): The Hessian matrices $A_1 = \begin{pmatrix}0 & 0 \\ 0 & 1/b_2\end{pmatrix}$, $A_3 = \begin{pmatrix}1/a_1 & 0 \\ 0 & 0\end{pmatrix}$, and $A_4 = \frac{1}{\Delta}\begin{pmatrix}b_2 & -a_2 \\ -a_2 & a_1\end{pmatrix}$ where $\Delta = a_1 b_2 - a_2^2$.

4. **Transversality condition** (`transversality_check`): The condition $(\star)$: $a_1 \neq 0$, $b_2 \neq 0$, and $\Delta \neq 0$ ensures all four face planes project isomorphically onto the base.

5. **Lagrangian property of graphs** (`hessian_symmetry_implies_lagrangian`): Hessian symmetry $\partial^2 h / \partial q_1 \partial q_2 = \partial^2 h / \partial q_2 \partial q_1$ implies the pullback $\omega|_{\text{graph}(dh)} = 0$. This is the fundamental reason mollification preserves the Lagrangian condition.

6. **Proof structure** (`proof_structure`): The 5-step chain: normal form → generating function → mollification → global assembly → Hamiltonian isotopy.

**Scope and limitations.** Symplectic geometry (Lagrangian Grassmannian, Hamiltonian isotopy, cohomology class constancy), mollification theory, and the global assembly argument are beyond current Mathlib capabilities. The Lean file verifies the linear algebra computations that underpin the local analysis.

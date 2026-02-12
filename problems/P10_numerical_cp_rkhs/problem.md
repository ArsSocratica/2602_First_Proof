# Problem 10 — Numerical Linear Algebra: Preconditioned CG for CP Decomposition with RKHS

## Problem Statement

Given a $d$-way tensor $\mathcal{T} \in \mathbb{R}^{n_1 \times n_2 \times \cdots \times n_d}$ such that the data is unaligned (meaning the tensor $\mathcal{T}$ has missing entries), we consider the problem of computing a CP decomposition of rank $r$ where some modes are infinite-dimensional and constrained to be in a Reproducing Kernel Hilbert Space (RKHS). We want to solve this using an alternating optimization approach, and our question is focused on the mode-$k$ subproblem for an infinite-dimensional mode. For the subproblem, the CP factor matrices $A_1, \dots, A_{k-1}, A_{k+1}, \dots, A_d$ are fixed, and we are solving for $A_k$.

### Notation

- $N = \prod_i n_i$: product of all sizes
- $n \equiv n_k$: size of mode $k$
- $M = \prod_{i \neq k} n_i$: product of all dimensions except $k$, assume $n \ll M$
- $q \ll N$: number of observed entries
- $T \in \mathbb{R}^{n \times M}$: mode-$k$ unfolding with missing entries set to zero
- $S \in \mathbb{R}^{N \times q}$: selection matrix (subset of $N \times N$ identity) such that $S^T \text{vec}(T)$ selects the $q$ known entries
- $Z = A_d \odot \cdots \odot A_{k+1} \odot A_{k-1} \odot \cdots \odot A_1 \in \mathbb{R}^{M \times r}$: Khatri-Rao product
- $B = TZ$: MTTKRP of tensor and Khatri-Rao product
- $A_k = KW$ where $K \in \mathbb{R}^{n \times n}$ is the PSD RKHS kernel matrix
- $W \in \mathbb{R}^{n \times r}$: the unknown

### System to Solve

$$\left[(Z \otimes K)^T S S^T (Z \otimes K) + \lambda (I_r \otimes K)\right] \text{vec}(W) = (I_r \otimes K) \text{vec}(B)$$

This is a system of size $nr \times nr$. Using a standard linear solver costs $O(n^3 r^3)$, and explicitly forming the matrix is an additional expense.

### Question

Explain how an iterative preconditioned conjugate gradient linear solver can be used to solve this problem more efficiently. Explain the method and choice of preconditioner. Explain in detail how the matrix-vector products are computed and why this works. Provide complexity analysis. We assume $n, r < q \ll N$. Avoid any computation of order $N$.

## Author

Tamara G. Kolda (MathSci.ai) and Rachel Ward (University of Texas at Austin)

## Key Concepts

- CP tensor decomposition with missing data
- Reproducing Kernel Hilbert Spaces (RKHS)
- Preconditioned Conjugate Gradient (PCG)
- Khatri-Rao products and MTTKRP
- Kronecker product structure exploitation
- Efficient matrix-vector products avoiding $O(N)$ cost

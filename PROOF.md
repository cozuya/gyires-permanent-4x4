# Proof

This is a readable account of the argument that is formalized in this repository. The
section numbers refer to Lean files where the corresponding step is proved.

## Statement

For a real $4\times4$ matrix $A$ write

```math
p=\mathrm{per}(A),\quad g=\mathrm{per}(AA^T),\quad h=\mathrm{per}(A^TA),\quad z=\mathrm{per}(A^2),
```

with ordinary matrix products. If $A$ is doubly stochastic (nonnegative entries, every row
and column sum equal to 1), then

```math
3\,(g+h+2z)\le 128\,p^2,
```

with equality if and only if $A=J_4$, the matrix with every entry $1/4$.

## 1. Reduction to a stronger inequality

For square real matrices $M,N$ of any size $n$,

```math
\mathrm{per}(MM^T)+\mathrm{per}(NN^T)\ \ge\ 2\mathrm{per}(MN^T). \qquad (1)
```

*Proof* ([Reduction.lean](RequestProject/Reduction.lean)). For a function
$\varphi:[n]\to[n]$ put $u_M(\varphi)=\prod_i M_{i,\varphi(i)}$. Expanding the entries of
$MN^T$ gives

```math
\mathrm{per}(MN^T)=B(u_M,u_N),\qquad
B(a,b)=\sum_{\sigma\in S_n}\sum_{\varphi}a(\varphi\circ\sigma^{-1})\,b(\varphi).
```

The form $B$ is positive semidefinite, because
$n!\,B(d,d)=\sum_{\psi}\bigl(\sum_{\tau\in S_n}d(\psi\circ\tau)\bigr)^2$. Applying this to
$d=u_M-u_N$ and using $B(u_M,u_N)=B(u_N,u_M)$ gives (1). ∎

Define the degree-8 form

```math
H(M)=32\mathrm{per}(M)^2-3\mathrm{per}(MM^T).
```

Since $\mathrm{per}(A^T)=\mathrm{per}(A)$ and $A^T$ is doubly stochastic when
$A$ is,

```math
128p^2-3(g+h+2z)=2H(A)+2H(A^T)+3\,(g+h-2z),
```

and $g+h-2z\ge 0$ by (1) with $M=A$, $N=A^T$. Therefore it suffices to prove

```math
H(A)\ge 0 \qquad (2)
```

for every doubly stochastic $A$, with equality only at $A=J_4$.

Then equality in the target forces $H(A)=0$, hence $A=J_4$. Conversely
$J_4^2=J_4J_4^T=J_4^TJ_4=J_4$ and $\mathrm{per}(J_4)=24/4^4=3/32$, so both sides
equal $9/8$ at $J_4$ ([Gyires.lean](RequestProject/Gyires.lean),
[Equality.lean](GyiresEquality/Equality.lean)).

$H$ is invariant under independent permutations of rows and of columns:
$\mathrm{per}(RMC)=\mathrm{per}(M)$ and $(RMC)(RMC)^T=R(MM^T)R^T$.
It is **not** invariant under transposition, which is why both $H(A)$ and $H(A^T)$
appear above.

## 2. Reduction to cones of faces

Encode a set of matrix positions by a 16-bit mask. For a mask $S$, let $K(S)$ be the
set of nonnegative real matrices with equal row and column sums (some common value
$c\ge0$) that vanish outside $S$. A *face* of the Birkhoff polytope corresponds to a mask
that is the union of the supports of the permutation matrices it contains. Its *center*
$V_S$ is the sum of those permutation matrices.

**Entry step** ([Gyires.lean](RequestProject/Gyires.lean)). Let $m$ be the smallest entry
of $A$. Permuting rows and columns, which does not change $H$, put it at position
$(0,0)$. Then $A=mJ+x$, where $J$ is the all-ones matrix and $x=A-mJ$ is nonnegative,
has all line sums $1-4m$, and vanishes at $(0,0)$. That is, $x\in K(F)$ for the face
$F=\{x_{00}=0\}$.

**Support lemma** ([Faces.lean](RequestProject/Faces.lean)). If $x\in K(S)$ and
$x_{ij}>0$, some permutation matrix supported in $S$ has a 1 at $(i,j)$. This follows from
Mathlib's Birkhoff–von Neumann theorem applied to $x/c$. Consequently $x$ is supported in
the union of the permutation supports inside $S$.

**Pulling step** ([TreeSound.lean](RequestProject/TreeSound.lean), `FaceState.of_pull`).
Let $V=V_S$. Put $\tau=\min\{x_{ij}/V_{ij}: V_{ij}>0\}\ge 0$ and $x'=x-\tau V$. Then $x'$ is
nonnegative, has equal line sums, and vanishes at the minimizing position. By the support
lemma it lies in $K(f)$ for some facet $f$ of the current face. Repeating, the dimension
drops at each step until a single permutation matrix $P$ remains, where $x=cP$.

So every doubly stochastic $A$ satisfies, after a row and column permutation,

```math
A=\sum_{k=0}^{9}t_kV_k,\qquad t_k\ge 0, \qquad (3)
```

where $V_0=J$, $V_1$ is the center of $F$, and $V_1,\dots,V_9$ are the centers of a
descending chain of faces $F\supset F_2\supset\dots$ ending at a vertex. Some $t_k$ may be
zero, so boundary matrices, zero entries and singular matrices are all covered.

## 3. The finite certificate

For a fixed chain, $H(\sum_k t_kV_k)$ is a homogeneous polynomial of degree 8 in
$t_0,\dots,t_9$, with 24,310 monomials (17 choose 9). Every $V_k$ has nonnegative
integer entries. So $\mathrm{per}(M)$ and $\mathrm{per}(MM^T)$, as polynomials in
$t$, have nonnegative integer coefficients. The certificate checks, coefficient by
coefficient,

```math
32\cdot[\mathrm{per}(M)^2]_\alpha\ \ge\ 3\cdot[\mathrm{per}(MM^T)]_\alpha, \qquad |\alpha|=8. \qquad (4)
```

Then every coefficient of $H$ is nonnegative, so $H\ge0$ on the whole cone (3).

**Symmetry.** The checker does not enumerate all chains. At each face it keeps only the
row and column permutations fixing every center chosen so far. Facets in the same orbit
of that group are checked once (`FaceState.of_sym`); this is sound because $H$ is invariant
and the chosen centers are fixed. The top level uses the 576-element group of row and
column permutations, so the 16 facets $x_{ij}=0$ reduce to the single facet $F$.

**Size.** The resulting tree has exactly **65,376 leaves**, each a chain of ten
generators. This equals the number of orbits of complete flags of the $4\times4$ Birkhoff
polytope under row and column permutations ($37{,}656{,}576/576$), the same count as in the
[original computational proof](original/README.md).

**How Lean checks it** ([GyiresCompute/Basic.lean](GyiresCompute/Basic.lean),
[PolySound.lean](RequestProject/PolySound.lean), [HEval.lean](RequestProject/HEval.lean)).
The checker `checkNode` recomputes, from the 24 permutation matrices, every face closure,
center, candidate facet, stabilizer and leaf polynomial. Polynomials are dense arrays of
natural numbers indexed by exponent vectors, multiplied with precomputed monomial tables.
The tables themselves are verified by `tableOK`. $\mathrm{per}(M)$ and
$\mathrm{per}(MM^T)$ are computed by Laplace expansion along rows $\{0,1\}$. The theorem
`checkNode_sound` proves in Lean that a `true` result implies $H\ge 0$ on every
matrix (3) below the checked node. The certificate is split into 13 independent pieces
below the first two levels of the tree. Each piece is evaluated with `native_decide`
([Cert/](RequestProject/Cert)).

## 4. Equality

For every one of the 65,376 chains, the coefficients with equality in (4) are exactly
those of $t_0^8$ and $t_0^7t_k$ ($k=1,\dots,9$). This reflects $H(J)=0$ and
$\nabla H(J)=0$. In particular the coefficient of each pure power $t_k^8$ with $k\ge1$,
which equals $H(V_k)$, is strictly positive.

The strict checker `checkNodeS` ([GyiresStrictCompute/Basic.lean](GyiresStrictCompute/Basic.lean))
adds this test at every leaf. `checkNodeS_sound`
([StrictSound.lean](GyiresEquality/StrictSound.lean)) proves the strengthened statement:
$H(\sum t_kV_k+x)>0$ whenever $x\ne0$ or some $t_k>0$ with $k\ge1$. The proof uses
$H(M)\ge c_k\,t_k^8$ with $c_k>0$, since all other terms are nonnegative.

In the entry step, $x=0$ forces $A=mJ$ and hence $A=J_4$. So $H(A)>0$ for every
doubly stochastic $A\ne J_4$ (`permanent_gram_lt`), which proves (2) and the equality
case.

## 5. Ratio form

Every doubly stochastic matrix has positive permanent. By Birkhoff's theorem some
permutation $\sigma$ has all entries $A_{i\sigma(i)}>0$, and that diagonal contributes a
positive term to the permanent. The products $AA^T$, $A^TA$ and $A^2$ are doubly
stochastic, so the denominator in the Cheon–Wanless form is positive, and that form is
equivalent to the polynomial one ([Ratio.lean](GyiresEquality/Ratio.lean)).

## Relation to the original computer-assisted proof

The [original proof](original/README.md) uses the same decomposition. It covers the
Birkhoff polytope by the cones over all complete flags of faces, starting at the
center $J$, and checks 1,589,290,560 coefficients over the same 65,376 orbit
representatives with a separate C++ verifier. The Lean formalization enters the flag
tree through the minimum entry instead, which yields cones over flags through the facet
$x_{00}=0$. Since all 16 facets are equivalent under symmetry, these are the same orbit
classes.

The Lean checker does not read the original certificate. It regenerates everything
itself, so reproducing the Lean theorems requires none of the original programs.

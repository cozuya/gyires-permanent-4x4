> **Display copy.** The original write-up is preserved byte-for-byte in
> [RESULTS.original.txt](RESULTS.original.txt) (SHA-256
> `abf09678127efe3e73dce5a66d2a8ebdd42a1d3ca81b804fbdcc8fb13f596390`). This copy changes
> only math markup for GitHub's renderer, which rejects `\operatorname`: `\operatorname` becomes
> `\mathrm` (20 times), equation `\tag{n}` becomes `(n)` (9 times), and one `\boxed` is
> removed. The text is otherwise unchanged.
> Paths in section 5 refer to the original working directory.

# Result: the inequality is true

For every real doubly stochastic $4\times4$ matrix $A$,

$$
128\mathrm{per}(A)^2\ge
3\bigl[\mathrm{per}(AA^T)+\mathrm{per}(A^TA)
       +2\mathrm{per}(A^2)\bigr].
$$

Equality holds precisely when every entry of $A$ is $1/4$.

This is a computer-assisted proof using an exhaustive, exact integer coefficient certificate. The complete certificate generator and verifier are included below and are also saved as `RESULTS_certificate/generate.py` and `RESULTS_certificate/verify.cpp`. The computation checks polynomials on cones covering the entire doubly stochastic polytope, so it establishes the assertion for all admissible real matrices, including matrices with zero entries and singular matrices.

I did not recall an exact solution to this problem. No external sources, network access, or other agents were used. Exploratory numerical calculations were performed, but they are not premises of the proof.

## 1. A stronger inequality suffices

We will establish

$$
32\mathrm{per}(A)^2\ge3\mathrm{per}(AA^T) \qquad (1)
$$

for every doubly stochastic $4\times4$ matrix $A$.

For an arbitrary real $4\times4$ matrix $M$, define

$$
f_M(z)=\prod_{i=1}^4\left(\sum_{j=1}^4m_{ij}z_j\right)
      =\sum_{|\alpha|=4}f_\alpha(M)z^\alpha,
\qquad
\alpha!=\prod_{j=1}^4\alpha_j!.
$$

There are 35 multi-indices in this sum. Direct expansion gives, for arbitrary real $M,N$,

$$
\mathrm{per}(MN^T)
 =\sum_{|\alpha|=4}\alpha! f_\alpha(M)f_\alpha(N). \qquad (2)
$$

To verify the multiplicity in (2), expand the permanent and choose a column index $j_i$ in each matrix-product entry. Fix the multiplicities $\alpha$ of the four indices $j_1,\ldots,j_4$. Summing the $M$-products over these index choices gives $f_\alpha(M)$. For any one such choice, summing the $N$-products over the row permutation gives $\alpha! f_\alpha(N)$: each assignment of the columns to the four rows occurs $\alpha!$ times. This proves (2).

In particular,

$$
\mathrm{per}(M)=f_{(1,1,1,1)}(M),\qquad
\mathrm{per}(MM^T)=\sum_\alpha\alpha!f_\alpha(M)^2. \qquad (3)
$$

Set

$$
p=\mathrm{per}(A),\quad
 g=\mathrm{per}(AA^T),\quad
 h=\mathrm{per}(A^TA),\quad
 z=\mathrm{per}(A^2).
$$

Taking $M=A$, $N=A^T$ in (2) correctly gives $MN^T=A^2$. Consequently,

$$
g+h-2z
 =\sum_\alpha\alpha!\bigl(f_\alpha(A)-f_\alpha(A^T)\bigr)^2\ge0. \qquad (4)
$$

Since $A^T$ is also doubly stochastic and has permanent $p$, (1) applied to both $A$ and $A^T$ gives

$$
3(g+h)\le64p^2.
$$

Combining this with (4),

$$
3(g+h+2z)\le6(g+h)\le128p^2,
$$

which is exactly the requested inequality. It remains to prove (1).

## 2. Cones covering every doubly stochastic matrix

Write $\mathcal B$ for the $4\times4$ doubly stochastic polytope. We use the Birkhoff–von Neumann theorem in its precise finite-dimensional form: every doubly stochastic matrix is a convex combination of permutation matrices. Thus $\mathcal B$ is the convex hull of its 24 permutation matrices.

For completeness, this theorem follows from Hall's marriage theorem here. In the positive-entry support of a doubly stochastic matrix, a set $I$ of rows has at least $|I|$ neighboring columns, since

$$
|I|=\sum_{i\in I,j}a_{ij}
 \le\sum_{j\in N(I),i}a_{ij}=|N(I)|.
$$

There is therefore a supported permutation. Subtract the minimum entry along that permutation times its permutation matrix. If that minimum is less than one, rescale the remainder to be doubly stochastic and repeat. At least one positive entry disappears at each subtraction. This produces the asserted convex combination in finitely many steps.

Every nonempty face of $\mathcal B$ is specified by setting some entries to zero. Its support is the set of entries that can be positive on the face. To see that zero constraints suffice, take a relative interior point $C$ of a face and a doubly stochastic matrix $B$ supported on its positive entries. For sufficiently small $\varepsilon>0$, the matrix $D=C+\varepsilon(C-B)$ is doubly stochastic. Since $C$ lies in the open segment joining $B$ to $D$, the defining property of a face forces $B$ to belong to that face.

Encode a support by a 16-bit mask $m$, using bit $4i+j$ for entry $(i,j)$, with indices $0,1,2,3$. Let $\mathcal P(m)$ be the set of permutation matrices supported in $m$. A mask is exactly the support of a nonempty face if and only if

$$
\mathcal P(m)\ne\varnothing,
\qquad
m=\bigcup_{P\in\mathcal P(m)}\mathrm{supp}(P). \qquad (5)
$$

Indeed, averaging these permutation matrices produces a matrix positive at exactly the entries in the union. Conversely, the Birkhoff decomposition of a relative interior point of a face shows that every entry of the face support occurs in a supported permutation.

For such a face, choose its center

$$
C_m=\frac1{|\mathcal P(m)|}\sum_{P\in\mathcal P(m)}P. \qquad (6)
$$

It lies in the relative interior of its face. For integer arithmetic, let $S_m$ denote the sum in (6), let $d_m$ be the greatest common divisor of its 16 entries, and use the integer generator

$$
V_m=S_m/d_m.
$$

This is a positive scalar multiple of $C_m$. Each entry of $V_m$ is an integer between 0 and 6: a specified entry belongs to exactly $3!=6$ of the 24 permutation matrices.

A full flag is a chain

$$
F_9\supset F_8\supset\cdots\supset F_0,
\qquad \dim F_i=i,
$$

where $F_9=\mathcal B$. Every point of $\mathcal B$ is in the convex hull of the ten centers associated with some full flag. One can see this without assuming a triangulation theorem: if the point equals the chosen center, the claim is immediate. Otherwise, from the center of its positive-dimensional face, extend the ray through the point until it reaches the boundary. The boundary point belongs to a facet. Express the original point as a convex combination of the center and that boundary point, then repeat in the facet. This decreases the dimension at each step.

Therefore every doubly stochastic $A$ belongs to at least one of the cones

$$
\left\{\sum_{k=0}^9 t_kV_{m_k}:t_k\ge0\right\}, \qquad (7)
$$

where $m_0,\ldots,m_9$ are the supports in a full flag, ordered from dimension 9 down to dimension 0. Replacing centers by positive scalar multiples does not change these cones. In particular, (7) covers matrices with arbitrary real entries satisfying the doubly stochastic constraints.

## 3. The exact coefficient certificate

Define the homogeneous degree-eight polynomial

$$
H(M)=32\mathrm{per}(M)^2-3\mathrm{per}(MM^T).
$$

For each full flag, substitute

$$
M(t)=\sum_{k=0}^9t_kV_{m_k}.
$$

The certificate establishes the following finite statement:

> Every coefficient of the degree-eight polynomial $H(M(t))$ is a nonnegative integer, for every full flag.

A polynomial with nonnegative coefficients is nonnegative whenever all its variables are nonnegative. Together with the covering (7), this finite statement proves $H(A)\ge0$ for every doubly stochastic $A$, which is (1).

Here is how all flags and all coefficients are checked.

**Enumeration of faces and facets.** Enumerate all $2^{16}$ masks and retain exactly those satisfying (5). For a retained mask, let $e$ be its number of entries and $c$ the number of connected components of its bipartite row-column support graph. Its face dimension is

$$
e-8+c. \qquad (8)
$$

The row/column equations have rank $8-c$: a linear relation among these equations gives multipliers $u_i,v_j$ satisfying $u_i+v_j=0$ on every support edge, with one free multiplier per connected component. Positivity of the center on the entire support ensures that there are no additional affine constraints, proving (8).

Every facet is obtained by setting at least one allowed entry to zero. For each allowed entry, remove all permutations containing it and take the union of the surviving permutation supports. Retain the resulting face exactly when its dimension is one less. This enumerates every facet: any facet is contained in a coordinate-zero hyperplane, and intersection with that hyperplane is a proper face of dimension at least that of the facet, hence is the facet itself.

The resulting face counts, from dimension 0 to dimension 9, are

$$
(24,240,978,1968,2176,1392,528,120,16,1).
$$

There are 7,443 nonempty faces and 37,656,576 full flags.

**Symmetry reduction.** The group of independent row and column permutations has $24^2=576$ elements. It preserves $H$: if $M'=RMC^T$, then $M'M'^T=RMM^TR^T$, and the permanent is invariant under row and column permutations. It also carries each chosen integer center to the corresponding integer center of the image face.

Starting with the full group, the generator takes one facet from each orbit under the stabilizer of the current chain, then passes to the stabilizer of the chosen facet. This recursion gives one representative of every full-flag orbit. It finds 65,376 representatives. Each full flag has trivial stabilizer, checked by the generator; independently, the number of representatives times 576 equals the full-flag count above.

Thus checking the representatives checks all full flags. This symmetry acts on the stronger polynomial $H$; no invariance of $\mathrm{per}(A^2)$ under independent row/column permutations is being assumed.

**Coefficient expansion.** For each representative, expand

$$
\prod_{i=1}^4\sum_{j=1}^4\sum_{k=0}^9
 (V_{m_k})_{ij}\,z_jt_k
 =\sum_{|\alpha|=4,\,|\beta|=4}c_{\alpha,\beta}z^\alpha t^\beta.
$$

These integers are computed by multiplying the four linear factors, using the explicit recurrence implemented in the verifier. Put

$$
q_\alpha(t)=\sum_{|\beta|=4}c_{\alpha,\beta}t^\beta.
$$

By (3),

$$
H(M(t))
 =29q_{(1,1,1,1)}(t)^2
   -3\sum_{\alpha\ne(1,1,1,1)}\alpha!\,q_\alpha(t)^2. \qquad (9)
$$

The verifier expands (9) by ordinary exact convolution and checks each resulting coefficient. There are 35 indices $\alpha$, 715 degree-four monomials in the ten $t$-variables, and

$$
\binom{17}{8}=24,310
$$

degree-eight monomials. Across all 65,376 representatives, this checks exactly 1,589,290,560 coefficients.

**Integer overflow is excluded.** All generator entries are at most 6. Every intermediate coefficient in the four-factor expansion is at most

$$
(4!)^2 6^4=746,496.
$$

For the degree-eight calculation, bound the sum of absolute contributions by the coefficient in
$32\mathrm{per}(M)^2+3\mathrm{per}(MM^T)$.
The first term has $32\cdot24^2$ products of eight entries, and the second has $3\cdot24\cdot4^4$ such products. The coefficient in a product of eight linear forms is at most $8!6^8$. Consequently every coefficient and every partial accumulation is bounded in absolute value by

$$
(32\cdot24^2+3\cdot24\cdot4^4)8!6^8
 =2,496,508,125,511,680<2^{63}-1.
$$

Individual convolution multiplications also fit: their absolute value is at most $144\cdot746,496^2<2^{63}-1$. Thus the verifier's signed 64-bit integer arithmetic is exact. There is no floating-point or numerical-tolerance step in the certificate.

## 4. Equality and conclusion

The verifier additionally checks that, for every representative, the coefficient of $t_0^8$ is zero and each of the nine coefficients of $t_k^8$, $k>0$, is strictly positive. The index 0 is always the center of the full polytope, proportional to the all-ones matrix; the other centers belong to proper faces.

Consequently $H$ is strictly positive at every doubly stochastic matrix other than $J$, where $J_{ij}=1/4$. Indeed, any representation (7) of a matrix other than $J$ has at least one positive coefficient $t_k$ with $k>0$. The corresponding pure eighth-power term is positive, and every other polynomial coefficient is nonnegative. This proves strictness in (1) away from $J$, and hence strictness in the requested inequality away from $J$.

Finally,

$$
\mathrm{per}(J)=\frac{24}{4^4}=\frac3{32},
\qquad J^2=JJ^T=J^TJ=J.
$$

Both sides of the requested inequality equal $9/8$ at $J$. This proves the universal assertion, including its equality case.

## 5. Reproducing the computation

The scripts below use only Python's standard library and C++17's standard library. From the workspace directory, run:

```sh
set -e
python3 RESULTS_certificate/generate.py > /tmp/perm4-cones.txt
g++ -std=c++17 -O3 -Wall -Wextra -pedantic RESULTS_certificate/verify.cpp -o /tmp/perm4-verify
/tmp/perm4-verify < /tmp/perm4-cones.txt
```

The generator enumerates the faces and flag representatives anew. The verifier exits unsuccessfully if it finds any negative coefficient, an invalid input, or a failed strictness check. Both the exhaustive coefficient check and the checks reported below were actually executed. The recorded verifier output is also saved in `RESULTS_certificate/verification.txt`.

```text
PASS
flags: 65376
coefficients: 1589290560
zero coefficients: 653760
largest coefficient: 45478883488
All coefficients are nonnegative.
All proper-face-center pure-power coefficients are positive.
```

The first exhaustive implementation also passed all 65,376 representatives. The final standalone generator produced identical cone data, and the final standalone verifier was then run over the full dataset, producing the output above. The finite check is essential to this proof; no claim is made that checking only the face centers would suffice.

## 6. Complete certificate generator

```python
#!/usr/bin/env python3
"""Generate all full-flag representatives for the exact permanent certificate.

Only Python's standard library is used. The certificate data go to stdout;
counts go to stderr. Matrix entries are printed in row-major order.
"""
from itertools import permutations
from math import gcd
import sys

PERMS = list(permutations(range(4)))
PERM_MASKS = [sum(1 << (4*i + p[i]) for i in range(4)) for p in PERMS]
FULL = (1 << 16) - 1


def components(mask):
    adjacency = [[] for _ in range(8)]
    for i in range(4):
        for j in range(4):
            if mask & (1 << (4*i + j)):
                adjacency[i].append(4+j)
                adjacency[4+j].append(i)
    seen = set()
    count = 0
    for start in range(8):
        if start in seen:
            continue
        count += 1
        stack = [start]
        while stack:
            v = stack.pop()
            if v not in seen:
                seen.add(v)
                stack.extend(adjacency[v])
    return count


# A support is a face support exactly when it is the union of the
# permutation supports contained in it.
faces = {}
centers = {}
for mask in range(1 << 16):
    vertices = [p for p in PERM_MASKS if (p & mask) == p]
    if not vertices:
        continue
    union = 0
    for p in vertices:
        union |= p
    if union != mask:
        continue
    dimension = mask.bit_count() - 8 + components(mask)
    faces[mask] = (dimension, vertices)
    entries = [sum((p >> ij) & 1 for p in vertices) for ij in range(16)]
    divisor = 0
    for value in entries:
        divisor = gcd(divisor, value)
    centers[mask] = [value // divisor for value in entries]
    assert max(centers[mask]) <= 6

expected_face_counts = [24, 240, 978, 1968, 2176, 1392, 528, 120, 16, 1]
face_counts = [sum(d == k for d, _ in faces.values()) for k in range(10)]
assert face_counts == expected_face_counts

# Obtain every facet by setting an entry to zero and then taking the
# union of the surviving permutation supports.
facets = {}
flag_counts = {}
for mask, (dimension, vertices) in sorted(faces.items(), key=lambda kv: kv[1][0]):
    children = set()
    if dimension:
        for ij in range(16):
            if not (mask & (1 << ij)):
                continue
            child = 0
            for p in vertices:
                if not (p & (1 << ij)):
                    child |= p
            if child in faces and faces[child][0] == dimension - 1:
                children.add(child)
        assert children
        flag_counts[mask] = sum(flag_counts[child] for child in children)
    else:
        flag_counts[mask] = 1
    facets[mask] = sorted(children)
assert flag_counts[FULL] == 37656576

# The 576 independent row/column permutations act on support masks.
actions = [
    [1 << (4*r[i] + c[j]) for i in range(4) for j in range(4)]
    for r in PERMS for c in PERMS
]


def transform(mask, action):
    result = 0
    while mask:
        bit = mask & -mask
        mask -= bit
        result |= actions[action][bit.bit_length() - 1]
    return result


# At each step take facet orbits under the stabilizer of the preceding
# chain. This gives one representative of every full-flag orbit.
flags = []


def visit(chain, stabilizer):
    if len(chain) == 10:
        assert len(stabilizer) == 1
        flags.append(chain)
        return
    children = set(facets[chain[-1]])
    done = set()
    for child in sorted(children):
        if child in done:
            continue
        orbit = {transform(child, g) for g in stabilizer}
        assert orbit <= children
        done.update(orbit)
        child_stabilizer = [g for g in stabilizer if transform(child, g) == child]
        visit(chain + [child], child_stabilizer)
    assert done == children


visit([FULL], list(range(576)))
assert len(flags) == 65376
assert len(flags) * 576 == flag_counts[FULL]
print("faces by dimension:", face_counts, file=sys.stderr)
print("maximal flags:", flag_counts[FULL], file=sys.stderr)
print("representatives:", len(flags), file=sys.stderr)
print(len(flags))
for flag in flags:
    print(" ".join(str(x) for mask in flag for x in centers[mask]))
```

## 7. Complete exact coefficient verifier

```cpp
// Exact coefficient verifier for 32 per(A)^2 - 3 per(A A^T).
// Input: the output of generate.py. No floating-point arithmetic is used.
#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdio>
#include <limits>
#include <unordered_map>
#include <vector>

using Int = std::int64_t;
using Code = std::uint64_t;
static_assert(std::numeric_limits<Int>::digits >= 63);

// A composition is encoded in hexadecimal digits: each component < 16.
void compositions_rec(int n, int degree, int position, Code code,
                      std::vector<Code>& result) {
    if (position == n - 1) {
        result.push_back(code | (Code(degree) << (4 * position)));
        return;
    }
    for (int k = 0; k <= degree; ++k)
        compositions_rec(n, degree - k, position + 1,
                         code | (Code(k) << (4 * position)), result);
}

std::vector<Code> compositions(int n, int degree) {
    std::vector<Code> result;
    compositions_rec(n, degree, 0, 0, result);
    return result;
}

int main() {
    // Alpha indexes monomials in four z variables; beta indexes
    // monomials in the ten nonnegative cone coordinates t.
    std::array<std::vector<Code>, 5> alpha, beta;
    std::array<std::unordered_map<Code, int>, 5> alpha_index, beta_index;
    for (int d = 0; d <= 4; ++d) {
        alpha[d] = compositions(4, d);
        beta[d] = compositions(10, d);
        for (int i = 0; i < int(alpha[d].size()); ++i)
            alpha_index[d][alpha[d][i]] = i;
        for (int i = 0; i < int(beta[d].size()); ++i)
            beta_index[d][beta[d][i]] = i;
    }

    std::array<std::vector<std::array<int, 4>>, 4> alpha_next;
    std::array<std::vector<std::array<int, 10>>, 4> beta_next;
    for (int d = 0; d < 4; ++d) {
        alpha_next[d].resize(alpha[d].size());
        beta_next[d].resize(beta[d].size());
        for (int a = 0; a < int(alpha[d].size()); ++a)
            for (int j = 0; j < 4; ++j)
                alpha_next[d][a][j] =
                    alpha_index[d + 1].at(alpha[d][a] + (Code(1) << (4*j)));
        for (int b = 0; b < int(beta[d].size()); ++b)
            for (int k = 0; k < 10; ++k)
                beta_next[d][b][k] =
                    beta_index[d + 1].at(beta[d][b] + (Code(1) << (4*k)));
    }

    const auto degree_eight = compositions(10, 8);
    std::unordered_map<Code, int> eight_index;
    for (int i = 0; i < int(degree_eight.size()); ++i)
        eight_index[degree_eight[i]] = i;
    const int na = int(alpha[4].size());
    const int nb = int(beta[4].size());
    const int central = alpha_index[4].at(0x1111);
    if (na != 35 || nb != 715 || degree_eight.size() != 24310)
        return 2;

    std::vector<std::array<int, 3>> products;
    for (int i = 0; i < nb; ++i)
        for (int j = i; j < nb; ++j)
            products.push_back({i, j, eight_index.at(beta[4][i] + beta[4][j])});

    const int factorial[] = {1, 1, 2, 6, 24};
    std::vector<int> alpha_factorial(na, 1);
    for (int a = 0; a < na; ++a)
        for (int j = 0; j < 4; ++j)
            alpha_factorial[a] *= factorial[(alpha[4][a] >> (4*j)) & 15];

    int number_of_flags;
    if (std::scanf("%d", &number_of_flags) != 1 || number_of_flags != 65376)
        return 2;
    std::uint64_t checked = 0;
    std::uint64_t zeros = 0;
    Int largest = 0;

    for (int flag = 0; flag < number_of_flags; ++flag) {
        int generators[10][4][4];
        for (int k = 0; k < 10; ++k)
            for (int i = 0; i < 4; ++i)
                for (int j = 0; j < 4; ++j) {
                    int& value = generators[k][i][j];
                    if (std::scanf("%d", &value) != 1 || value < 0 || value > 6)
                        return 2;
                }

        // Expand product_i sum_{j,k} generators[k][i][j] z_j t_k.
        // The final array contains every coefficient f_{alpha,beta}.
        std::vector<Int> coefficients(1, 1);
        for (int d = 0; d < 4; ++d) {
            const int old_na = int(alpha[d].size());
            const int old_nb = int(beta[d].size());
            const int new_nb = int(beta[d + 1].size());
            std::vector<Int> next(alpha[d + 1].size() * new_nb, 0);
            for (int a = 0; a < old_na; ++a)
                for (int b = 0; b < old_nb; ++b) {
                    const Int value = coefficients[a*old_nb + b];
                    if (!value) continue;
                    for (int j = 0; j < 4; ++j) {
                        Int* destination = &next[alpha_next[d][a][j] * new_nb];
                        for (int k = 0; k < 10; ++k)
                            destination[beta_next[d][b][k]] +=
                                value * generators[k][d][j];
                    }
                }
            coefficients.swap(next);
        }

        // per(A A^T) = sum_alpha alpha! f_alpha(A)^2.
        // The central alpha has coefficient 32 - 3 = 29; the others
        // have coefficient -3 alpha! in the polynomial being certified.
        std::vector<Int> result(degree_eight.size(), 0);
        for (int a = 0; a < na; ++a) {
            const Int factor = a == central ? 29 : -3 * alpha_factorial[a];
            const Int* f = &coefficients[a*nb];
            for (auto pair : products) {
                const Int multiplier = pair[0] == pair[1] ? factor : 2*factor;
                result[pair[2]] += multiplier * f[pair[0]] * f[pair[1]];
            }
        }

        for (int i = 0; i < int(result.size()); ++i) {
            if (result[i] < 0) {
                std::printf("FAIL flag=%d coefficient=%lld exponents=", flag,
                            static_cast<long long>(result[i]));
                for (int k = 0; k < 10; ++k)
                    std::printf(" %d", int((degree_eight[i] >> (4*k)) & 15));
                std::puts("");
                return 1;
            }
            ++checked;
            zeros += result[i] == 0;
            largest = std::max(largest, result[i]);
        }

        // Also check strict positivity at every proper-face center.
        if (result[eight_index.at(Code(8))] != 0) return 3;
        for (int k = 1; k < 10; ++k)
            if (result[eight_index.at(Code(8) << (4*k))] <= 0) return 3;

        if ((flag + 1) % 10000 == 0)
            std::fprintf(stderr, "checked %d / %d flags\n", flag + 1, number_of_flags);
    }

    // Reject extra non-whitespace input.
    char extra;
    if (std::scanf(" %c", &extra) == 1) return 2;
    std::printf("PASS\nflags: %d\ncoefficients: %llu\nzero coefficients: %llu\n",
                number_of_flags, static_cast<unsigned long long>(checked),
                static_cast<unsigned long long>(zeros));
    std::printf("largest coefficient: %lld\n", static_cast<long long>(largest));
    std::puts("All coefficients are nonnegative.");
    std::puts("All proper-face-center pure-power coefficients are positive.");
    return 0;
}
```

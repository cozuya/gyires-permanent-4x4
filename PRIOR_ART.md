# Prior art

## Origin and statement

B. Gyires, *On permanent inequalities*, in *Combinatorics* (Proc. Fifth Hungarian
Colloquium, Keszthely, 1976), Colloq. Math. Soc. János Bolyai **18**, North-Holland, 1978,
pp. 471–484 ([zbMATH 0398.15007](https://zbmath.org/3618267)), is the bibliographic origin of
the conjecture. The original article was **not accessed** for this review.

G.-S. Cheon and I. M. Wanless, *An update on Minc's survey of open problems involving
permanents*, Linear Algebra Appl. **403** (2005) 314–342,
DOI [10.1016/j.laa.2005.02.030](https://doi.org/10.1016/j.laa.2005.02.030)
([author's PDF](https://users.monash.edu.au/~iwanless/papers/permsurveyLAA.pdf)), state it as
**Conjecture 20 (Gyires)**:

```math
\frac{4\mathrm{per}(A)^2}{\mathrm{per}(AA^{*})+\mathrm{per}(A^{*}A)+2\mathrm{per}(A^{2})}\ \ge\ \frac{n!}{n^{n}},\qquad A\in\Omega_n,
```

with equality precisely at $J_n$. Here $\Omega_n$ is the set of $n\times n$ doubly
stochastic matrices and products are ordinary matrix products. For real $A$,
$A^{*}=A^{T}$, and for $n=4$ this is the theorem proved in this repository. The Lean
formalization includes this exact ratio form, its equality case, and the positivity of the
denominator ([Ratio.lean](GyiresEquality/Ratio.lean)).

Cheon and Wanless continue Minc's numbering of conjectures in practice. They do not say so
explicitly, but Yair Lavi's Minc's-list project states that its numbering "follows Minc's
catalogue as retained by Cheon and Wanless". Lavi's Conjecture 20 page describes it as
Conjecture 20 in Minc's 1978 book *Permanents* (Encyclopedia Math. Appl. 6,
Addison-Wesley). The book was not consulted here, so that placement is reported, not
verified.

## Known progress

- **$n\le 3$.** D. K. Chang, *On two permanental conjectures*, Linear Multilinear Algebra
  **26** (1990) 207–213, DOI [10.1080/03081089008817977](https://doi.org/10.1080/03081089008817977).
  The publisher's abstract says Gyires' conjecture is proved for $n=3$. The full text was
  not accessed. Lavi notes that Chang's results do not include the equality clause.
- **Near $J_n$.** Cheon–Wanless report Chang's sufficient condition
  $\min_{i,j}a_{ij}\ge (n-2)/(n-1)^2$. For $n=4$ this requires every entry to be at least $2/9$.
- **Boundary of $\Omega_4$ (announced).** [Yair Lavi's Conjecture 20 page](https://yair-lavi.com/mincs-list/conjecture-20/index.html),
  part of a project on Minc's list whose [index](https://yair-lavi.com/mincs-list/index.html)
  is dated October 12, 2026, lists the conjecture as **open**. It announces that every
  $A\in\Omega_4$ with a zero entry satisfies the inequality strictly, together with results
  near $J_n$ and for special families. No proof was linked at the time of checking
  (October 19, 2026).

The boundary does not determine the interior: a degree-8 polynomial can be positive at
$J_4$ and on the boundary yet negative in between. This repository's theorem covers all
of $\Omega_4$.

## Nearby recent work, not covering this statement

- IneqAgent ([arXiv:2610.20681](https://arxiv.org/abs/2610.20681), October 2026) reports
  formally verified results for other permanent conjectures in dimension four, including
  Dittert-type inequalities. Their statements do not imply Gyires' inequality.
- A proof of Dittert's conjecture for $n=4$ with a Lean-verified sum-of-squares certificate
  ([arXiv:2607.29191](https://arxiv.org/abs/2607.29191)) concerns a different conjecture on
  the same list.
- A MathOverflow example ([question 422029](https://mathoverflow.net/questions/422029/on-permanent-of-a-square-of-a-doubly-stochastic-matrix))
  shows $\mathrm{per}(A^2)>\mathrm{per}(A)$ can occur for symmetric doubly
  stochastic $A$. So the shortcut $\mathrm{per}(A^2)\le\mathrm{per}(A)$ is not
  available, although that example satisfies Gyires' inequality.
- Searches of public formal-mathematics collections (Google DeepMind's
  formal-conjectures, OpenAI's mathematics release, the-omega-institute repository) found
  related permanent statements but no formalization of this one.

## Novelty statement

An AI-assisted literature review (October 16, 2026), with a bounded update on October 19,
2026, located **no earlier unrestricted proof of the 4×4 case** in the sources examined.
This is only a finding about the sources checked, **not a claim of novelty, first
discovery, historical priority, or an official change to any conjecture listing**.
The purpose of this repository is to provide a checkable proof for researchers
investigating this case.

What was already known or conjectured, and is not claimed here:

- the inequality and its equality clause, conjectured by Gyires;
- the $n\le 3$ cases;
- the general methods: Birkhoff decomposition, subdivision into cones, symmetry
  reduction, nonnegative-coefficient certificates, and exact polynomial arithmetic.

**Results provided in this repository:** a complete proof for $n=4$ with its equality case; the stronger
inequality $3\mathrm{per}(AA^T)\le32\mathrm{per}(A)^2$ on $\Omega_4$; and a Lean
formalization of all of these, under the trust model described in the [README](README.md).

## Access limitations

- Gyires' 1978 article and Chang's 1990 full text were not read.
- Minc's 1978 book was not consulted.
- The 2005 survey statement was checked against the author's PDF and against a 2008
  thesis transcription (L. I. Troanca, University of Manitoba, Conjecture 20, p. 34).
- Lavi's boundary result is an announcement; no manuscript was examined.

// Independent re-check of the leaf test, outside Lean.
//
// For every leaf cone written by tree.py (ten 4x4 generator matrices g_0..g_9), form
// M = sum_k t_k g_k and compute, as polynomials in t with exact unsigned 128-bit
// coefficients, P = C * per(M)^2 and Q = 3 * per(M M^T) (C = 32 by default). It reports:
//   - leaves where some coefficient has P < Q (must be 0 for C = 32);
//   - leaves whose tight set (P == Q) is not exactly {t0^8, t0^7 t_k : k = 1..9};
//   - leaves where a pure power t_k^8, k >= 1, is not strict (P > Q);
//   - the minimum ratio P/Q over non-tight coefficients and the largest coefficient;
//   - a self-test comparing polynomial values with directly computed permanents.
// Run with C = 31 as a negative control: every leaf must then fail.
//
// Build: g++ -O2 -fopenmp -o leafcheck leafcheck.cpp
// Usage: ./leafcheck DATA_DIR [C]
#include <algorithm>
#include <atomic>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <vector>
#include <omp.h>

typedef unsigned __int128 u128;
static const int N1 = 10, N2 = 55, N4 = 715, N8 = 24310, NLEAF = 65376;
static const u128 LIMIT = ((u128)1) << 120;
static std::vector<int> T11, T22, T44;
static std::vector<uint8_t> L;
static std::atomic<int> overflow{0};

static void load(const char* dir, const char* name, void* p, size_t n) {
  char path[4096];
  snprintf(path, sizeof path, "%s/%s", dir, name);
  FILE* f = fopen(path, "rb");
  if (!f || fread(p, 1, n, f) != n) { fprintf(stderr, "cannot read %s\n", path); exit(2); }
  fclose(f);
}

// r = p * q using the monomial table T (index x*nb+y -> index of the product monomial).
static void pmul(const int* T, int na, int nb, int nc, const u128* p, const u128* q, u128* r) {
  std::fill(r, r + nc, (u128)0);
  for (int x = 0; x < na; ++x) {
    if (!p[x]) continue;
    for (int y = 0; y < nb; ++y) {
      if (!q[y]) continue;
      u128 v = r[T[x * nb + y]] + p[x] * q[y];
      if (v > LIMIT) overflow = 1;
      r[T[x * nb + y]] = v;
    }
  }
}

// 4x4 permanent by Laplace expansion along rows {0,1} versus {2,3}.
template <class F>
static void laplace(F X, const int* Ta, int na, int nb, const int* Tb, int nc, u128* out) {
  static const int quads[6][4] = {{0,1,2,3},{0,2,1,3},{0,3,1,2},{1,2,0,3},{1,3,0,2},{2,3,0,1}};
  std::vector<u128> a(nb), b(nb), c(nb), d(nb), prod(nc);
  std::fill(out, out + nc, (u128)0);
  for (auto& qd : quads) {
    auto p2 = [&](int r1, int r2, int c1, int c2, u128* dst) {
      pmul(Ta, na, na, nb, X(r1, c1), X(r2, c2), a.data());
      pmul(Ta, na, na, nb, X(r1, c2), X(r2, c1), b.data());
      for (int i = 0; i < nb; ++i) dst[i] = a[i] + b[i];
    };
    p2(0, 1, qd[0], qd[1], c.data());
    p2(2, 3, qd[2], qd[3], d.data());
    pmul(Tb, nb, nb, nc, c.data(), d.data(), prod.data());
    for (int i = 0; i < nc; ++i) out[i] += prod[i];
  }
}

static u128 per4(const u128 M[16]) {
  int p[4] = {0, 1, 2, 3};
  u128 s = 0;
  do s += M[p[0]] * M[4 + p[1]] * M[8 + p[2]] * M[12 + p[3]];
  while (std::next_permutation(p, p + 4));
  return s;
}

int main(int argc, char** argv) {
  if (argc < 2) { fprintf(stderr, "usage: %s DATA_DIR [C]\n", argv[0]); return 2; }
  const char* dir = argv[1];
  const u128 C = argc > 2 ? (u128)atoi(argv[2]) : 32;
  T11.resize(N1 * N1); T22.resize(N2 * N2); T44.resize(N4 * N4); L.resize((size_t)NLEAF * 160);
  load(dir, "T11.bin", T11.data(), T11.size() * 4);
  load(dir, "T22.bin", T22.data(), T22.size() * 4);
  load(dir, "T44.bin", T44.data(), T44.size() * 4);
  load(dir, "leaves.bin", L.data(), L.size());
  // E8 indices of the pure powers t_k^8 (tree.py checks the table layout).
  std::vector<int> pure(N1);
  {
    std::vector<int> e2(N1), e4(N1);
    for (int k = 0; k < N1; ++k) e2[k] = T11[k * N1 + k];
    for (int k = 0; k < N1; ++k) e4[k] = T22[e2[k] * N2 + e2[k]];
    for (int k = 0; k < N1; ++k) pure[k] = T44[e4[k] * N4 + e4[k]];
  }
  std::atomic<long> failing{0}, tight_mismatch{0}, pure_not_strict{0}, selftest_fail{0}, done{0};
  long double min_ratio = 1e30L;
  u128 max_coeff = 0;
  #pragma omp parallel
  {
    std::vector<u128> lin(16 * N1), gram(16 * N2), per(N4), pg(N8), psq(N8), t1(N2);
    #pragma omp for schedule(dynamic, 16)
    for (int li = 0; li < NLEAF; ++li) {
      const uint8_t* g = &L[(size_t)li * 160];
      for (int e = 0; e < 16; ++e)
        for (int k = 0; k < N1; ++k) lin[e * N1 + k] = g[k * 16 + e];
      auto LX = [&](int i, int j) { return &lin[(4 * i + j) * N1]; };
      for (int i = 0; i < 4; ++i)
        for (int j = 0; j < 4; ++j) {
          u128* G = &gram[(4 * i + j) * N2];
          std::fill(G, G + N2, (u128)0);
          for (int l = 0; l < 4; ++l) {
            pmul(T11.data(), N1, N1, N2, LX(i, l), LX(j, l), t1.data());
            for (int z = 0; z < N2; ++z) G[z] += t1[z];
          }
        }
      auto GX = [&](int i, int j) { return &gram[(4 * i + j) * N2]; };
      laplace(LX, T11.data(), N1, N2, T22.data(), N4, per.data());
      laplace(GX, T22.data(), N2, N4, T44.data(), N8, pg.data());
      pmul(T44.data(), N4, N4, N8, per.data(), per.data(), psq.data());
      bool ok = true;
      long tight = 0;
      long double lmin = 1e30L;
      u128 lmax = 0;
      for (int i = 0; i < N8; ++i) {
        u128 P = C * psq[i], Q = 3 * pg[i];
        lmax = std::max(lmax, std::max(P, Q));
        if (P < Q) ok = false;
        if (P == Q) ++tight;
        else if (Q > 0) lmin = std::min(lmin, (long double)P / (long double)Q);
      }
      bool tight_ok = tight == N1;
      for (int i = 0; i < N1; ++i) tight_ok = tight_ok && C * psq[i] == 3 * pg[i];
      bool pure_ok = true;
      for (int k = 1; k < N1; ++k) pure_ok = pure_ok && C * psq[pure[k]] > 3 * pg[pure[k]];
      if (!ok) ++failing;
      if (!tight_ok) ++tight_mismatch;
      if (!pure_ok) ++pure_not_strict;
      #pragma omp critical
      {
        min_ratio = std::min(min_ratio, lmin);
        max_coeff = std::max(max_coeff, lmax);
      }
      if (li % 997 == 0) {  // self-test at t_k = 1 + (k mod 3)
        u128 tv[N1], M[16], MMt[16];
        for (int k = 0; k < N1; ++k) tv[k] = 1 + (k % 3);
        for (int e = 0; e < 16; ++e) {
          M[e] = 0;
          for (int k = 0; k < N1; ++k) M[e] += tv[k] * g[k * 16 + e];
        }
        for (int i = 0; i < 4; ++i)
          for (int j = 0; j < 4; ++j) {
            MMt[4 * i + j] = 0;
            for (int l = 0; l < 4; ++l) MMt[4 * i + j] += M[4 * i + l] * M[4 * j + l];
          }
        std::vector<u128> v1(N1), v2(N2), v4(N4), v8(N8);
        for (int x = 0; x < N1; ++x) v1[x] = tv[x];
        for (int x = 0; x < N1; ++x) for (int y = 0; y < N1; ++y) v2[T11[x * N1 + y]] = v1[x] * v1[y];
        for (int x = 0; x < N2; ++x) for (int y = 0; y < N2; ++y) v4[T22[x * N2 + y]] = v2[x] * v2[y];
        for (int x = 0; x < N4; ++x) for (int y = 0; y < N4; ++y) v8[T44[x * N4 + y]] = v4[x] * v4[y];
        u128 ePer = 0, ePg = 0, ePsq = 0;
        for (int i = 0; i < N4; ++i) ePer += per[i] * v4[i];
        for (int i = 0; i < N8; ++i) { ePg += pg[i] * v8[i]; ePsq += psq[i] * v8[i]; }
        u128 dPer = per4(M);
        if (ePer != dPer || ePg != per4(MMt) || ePsq != dPer * dPer) ++selftest_fail;
      }
      ++done;
    }
  }
  int bits = 0;
  for (u128 v = max_coeff; v; v >>= 1) ++bits;
  printf("constant C = %d, threads = %d\n", (int)C, omp_get_max_threads());
  printf("leaf cones checked: %ld\n", done.load());
  printf("leaves with a negative coefficient (C*per^2 < 3*perGram): %ld\n", failing.load());
  printf("leaves whose tight set is not {t0^8, t0^7*t_k}: %ld\n", tight_mismatch.load());
  printf("leaves with a non-strict pure power t_k^8 (k >= 1): %ld\n", pure_not_strict.load());
  printf("minimum ratio over non-tight coefficients: %.9Lf\n", min_ratio);
  printf("largest coefficient: %.6Le (%d bits)\n", (long double)max_coeff, bits);
  printf("self-test failures: %ld, overflow guard tripped: %d\n", selftest_fail.load(), overflow.load());
  bool pass = failing == 0 && tight_mismatch == 0 && pure_not_strict == 0 && selftest_fail == 0 &&
              !overflow && done == NLEAF;
  printf("RESULT: %s\n", pass ? "PASS" : "FAIL");
  return pass ? 0 : 1;
}

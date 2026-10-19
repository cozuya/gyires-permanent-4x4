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

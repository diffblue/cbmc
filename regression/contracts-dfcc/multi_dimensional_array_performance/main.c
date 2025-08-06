#include <stdint.h>

#define __contract__(x) x
#define __loop__(x) x

/* https://diffblue.github.io/cbmc/contracts-assigns.html */
#define assigns(...) __CPROVER_assigns(__VA_ARGS__)

/* https://diffblue.github.io/cbmc/contracts-requires-ensures.html */
#define requires(...) __CPROVER_requires(__VA_ARGS__)
#define ensures(...) __CPROVER_ensures(__VA_ARGS__)
/* https://diffblue.github.io/cbmc/contracts-loops.html */
#define invariant(...) __CPROVER_loop_invariant(__VA_ARGS__)

#define memory_slice(...) __CPROVER_object_upto(__VA_ARGS__)
#define memory_no_alias(...) __CPROVER_is_fresh(__VA_ARGS__)

/*
 * Prevent clang-format from corrupting CBMC's special ==> operator
 */
/* clang-format off */
#define forall(qvar, qvar_lb, qvar_ub, predicate)                 \
  __CPROVER_forall                                                \
  {                                                               \
    unsigned qvar;                                                \
    ((qvar_lb) <= (qvar) && (qvar) < (qvar_ub)) ==> (predicate)   \
  }

/* clang-format on */

/*
 * Prevent clang-format from corrupting CBMC's special ==> operator
 */
/* clang-format off */
#define CBMC_CONCAT_(left, right) left##right
#define CBMC_CONCAT(left, right) CBMC_CONCAT_(left, right)

#define array_bound_core(qvar, qvar_lb, qvar_ub, array_var,            \
                         value_lb, value_ub)                           \
  __CPROVER_forall                                                     \
  {                                                                    \
    unsigned qvar;                                                     \
    ((qvar_lb) <= (qvar) && (qvar) < (qvar_ub)) ==>                    \
        (((int)(value_lb) <= ((array_var)[(qvar)])) &&		       \
         (((array_var)[(qvar)]) < (int)(value_ub)))		       \
  }

#define array_bound(array_var, qvar_lb, qvar_ub, value_lb, value_ub) \
  array_bound_core(CBMC_CONCAT(_cbmc_idx, __LINE__), (qvar_lb),      \
      (qvar_ub), (array_var), (value_lb), (value_ub))
/* clang-format on */

#define MLDSA_K 2
#define MLDSA_L 1
#define MLDSA_N 16
#define MLDSA_Q 8380417

typedef struct
{
  int32_t coeffs[MLDSA_N];
} mld_poly;

typedef struct
{
  mld_poly vec[MLDSA_L];
} mld_polyvecl;

typedef struct
{
  mld_polyvecl vec[MLDSA_K];
} mld_polymat;

/* clang-format off */
void mld_poly_permute_bitrev_to_custom(int32_t p[MLDSA_N])
__contract__(
  requires(memory_no_alias(p, sizeof(int32_t) * MLDSA_N))
  requires(array_bound(p, 0, MLDSA_N, 0, MLDSA_Q))
  assigns(memory_slice(p, sizeof(int32_t) * MLDSA_N))
  ensures(array_bound(p, 0, MLDSA_N, 0, MLDSA_Q))
);

void mld_polymat_permute_bitrev_to_custom(mld_polymat *mat)
__contract__(
  requires(memory_no_alias(mat, sizeof(mld_polymat)))
  requires(forall(k1, 0, MLDSA_K, forall(l1, 0, MLDSA_L,
    array_bound(mat->vec[k1].vec[l1].coeffs, 0, MLDSA_N, 0, MLDSA_Q))))
  assigns(memory_slice(mat, sizeof(mld_polymat)))
  ensures(forall(k1, 0, MLDSA_K, forall(l1, 0, MLDSA_L,
    array_bound(mat->vec[k1].vec[l1].coeffs, 0, MLDSA_N, 0, MLDSA_Q))))
);

void mld_polymat_permute_bitrev_to_custom(mld_polymat *mat)
{
  unsigned int i, j;
  for (i = 0; i < MLDSA_K; i++)
  __loop__(
    assigns(i, j, memory_slice(mat, sizeof(mld_polymat)))
    invariant(i <= MLDSA_K)
    invariant(forall(k1, 0, MLDSA_K, forall(l1, 0, MLDSA_L,
      array_bound(mat->vec[k1].vec[l1].coeffs, 0, MLDSA_N, 0, MLDSA_Q))))
  )
  {
    for (j = 0; j < MLDSA_L; j++)
    __loop__(
      assigns(j, memory_slice(mat, sizeof(mld_polymat)))
      invariant(i <= MLDSA_K)
      invariant(j <= MLDSA_L)
      invariant(forall(k2, 0, MLDSA_K, forall(l2, 0, MLDSA_L,
        array_bound(mat->vec[k2].vec[l2].coeffs, 0, MLDSA_N, 0, MLDSA_Q))))
    )
    {
      mld_poly_permute_bitrev_to_custom(mat->vec[i].vec[j].coeffs);
    }
  }
}
/* clang-format on */

int main()
{
  mld_polymat *m;
  mld_polymat_permute_bitrev_to_custom(m);
}

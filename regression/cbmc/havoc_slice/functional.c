#include <stdint.h>
#include <stdlib.h>

/*

When translating to SMT, structs are represented by algebraic datatypes (ADTs)
and arrays of structs by arrays of ADTs.

When forming a pointer ranging over an array of struct using a nondeterministic
index, the pointer offset appears completely non-deterministic to CBMC, and
in-place updates made using assignments or __CPROVER_array_replace then expand
into large sequences of byte_updates ranging over the whole array.

If we could somehow track the fact that a pointer formed using arr[i] is still
aligned on array cell boundaries, i.e. is of the form i*sizeof(T) where T is the
type of the array, across intermediate variables and assignments then we would
be able to encode these cases in SMT more optimally:

T arr[N];
size_t i = nondetd_size_t();
if (i < N) {
  T *ai = &arr[i];
  T v =  nondet_T();
  *ai = v;
  // here we have ai of the form &a[0] + i*sizeof(T) assigned with a value of
size sizeof(T)
  // can be modeled as a functional array update at index i.
}

size_t k = nondet_size_t();
if (k < N) {
  size_t S = N-k;
  T nondet[S];
  T *ak = &a[k];
  __CPROVER_array_replace(ak, nondet);
  // here we have ai of the form &a[0] + k*sizeof(T) updated in place with a
value of size k*sizeof(T)
  // can be modeled as a functional slice update at index k with k elements.
}

At the moment these constructs blow up with --z3 and --bitwuzla
*/

// #define N 4 // use 8, 16, ... to see the blowup
#define K 4

typedef struct
{
  int32_t coeffs[N];
} vec_N;

typedef struct
{
  vec_N vec[K];
} vec_K_N;

unsigned int __VERIFIER_nondet_unsigned_int();
vec_N __VERIFIER_nondet_vec_N();

int main(void)
{
  vec_K_N *v = malloc(sizeof(vec_K_N));
  __CPROVER_assume(v);

  unsigned int i = __VERIFIER_nondet_unsigned_int();

  // models a nondet loop step from an arbitrary state
  if(i < K)
  {
#ifdef ASSIGN_DIRECT
    // nondet assignment without indirection through a
    // simplifies to a functional update
    v->vec[i] = __VERIFIER_nondet_vec_N();
#endif

    // simulates how symex models argument passing for a function call
    vec_N *__arg = &v->vec[i];
    vec_N *a = __arg;

#ifdef ASSIGN
    // nondet assignment with indirection through a
    // currently does NOT simplifies to a functional update but ultimately
    // should
    *a = __VERIFIER_nondet_vec_N();
#endif

#ifdef SLICE_BYTES
    // Modeled as a byte slice operation without indirection
    // does NOT simplify to a functional array update due to lack of pattern
    // matching on the pointer offset expression.
    // We could realize the pointer offset is of the form i*16 and that the
    // new value is of size 16 too but we currently don't.
    char nondet[sizeof(vec_N)];
    __CPROVER_array_replace((char *)a, nondet);
#endif

#ifdef SLICE_TYPED
    // Modeled as a typed slice operation without indirection.
    // Does NOT simplify to a functional array update due to lack of pattern
    // matching on the pointer offset expression and types.
    // We could realize the pointer offset is of the form i*16 and that the
    // new value is of size 16 too but we currently don't.
    vec_N nondet[1];
    __CPROVER_array_replace(a, nondet);
#endif
    __CPROVER_assert(a->coeffs[0] > 0, "expected to fail");
  }
  return 0;
}

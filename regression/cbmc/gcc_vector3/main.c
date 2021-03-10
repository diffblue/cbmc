#include <assert.h>

#ifdef __GNUC__
typedef int v4si __attribute__((vector_size(16)));

typedef union {
  v4si v;
  int members[4];
} vector_u;
#endif

int main()
{
#if defined(__GNUC__) && !defined(__clang__)
  // https://gcc.gnu.org/onlinedocs/gcc/Vector-Extensions.html
  v4si a = {1, 2, 3, 4};
  v4si b = {5, 6, 7, 8};
  v4si mask1 = {0, 1, 5, 3};
  v4si mask2 = {0, 4, 2, 5};

  vector_u res;

  res.v = __builtin_shuffle(a, mask1);
  assert(res.members[0] == 1);
  assert(res.members[1] == 2);
  assert(res.members[2] == 2);
  assert(res.members[3] == 4);

  res.v = __builtin_shuffle(a, b, mask2);
  assert(res.members[0] == 1);
  assert(res.members[1] == 5);
  assert(res.members[2] == 3);
  assert(res.members[3] == 6);
#elif defined(__clang__)
  v4si a = {1, 2, 3, 4};
  v4si b = {5, 6, 7, 8};

  vector_u res;

  res.v = __builtin_shufflevector(a, a, 0, 1, -1, 3);
  assert(res.members[0] == 1);
  assert(res.members[1] == 2);
  // res.members[2] is "don't care"
  assert(res.members[3] == 4);

  res.v = __builtin_shufflevector(a, b, 0, 4, 2, 5);
  assert(res.members[0] == 1);
  assert(res.members[1] == 5);
  assert(res.members[2] == 3);
  assert(res.members[3] == 6);
#endif
}

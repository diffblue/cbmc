#include <assert.h>

#define SIZE 1

struct s
{
  char a1[1];
  unsigned int a2_len;
  char a2[SIZE];
};

void main()
{
  struct s s1;
  char buf[SIZE];

  __CPROVER_assume(s1.a2_len <= SIZE);
  __CPROVER_assume(s1.a2_len >= SIZE);
  char src_n[s1.a2_len];
  __CPROVER_array_copy(src_n, s1.a2);
  assert(src_n[0] == s1.a2[0]);
}

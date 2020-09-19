#include <assert.h>
#include <stdbool.h>
#include <stdlib.h>

#define MAX_LEN 100

// Compares if two arrays are the same (sort of)
bool foo(char *a1, size_t a1_len, char *a2, size_t a2_len)
{
  bool res = true;
  if(a1_len == a2_len)
  {
    for(size_t i = 0; i < a1_len; i++)
    {
      if(a2[i] != a1[i])
        res &= false;
    }
    return res;
  }
  else
  {
    return false;
  }
}

void main()
{
  const char *a1;
  const char *a2;
  size_t a1_len;
  size_t a2_len;
  // CBMC will choose i non-deterministically
  size_t i;

  __CPROVER_assume(a1_len < MAX_LEN);
  __CPROVER_assume(a2_len <= a1_len);
  __CPROVER_assume(i < a2_len);

  a1 = malloc(a1_len);
  a2 = malloc(a2_len);

  if(foo(a1, a1_len, a2, a2_len))
    assert(a1[i] == a2[i]);
  else
    assert(true);
  return;
}
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

bool search(char *a, size_t a_len, char key)
{
  bool res = false;
  for(size_t i = 0; i < a_len; i++)
  {
    if(a[i] == key)
      res = true;
  }
  return res;
}

void copy(char **a1, char **a2)
{
  *a1 = *a2;
  return;
}

bool main()
{
  char *a1;
  char *a2;
  size_t a1_len;
  size_t a2_len;
  // Some char
  char key = 'a';
  // CBMC will choose i non-deterministically
  size_t i;

  __CPROVER_assume(a1_len < MAX_LEN);
  __CPROVER_assume(a2_len <= a1_len);
  __CPROVER_assume(i < a2_len);

  a2 = malloc(a2_len);
  // a2_len is identified as abstract in the spec but a1_len is not.
  // So in the abstracted program a1_len will get the original a2_len, not abst(a2_len)
  a1_len = a2_len;

  // assignment of the full array.
  // a2's spec has to be copied over for a1 as well.
  copy(&a1, &a2);

  // If a2's spec is not transferred to a1, then the search should result in out of bounds access.
  // If a2's spec is transferred then inside search a1_len
  // will get abstracted and there will be no out of bounds.
  bool res = search(a1, a1_len, key);
  return res;
}

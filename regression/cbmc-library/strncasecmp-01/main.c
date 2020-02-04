#include <assert.h>
#include <string.h>

int main()
{
#ifdef _WIN32
  // strncasecmp is a POSIX call not available on Windows
  // Can cbmc-library regression be configured to just skip this test
  // on Windows?
#else
  char a[] = "abc";
  char b[] = "xyz";
  char A[] = "ABC";
  char B[] = "XYZ";
  assert(strncasecmp(a, b, 0) == 0);
  assert(strncasecmp(A, B, 0) == 0);
  assert(strncasecmp(A, b, 0) == 0);
  assert(strncasecmp(A, b, 2) == -1);
  assert(strncasecmp(B, a, 2) == 1);
#endif
  return 0;
}

#include <assert.h>
#include <ctype.h>

int main()
{
#if !defined(__FreeBSD__) && !defined(__OpenBSD__) && !defined(__NetBSD__)
  // We would need to model conversion tables, where each of the BSDs has their
  // peculiar approach.
  int x;
  int r = tolower(x);
  assert(r >= x);
#endif
  return 0;
}

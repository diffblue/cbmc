#include <stdio.h>

// A plain (non-static) inline definition survives into the goto model on all
// platforms but is never called and never has its address taken, so it is not
// reachable from the entry point. Before the fix, inline functions were
// treated as reachable regardless, which is the bug being guarded against
// (see #5173).
inline int uncalled_inline(void)
{
  return getchar();
}

int main()
{
  return 0;
}

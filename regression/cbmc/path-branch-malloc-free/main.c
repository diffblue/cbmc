#include <stdlib.h>

// Each `free` call previously triggered two GOTO branches in the CPROVER
// library bookkeeping (one in `free` itself for the memory-leak update and
// one in `__CPROVER_deallocate` for the nondeterministic deallocation
// tracking). Under `--paths lifo`, those branches multiplied the symex
// state space by ~4 per call, so a handful of `malloc`/`free` pairs caused
// exponential path explosion and reliably timed out before the bookkeeping
// was rewritten as conditional expressions. With the rewrite this same
// program runs in seconds; without it, ctest's 1200s per-profile timeout
// is comfortably exceeded.
int main(void)
{
  void *p0 = malloc(8);
  void *p1 = malloc(8);
  void *p2 = malloc(8);
  void *p3 = malloc(8);
  void *p4 = malloc(8);
  void *p5 = malloc(8);
  void *p6 = malloc(8);
  void *p7 = malloc(8);
  void *p8 = malloc(8);
  void *p9 = malloc(8);
  void *pA = malloc(8);

  free(p0);
  free(p1);
  free(p2);
  free(p3);
  free(p4);
  free(p5);
  free(p6);
  free(p7);
  free(p8);
  free(p9);
  free(pA);

  return 0;
}

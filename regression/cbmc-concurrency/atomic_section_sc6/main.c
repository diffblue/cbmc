#include <assert.h>

int spawned=0;

void check()
{
   assert(spawned>0);
}

void spawn()
{
__CPROVER_ASYNC_1: check();
}

int main()
{
   __CPROVER_atomic_begin();
   ++spawned;
   spawn();
   __CPROVER_atomic_end();
   return 0;
}

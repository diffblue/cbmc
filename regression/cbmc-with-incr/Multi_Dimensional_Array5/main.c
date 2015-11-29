// from CSmith

#include <assert.h>

int g_134 = 1;
int *g_374[1][1] = {{&g_134}};

void func_79(int * p_80)
{
   *p_80 = 0;
   assert(*p_80==0);
   assert(g_134==0);
}

int main ()
{
   func_79(*(&(g_374[0][0])));
   return 0;
}


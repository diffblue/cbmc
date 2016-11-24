#include <assert.h>

static int 
(safe_mod_func_int32_t_s_s)(int si1, int si2 )
{
 return

   ((si2 == 0) || ((si1 == (-2147483647-1)) && (si2 == (-1)))) ?
   ((si1)) :

   (si1 % si2);
}

int main()
{
 int a, b;
#ifdef __CPROVER__
 __CPROVER_assume(a==1);
 __CPROVER_assume(b==-2);
#else
 a=1;
 b=-2;
#endif
 int x=safe_mod_func_int32_t_s_s(a, b); 
 assert(x==1);
 return 0;
}

void assert(_Bool cond);

#ifdef PRINT
#include <stdio.h>
void assert(int cond) 
{ if(!cond) printf("assert failed!\n"); }
#endif

/* struct str2;  // <-- CBMC requires this line - but gcc doesn't. */

/* struct str2* gp1; // this does the work too */

typedef struct str1 {
  short x;
  struct str2* p2;
} Str1;

typedef struct str2 { /* rename this to "str2_" and it passes OK */
  short y;
  struct str1* p1;
} Str2;

int main()
{
  Str1 st1;
  Str2 st2 = { 1234, &st1 };

  assert( st2.y == 1234 );

  return 0;
}

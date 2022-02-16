#include <stdbool.h>
#include <stdlib.h>

bool nondet_bool();

typedef enum ABC
{
  A = 0,
  B = 1,
  C = 2
} ABC;

int main()
{
#pragma CPROVER check push
#pragma CPROVER check disable "bounds"
#pragma CPROVER check disable "pointer"
#pragma CPROVER check disable "div-by-zero"
#pragma CPROVER check disable "enum-range"
#pragma CPROVER check disable "signed-overflow"
#pragma CPROVER check disable "unsigned-overflow"
#pragma CPROVER check disable "pointer-overflow"
#pragma CPROVER check disable "float-overflow"
#pragma CPROVER check disable "conversion"
#pragma CPROVER check disable "undefined-shift"
#pragma CPROVER check disable "nan"
#pragma CPROVER check disable "pointer-primitive"
  {
    int N = 10;
    char *p = malloc(N * sizeof(*p));
    char *q;
    char *r;
    float den;
    float x;
    float y;
    ABC e;
    bool readable;
    char i;
    signed int j;
    readable = __CPROVER_r_ok(q, 1);
    q = p + 2000000000000;
    q = r;
    if(nondet_bool())
      den = 0.0;
    else
      den = 1.0;
    y = x / den;
    e = 10;
    i += 1;
    j += 1;
  }
#pragma CPROVER check push
#pragma CPROVER check enable "bounds"
#pragma CPROVER check enable "pointer"
#pragma CPROVER check enable "div-by-zero"
#pragma CPROVER check enable "enum-range"
#pragma CPROVER check enable "signed-overflow"
#pragma CPROVER check enable "unsigned-overflow"
#pragma CPROVER check enable "pointer-overflow"
#pragma CPROVER check enable "float-overflow"
#pragma CPROVER check enable "conversion"
#pragma CPROVER check enable "undefined-shift"
#pragma CPROVER check enable "nan"
#pragma CPROVER check enable "pointer-primitive"
  {
    int N = 10;
    char *p = malloc(N * sizeof(*p));
    char *q;
    char *r;
    float den;
    float x;
    float y;
    ABC e;
    bool readable;
    char i;
    signed int j;
    readable = __CPROVER_r_ok(q, 1);
    q = p + 2000000000000;
    q = r;
    if(nondet_bool())
      den = 0.0;
    else
      den = 1.0;
    y = x / den;
    e = 10;
    i += 1;
    j += 1;
  }
#pragma CPROVER check pop
#pragma CPROVER check pop
  return 0;
}

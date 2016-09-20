#include <assert.h>

// __VERIFIER_assume
// file <built-in-additions> line 3
void __VERIFIER_assume(_Bool);
// __assert_fail
// file /usr/include/assert.h line 67
extern void __assert_fail(const char *, const char *, unsigned int, const char *) _Noreturn;
// nondet_float
// file constant_propagation_20.c line 5
void nondet_float();

// Alen
// file constant_propagation_20.c line 3
const signed int Alen=2;
// Blen
// file constant_propagation_20.c line 4
const signed int Blen=1;
// main_return_value
// 
static signed int main_return_value;
// nondet_float_return_value
// 
static float nondet_float_return_value;
// xLen
// file constant_propagation_20.c line 2
const signed int xLen=10;

// main
// file constant_propagation_20.c line 6
void main()
{
  float A[2l]={ 1.0f, -5.000000e-1f };
  float B[1l]={ 1.0f };
  signed int i;
  signed int j;
  const signed long int j$array_size0=(signed long int)xLen;
  float x[j$array_size0];
  const signed long int x$array_size0=(signed long int)xLen;
  float x_aux[x$array_size0];
  const signed long int x_aux$array_size0=(signed long int)xLen;
  float y[x_aux$array_size0];
  const signed long int y$array_size0=(signed long int)xLen;
  float y_aux[y$array_size0];
  float total=0.000000f;
  i = 0;
  for( ; xLen >= 1; i = 1 + i)
  {
    x[(signed long int)i] = nondet_0();
    _Bool tmp_if_expr$1;
    if(x[0l] >= -1.000000f)
      tmp_if_expr$1 = x[0l] <= 1.000000f;

    else
      tmp_if_expr$1 = (_Bool)0;
    __CPROVER_assume(tmp_if_expr$1);
    x_aux[(signed long int)i] = 0.000000f;
    y_aux[(signed long int)i] = 0.000000f;
  }
  i = 0;
  for( ; xLen >= 1; i = 1 + i)
  {
    y[(signed long int)i] = 0.000000f;
    j = -1 + Blen;
    for( ; j >= 1; j = -1 + j)
      x_aux[(signed long int)j] = x_aux[(signed long int)(-1 + j)];
    x_aux[0l] = x[(signed long int)i];
    j = 0;
    for( ; !(j >= Blen); j = 1 + j)
    {
      y[(signed long int)i] = y[(signed long int)i] + B[(signed long int)j] * x_aux[(signed long int)j];
      _Bool tmp_if_expr$2;
      if(y[(signed long int)i] >= -2.000000f)
        tmp_if_expr$2 = y[(signed long int)i] <= 2.0f;

      else
        tmp_if_expr$2 = (_Bool)0;
      /* assertion y[i]>=-2.0f && y[i]<=2.0f */
      assert(tmp_if_expr$2);
    }
    j = 0;
    for( ; !(j >= -1 + Alen); j = 1 + j)
    {
      y[(signed long int)i] = y[(signed long int)i] + -(A[(signed long int)(1 + j)] * y_aux[(signed long int)j]);
      _Bool tmp_if_expr$3;
      if(y[(signed long int)i] >= -2.000000f)
        tmp_if_expr$3 = y[(signed long int)i] <= 2.0f;

      else
        tmp_if_expr$3 = (_Bool)0;
      /* assertion y[i]>=-2.0f && y[i]<=2.0f */
      assert(tmp_if_expr$3);
    }
    j = -2 + Alen;
    for( ; j >= 1; j = -1 + j)
      y_aux[(signed long int)j] = y_aux[(signed long int)(-1 + j)];
    y_aux[0l] = y[(signed long int)i];
  }
  main_return_value = nondet_signed_int();
}


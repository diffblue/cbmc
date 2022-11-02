#include <stdbool.h>
#include <stdlib.h>

/* Function return code  */
#define S2N_SUCCESS 0
#define S2N_FAILURE -1

/* A value which indicates the outcome of a function */
typedef struct
{
  int __error_signal;
} s2n_result;

#define S2N_RESULT s2n_result
#define S2N_RESULT_OK ((s2n_result){S2N_SUCCESS})
#define S2N_RESULT_ERROR ((s2n_result){S2N_FAILURE})

bool s2n_result_is_ok(s2n_result result)
{
  return result.__error_signal == S2N_SUCCESS;
}

bool validity1(int *x)
{
  return (x > 0);
}

bool validity2(int *x)
{
  return (x == 0);
}

S2N_RESULT validity3(int *x)
{
  if(x == NULL)
    return S2N_RESULT_ERROR;
  if(!validity1(x))
    return S2N_RESULT_ERROR;
  return S2N_RESULT_OK;
}

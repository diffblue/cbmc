#include <assert.h>

int main()
{
  unsigned x = __VERIFIER_nondet_unsigned();

  if(x>=0 && x<=1000)
  {
    struct
    {
      int asd;

      union {
        int i;
        char array[x];
      };
    } *ptr;

    if(x<=sizeof(int))
      assert(sizeof(*ptr)==sizeof(int)*2);
    else
      assert(sizeof(*ptr)==sizeof(int)+x);
  }
}

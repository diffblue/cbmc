// based on
// http://lists.cs.uiuc.edu/pipermail/llvm-commits/Week-of-Mon-20140303/207014.html

#include <assert.h>

#ifdef __GNUC__
typedef int v4si __attribute__ ((vector_size (16)));
#endif

int main()
{
  #ifdef __GNUC__

  v4si a = { 0, 1, 2, 3 }, b;

  b[0] = 0;
  b[1] = 1;
  b[2] = 2;
  b[3] = 3;

  for (int i = 0; i < 4; ++i) {
    /*
    printf("i = %d: a[i] = %d, b[i] = %d, cast(a)[i] = %d, cast(b)[i] = %d\n",
           a[i], b[i], ((int*) &a)[i], ((int*) &b)[i]);
    */
    int a_i=a[i];
    int b_i=b[i];
    assert(a[i]==b[i]);
    assert(a[i]==((int*) &a)[i]);
    assert(((int*) &a)[i]==((int*) &b)[i]);
    assert(((int*) &b)[i]==b[i]);
  }
  
  #endif

  return 0;
}

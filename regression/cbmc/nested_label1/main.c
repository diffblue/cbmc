#include <assert.h>

int main()
{
  goto label2;
  goto out;
label1:
label2:
label3:
  assert(0);
out:
  return 0;
}

#include <assert.h>

void main()
{
  int i = 0;
  int j = 0;

HEAD:
  if(i > 5)
    goto EXIT1;
  i++;
  goto HEAD;
EXIT1:;
  if(j > 5)
    goto EXIT2;
  j++;
  goto HEAD;
EXIT2:;
}

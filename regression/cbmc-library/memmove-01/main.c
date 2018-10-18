#include <assert.h>
#include <stdio.h>
#include <string.h>

void sort_items_by_criteria(int *item, int left, int right)
{
  int lidx = left, ridx = (left + right) / 2 + 1,
      lsize = (left + right) / 2 - left + 1;
  int tmp;

  if(right - left < 1)
    return;
  sort_items_by_criteria(item, left, (left + right) / 2);
  sort_items_by_criteria(item, (left + right) / 2 + 1, right);

  while(ridx <= right && lidx < ridx)
  {
    if(item[lidx] > item[ridx])
    {
      tmp = item[ridx];
      memmove(item + lidx + 1, item + lidx, lsize * sizeof(int));
      item[lidx] = tmp;
      ++ridx;
      ++lsize;
    }
    ++lidx;
    --lsize;
  }
}

int main(int argc, char *argv[])
{
  int a[7];

  //CBMC reports wrong results for 256, -2147221455, -2147221455, -2147221455, 16, -2147483600, 16384
  a[0] = 256;
  a[1] = -2147221455;
  a[2] = -2147221455;
  a[3] = -2147221455;
  a[4] = 16;
  a[5] = -2147483600;
  a[6] = 16384;

  sort_items_by_criteria(a, 0, 6);

  printf("%d %d %d %d %d %d %d\n", a[0], a[1], a[2], a[3], a[4], a[5], a[6]);

  assert(a[0] == -2147483600);
  return 0;
}

#include <assert.h>

int main(int argc, char **argv)
{
  int branch;
  int x = 0;

  if(branch)
  {
    x = 1;
  }
  else
  {
    x = -1;
  }

  // Merging a constant domain here will make this unprovable
  assert(x != 0);

  // Some subtle points here...
  // The history tracks paths, it is up to the domain to track the
  // path conditon / consequences of that path.
  //
  // We have two paths:
  //  branch == ?, x ==  1
  //  branch == 0, x == -1
  //
  // As the domain in the first case can't express branch != 0
  // we will wind up with three paths here, including a spurious
  // one with branch == 0, x == 1.
  if(branch)
  {
    assert(x == 1);
  }
  else
  {
    assert(x == -1);
  }

  // Working around the domain issues...
  // (This doesn't increase the number of paths)
  if(x == 1)
  {
    x--;
  }
  else
  {
    x++;
  }

  // Should be true in all 3 paths
  assert(x == 0);

  return 0;
}

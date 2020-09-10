#include <assert.h>

int main(int argc, char **argv)
{
  int branching_array[5];
  int x = 1;

  if(branching_array[0])
  {
    ++x;
  }
  // Two paths...
  assert(x > 0);

  if(branching_array[1])
  {
    ++x;
  }
  // Four paths...
  assert(x > 0);

  if(branching_array[2])
  {
    ++x;
  }
  // Eight paths...
  assert(x > 0);

  if(branching_array[3])
  {
    ++x;
  }
  // Paths merge so there will be some paths that will set x to \top
  // and so this will be flagged as unknown
  assert(x > 0);
  // In principle it would be possible to merge paths in such a way
  // that the those with similar domains are merged and this would be
  // able to be proved.  The local_control_flow_history code doesn't
  // do this though.

  return 0;
}

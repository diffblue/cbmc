#include <assert.h>

void f00(int x, int y)
{
  if(x < 0)
  {
    // Unreachable in all traces if they are considered individually
    assert(x < 0);
    assert(1);
    assert(0);
  }

  assert(x >= 0); // True in all traces
  assert(x < 0);  // False in all traces
  assert(x < 2);  // Split; true in some, false in others

  assert((x <= 0) ? 1 : y);                  // True in some, unknown in others
  assert((x <= 1) ? 0 : y);                  // False in some, unknown in others
  assert((x <= 2) ? ((x <= 3) ? 1 : 0) : y); // A mix of all three

  if(x < 5)
  {
    // Not reachable in all traces
    assert((x <= 0) ? 1 : y); // True in some, unknown in others
    assert((x <= 1) ? 0 : y); // False in some, unknown in others
    assert((x <= 2) ? ((x <= 3) ? 1 : 0) : y); // A mix of all three
  }

  if(x < 3)
  {
    // Not reachable in all traces
    assert((x <= 0) ? 1 : y); // True in some, unknown in others
    assert((x <= 1) ? 0 : y); // False in some, unknown in others
    assert((x <= 2) ? ((x <= 3) ? 1 : 0) : y); // A mix of all three
  }
}

int nondet_int();

int main(int argc, char **argv)
{
  int y = nondet_int();

  // Because the history is context sensitive these should be analysed independently
  // Just showing the domain will merge them giving top for everything interesting
  f00(0, y);
  f00(1, y);
  f00(2, y);
  f00(3, y);
  f00(4, y);
  f00(5, y);

  return 0;
}

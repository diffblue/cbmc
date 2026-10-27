// Author: Wang Chuanhao
/// \file
/// Implicit copy assignment copies every element of an array member.

#include <cassert>

struct S
{
  int values[2];

  S()
  {
    values[0] = 0;
    values[1] = 0;
  }
};

int main()
{
  S source, destination;
  source.values[0] = 7;
  source.values[1] = 11;
  destination = source;
  assert(destination.values[0] == 7);
  assert(destination.values[1] == 11);
}

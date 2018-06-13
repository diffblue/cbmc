#include <cassert>

const auto i=1;

int main (int argc, char **argv) {
  int x = 23;
  int y = 42;

  auto z = x + y;

  assert(z > 64);

  return 0;
}

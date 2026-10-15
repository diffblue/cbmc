#include <cassert>

int main(int argc, char * argv[])
{
  struct S {
    S() : x(42)
                 {
                 }

    int x;
  };
  S s = S{};

  __CPROVER_assert(s.x == 42, "");
  assert(s.x == 42);
}

// C++11: alignas specifier on struct/class/union declarations
struct alignas(16) S
{
  int x;
  int y;
};

class alignas(32) C
{
public:
  int a;
};

union alignas(8) U
{
  int i;
  float f;
};

int main()
{
  S s;
  s.x = 1;
  s.y = 2;
  __CPROVER_assert(s.x + s.y == 3, "struct alignas");

  C c;
  c.a = 42;
  __CPROVER_assert(c.a == 42, "class alignas");

  U u;
  u.i = 10;
  __CPROVER_assert(u.i == 10, "union alignas");
}

// using declarations in statement context and top-level asm
namespace N
{
int x = 42;
}

void f()
{
  using N::x;
}

__asm(".globl dummy_symbol");

int main()
{
  f();
  return 0;
}

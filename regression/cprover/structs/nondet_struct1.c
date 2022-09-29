struct S
{
  int x, y;
} s;

struct S nondet_S();

int main()
{
  s = nondet_S();
  return 0;
}

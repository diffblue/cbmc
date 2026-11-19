int g;
void foo(int x)
{
  g = x;
}
int main()
{
  foo(1);
  return g;
}

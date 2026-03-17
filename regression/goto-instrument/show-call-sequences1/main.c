int g;
void foo(int x) { g = x; }
int main()
{
  int i;
  for(i = 0; i < 10; i++)
    foo(i);
  return g;
}

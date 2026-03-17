// Test overload resolution with different parameter counts
void f(int)
{
}
void f(int, int)
{
}

int main()
{
  f(1);
  f(1, 2);
  return 0;
}

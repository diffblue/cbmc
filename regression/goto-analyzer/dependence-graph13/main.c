void bar(int a, int b)
{
  int result = b;
}

void main()
{
  int a = 1;
  int b = 2;
  int c = 3;
  bar(a, b + c);
}

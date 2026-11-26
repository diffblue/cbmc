struct S
{
  int a, b;
};

int main(void)
{
  int n = 0;
  static int x = ((struct S){n++, 1}).b;
  return x;
}

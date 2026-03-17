struct s {
  char a;
  int b;
  char c;
};

int main()
{
  struct s x;
  x.a = 1;
  x.b = 2;
  x.c = 3;
  return x.b;
}

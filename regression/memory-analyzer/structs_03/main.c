void checkpoint()
{
}

struct S
{
  int c1;
  char *c2;
};

struct S st = {1, "abc"};

int main()
{
  checkpoint();

  return 0;
}

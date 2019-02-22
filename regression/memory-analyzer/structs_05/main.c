void checkpoint()
{
}

struct S
{
  int c1;
  int a[2];
};

struct S st = {1, {2, 3}};

int main()
{
  checkpoint();

  return 0;
}

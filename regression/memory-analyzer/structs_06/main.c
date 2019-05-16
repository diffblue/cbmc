void checkpoint()
{
}

struct T
{
  int i;
};

struct S
{
  int c;
  struct T t;
};

struct S st = {1, {2}};

int main()
{
  checkpoint();

  return 0;
}

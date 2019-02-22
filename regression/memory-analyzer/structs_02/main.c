void checkpoint()
{
}

struct S
{
  int c1;
  int *c2;
};

int i = 0;
struct S st = {1, &i};

int main()
{
  i = 3;

  checkpoint();

  return 0;
}

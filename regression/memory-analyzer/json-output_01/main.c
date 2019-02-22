void checkpoint()
{
}

int x = 3;
int *p = &x;

struct S
{
  int c1;
  int c2;
};

struct S st = {.c1 = 1, .c2 = 2};

int a[] = {1, 2, 3};

int main()
{
  checkpoint();

  return 0;
}

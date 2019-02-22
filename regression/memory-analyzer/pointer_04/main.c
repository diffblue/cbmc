void checkpoint()
{
}

int x = 3;
int *p1 = &x;
int **p2 = &p1;

int main()
{
  checkpoint();

  return 0;
}

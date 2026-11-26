int g;
int main()
{
  int x = 0;
  int *local = &x;
  int *global = &g;
  int *null = 0;
  *local = 1;
  return x;
}

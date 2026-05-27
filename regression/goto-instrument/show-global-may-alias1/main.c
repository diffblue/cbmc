int g;
int *p;
int main()
{
  p = &g;
  g = 1;
  return *p;
}

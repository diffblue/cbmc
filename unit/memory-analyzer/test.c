int x;
char *s = "abc";
int *p;
void *vp;

void checkpoint()
{
}
void checkpoint2()
{
}

void func()
{
  checkpoint2();
}

int main()
{
  x = 8;
  p = &x;
  vp = (void *)&x;

  checkpoint();

  return 0;
}

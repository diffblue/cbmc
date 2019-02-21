int x;
float y;
char z;

char *s = "abc";
int *p;
void *vp;
int *np = 0;
void *vp_string;

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
  y = 2.5;
  z = 'c';

  p = &x;
  vp = (void *)&x;
  vp_string = s;

  checkpoint();

  return 0;
}

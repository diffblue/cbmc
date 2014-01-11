struct S
{
  char a, b, c, d;
} x;

int main()
{
  int i;
  char *p;
  
  p=&x.a;
  
  p[0]=1;
  p[1]=2;
  p[2]=3;
  p[3]=4;

  assert(x.a==1);
  assert(x.b==2);
  assert(x.c==3);
  assert(x.d==4);
}

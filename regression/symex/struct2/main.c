struct X
{
  int a, b;
} x;

int main()
{
  int *p;
  
  p=&x.a;
  *p=10;
  p++;
  *p=11;

  assert(x.a==10 && x.b==11);
}

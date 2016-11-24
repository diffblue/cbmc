struct X
{
  int a, b, c;
};

int main()
{
  int aa, bb, cc;
  
  struct X foo;
  
  foo=(struct X) { aa, bb, cc };
  
  assert(foo.a==aa);
  assert(foo.b==bb);
  assert(foo.c==cc);
}

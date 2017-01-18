
void f()
{
  int i;
  for (i = 0; i < 10; i++) {}
}

void g()
{
  int i;
  for (i = 0; i < 10; i++) {}
  for (i = 0; i < 10; i++) {}
}

int main()
{
  f();
  g();

  int i;
  for(i = 0; i < 10; i++) {}
}

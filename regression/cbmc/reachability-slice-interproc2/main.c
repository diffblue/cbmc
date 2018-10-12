void b();

void c()
{
  __CPROVER_assert(0, "");
  b();
}

void b()
{
  a();
  c();
}

void a()
{
  c();
}

int main()
{
  a();
}

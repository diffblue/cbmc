void a()
{
  __CPROVER_assert(0, "");
}

int main()
{
  a();
}

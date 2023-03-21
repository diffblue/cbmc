int foo()
{
}

int main()
{
  int (*fp)() = &foo;
  (*fp)();
}

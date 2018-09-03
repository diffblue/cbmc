int bar(int x)
{
  return 42;
}

int foo(int x)
{
  return bar(x);
}

int main(int argc, char* argv[])
{
  return foo(argc);
}

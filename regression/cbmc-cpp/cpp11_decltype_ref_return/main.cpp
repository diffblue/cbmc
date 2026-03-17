int global = 42;
int &get_ref()
{
  return global;
}

decltype(get_ref()) wrapper()
{
  return get_ref();
}

int main()
{
  // decltype(get_ref()) should be int&, so wrapper() returns int&
  wrapper() = 99;
  __CPROVER_assert(global == 99, "decltype preserves ref in return type");
}

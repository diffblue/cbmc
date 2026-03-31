// C++23 language features require GCC 11+
#if !defined(__GNUC__) && !defined(_MSC_VER) || __GNUC__ >= 11
// C++23 if !consteval
int f()
{
  if !consteval
  {
    return 42;
  }
  else
  {
    return 0;
  }
}

int main()
{
  __CPROVER_assert(f() == 42, "runtime branch taken");
}

#else
int main()
{
}
#endif

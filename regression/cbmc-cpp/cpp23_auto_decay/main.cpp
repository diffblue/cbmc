// C++23 language features require GCC 11+
#if !defined(__GNUC__) || __GNUC__ >= 11
int main()
{
  int arr[] = {1, 2, 3};
  auto p = auto(arr); // decays to int*
  __CPROVER_assert(*p == 1, "decay copy");
}

#else
int main()
{
}
#endif

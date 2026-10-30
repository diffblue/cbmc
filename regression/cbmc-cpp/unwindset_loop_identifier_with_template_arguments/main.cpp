// The identifier of a loop in a function template specialization with
// several template arguments contains a comma,
// `fill<signed_int,3>(ptr_signed_int).0', and --unwindset splits its
// argument at every comma.
extern "C" void __CPROVER_assert(bool, const char *);

template <class T, int N>
void fill(T *p)
{
  for(int i = 0; i < N; ++i)
    p[i] = T(1);
}

int main()
{
  int a[3];
  fill<int, 3>(a);
  __CPROVER_assert(a[2] == 1, "filled");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}

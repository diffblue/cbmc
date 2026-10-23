// N5008 [temp.deduct.call]/2.1: if P is not a reference type and A is an
// array type, the pointer type from the array-to-pointer conversion is used
// in place of A.  CBMC applied this only for P = T, so `f(arr)' with
// `template <class X> int f(X *)' (or `const X *', `box<X> f(X *)')
// found no match.
extern "C" void __CPROVER_assert(bool, const char *);

template <class X>
struct box
{
  long count;
};

template <class X>
int f(X *p)
{
  return p[1];
}

template <class X>
int g(const X *p)
{
  return p[2];
}

template <class X>
auto make(X *)
{
  return box<X *>{3};
}

int main()
{
  int arr[5] = {1, 2, 3, 4, 5};
  __CPROVER_assert(f(arr) == 2, "X *");
  __CPROVER_assert(g(arr) == 3, "const X *");
  auto b = make(arr);
  __CPROVER_assert(__is_same(decltype(b), box<int *>), "deduced X");
  __CPROVER_assert(b.count == 3, "value");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}

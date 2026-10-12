// N5008 [temp.spec.partial.order]/1, [temp.func.order]: K<box<int
// (*)(char)>> matches both partial specializations -- `R *' with
// R = int(char) and `R (*)(char)' with R = int.  The second is more
// specialized (its argument deduces the first's, not vice versa), so it is
// used.  CBMC picks the first.
extern "C" void __CPROVER_assert(bool, const char *);

template <class T>
struct box
{
};

template <class A>
struct K
{
  static const int n = 1;
};
template <class R>
struct K<box<R *>>
{
  static const int n = 2;
};
template <class R>
struct K<box<R (*)(char)>>
{
  static const int n = 4;
};

int main()
{
  __CPROVER_assert(K<box<int *>>::n == 2, "pointer");
  __CPROVER_assert(K<box<int (*)(char)>>::n == 4, "more specialized");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}

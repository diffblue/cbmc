// N5008 [temp.spec.partial.order]/1, [temp.func.order]: K<box<int
// (*)(char)>> matches both partial specializations -- `R *' with
// R = int(char) and `R (*)(char)' with R = int.  The second is more
// specialized (its argument deduces the first's, not vice versa), so it is
// used.  The ordering compared the template-ids `box<...>' as a whole and
// deduced nothing from them.  L checks the same for the declaration order
// reversed and a nested template-id.
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

template <class A>
struct L
{
  static const int n = 1;
};
template <class R>
struct L<box<box<R>> *>
{
  static const int n = 3;
};
template <class R>
struct L<R *>
{
  static const int n = 2;
};

int main()
{
  __CPROVER_assert(K<box<int *>>::n == 2, "pointer");
  __CPROVER_assert(K<box<int (*)(char)>>::n == 4, "more specialized");
  __CPROVER_assert(L<int *>::n == 2, "pointer, reversed");
  __CPROVER_assert(L<box<box<int>> *>::n == 3, "nested template-id");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}

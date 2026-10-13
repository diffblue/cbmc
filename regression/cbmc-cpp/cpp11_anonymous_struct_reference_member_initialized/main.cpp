// A GNU anonymous struct member (accepted by g++ and clang++) may hold a
// reference, unlike an anonymous union (N5008 [class.union.general]/3 is a
// rule for unions only): libc++ 21's _LIBCPP_COMPRESSED_PAIR is an
// anonymous struct, and __split_buffer<T, Alloc &> keeps its `allocator_type
// __alloc_' -- a reference -- in it.  The front end rejected the reference
// ("anonymous struct/union member of reference type"); it also routed only
// the FIRST mem-initializer naming a member of an anonymous struct to that
// subobject (`cap(nullptr), alloc(a)' left alloc uninitialized).
extern "C" void __CPROVER_assert(bool, const char *);
template <class A>
struct Buf
{
  int *first;
  struct
  {
    int *cap;
    A alloc;
  };
  explicit Buf(A a) : first(nullptr), cap(nullptr), alloc(a)
  {
  }
  int get() const
  {
    return alloc.n;
  }
  void bump()
  {
    ++alloc.n;
  }
};
struct Alloc
{
  int n;
};
int main()
{
  Alloc a{3};
  Buf<Alloc &> b(a);
  b.bump();
  __CPROVER_assert(
    b.get() == 4 && a.n == 4, "reference member of anonymous struct aliases");
  __CPROVER_assert(b.cap == nullptr && b.first == nullptr, "other members");
  Buf<Alloc> c(a);
  c.bump();
  __CPROVER_assert(c.get() == 5 && a.n == 4, "by value");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}

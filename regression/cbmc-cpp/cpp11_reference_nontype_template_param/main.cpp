// N5008 [temp.param]/4, [temp.arg.nontype]/1-2: a non-type template parameter
// may have reference type, and its argument designates an object with static
// storage duration (an address constant), not a value.  CBMC's util uses this:
//   template <typename T, const T &empty = T::blank> class reference_counting;
// (src/util/reference_counting.h).  Here `empty` defaults to the static member
// S::blank; r.get() returns that reference, so r.get().x == 7.  g++/clang++
// agree.
//
// KNOWN BUG: CBMC mishandles reference non-type template parameters.  The
// parameter's declarator `&` is dropped (treating `const T &empty` as a value
// parameter of type T), the reference argument (the static object S::blank) is
// valuified, and instantiation fails -- currently with a CONVERSION ERROR
// ("expected constant expression"), previously with an abort in
// to_constant_expr while building the instance name.  The abort has been fixed
// (template_suffix no longer forces a scalar-constant conversion on a
// non-scalar / reference / class-type non-type template argument,
// [temp.arg.nontype]); full support (keeping the argument as an address of the
// static object end-to-end so the reference parameter binds correctly) remains.
// Flip to CORE once reference non-type template parameters are fully supported.

extern "C" void __CPROVER_assert(int, const char *);

struct S
{
  int x;
  static const S blank;
};
const S S::blank = {7};

template <typename T, const T &empty = T::blank>
struct rc
{
  const T &get() const
  {
    return empty;
  }
};

int main()
{
  rc<S> r;
  __CPROVER_assert(r.get().x == 7, "reference NTTP defaults to S::blank");
  __CPROVER_assert(r.get().x != 7, "WRONG must FAIL");
  return 0;
}

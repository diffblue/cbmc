// N5008 [temp.param]/4, [temp.arg.nontype]/1-2: a non-type template parameter
// may have reference type, and its argument designates an object with static
// storage duration (an address constant), not a value.  CBMC's util uses this:
//   template <typename T, const T &empty = T::blank> class reference_counting;
// (src/util/reference_counting.h).  Here `empty` defaults to the static member
// S::blank; r.get() returns that reference, so r.get().x == 7.  g++/clang++
// agree.
//
// This exercises full reference non-type template parameter support: the
// parameter keeps its reference type (the declarator's `&` is merged into the
// parameter type), the reference argument is kept as the address of the static
// object rather than being valuified, and the instance-name suffix is built
// from the object's identity.  assertion.2 must FAIL, proving the property in
// assertion.1 is non-vacuous.

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

// N5008 [dcl.type.decltype]/1.5: decltype(E) for an lvalue expression E
// of type T is T&; indirection is an lvalue ([expr.unary.op]/1), so
// decltype(*p) must be int&.  CBMC used to compute int, collapsing
// libc++'s iter_reference_t (decltype(*declval<_Tp&>())) to a value
// type: assignment through any iterator's operator* failed as "not an
// lvalue" (third layer of the vector push_back family).
extern "C" void __CPROVER_assert(bool, const char *);

template <class T>
using ref_t = decltype(*T());

template <class T, class U>
struct same
{
  static const bool value = false;
};
template <class T>
struct same<T, T>
{
  static const bool value = true;
};
static_assert(same<ref_t<int *>, int &>::value, "decltype(*p) is int&");

struct it
{
  int *p;
  ref_t<int *> operator*()
  {
    return *p;
  }
};

int b;

int main()
{
  it i{&b};
  *i = 5;
  __CPROVER_assert(b == 5, "assigned through iterator");
}

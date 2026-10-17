// N5008 [expr.prim.req.compound]/1: `{ E } -> C' is satisfied iff
// C<decltype((E))> is; [dcl.type.decltype]/1.4-1.6: for an xvalue E that is
// T&&, for an lvalue T&, for a prvalue T.  The compound requirement took the
// type of the (implicitly dereferenced) operand and added `&' for an lvalue
// only, so a call returning an rvalue reference read as a prvalue: libc++'s
// `{ ranges::iter_move(__i) } -> same_as<iter_rvalue_reference_t<_In>>'
// (int&&) failed and no pointer was indirectly_readable, hence no
// input_iterator, hence no contiguous_range and no std::span from a range.
extern "C" void __CPROVER_assert(bool, const char *);

template <class T, class U>
concept same_as = __is_same(T, U);

int g;
int &lval()
{
  return g;
}
int &&xval()
{
  return static_cast<int &&>(g);
}
int prval()
{
  return g;
}
struct S
{
  int m;
  int &&mv()
  {
    return static_cast<int &&>(m);
  }
};

template <class F>
concept LRef = requires(F f)
{
  {
    f()
    } -> same_as<int &>;
};
template <class F>
concept RRef = requires(F f)
{
  {
    f()
    } -> same_as<int &&>;
};
template <class F>
concept PR = requires(F f)
{
  {
    f()
    } -> same_as<int>;
};
template <class P>
concept DerefLRef = requires(P p)
{
  {
    *p
    } -> same_as<int &>;
};
template <class P>
concept MoveDeref = requires(P p)
{
  {
    static_cast<int &&>(*p)
    } -> same_as<int &&>;
};
template <class T>
concept MemberMove = requires(T t)
{
  {
    t.mv()
    } -> same_as<int &&>;
};
template <class T>
concept MemberRead = requires(T t)
{
  {
    t.m
    } -> same_as<int &>;
};

static_assert(LRef<int &(*)()>, "lvalue-returning call: int&");
static_assert(!RRef<int &(*)()>, "lvalue-returning call is not int&&");
static_assert(RRef < int && (*)() >, "xvalue call: int&&");
static_assert(!LRef < int && (*)() >, "xvalue call is not int&");
static_assert(!PR < int && (*)() >, "xvalue call is not a prvalue");
static_assert(PR<int (*)()>, "prvalue call: int");
static_assert(DerefLRef<int *>, "*p is an lvalue: int&");
static_assert(MoveDeref<int *>, "static_cast<int&&>(*p): int&&");
static_assert(MemberMove<S>, "member call returning int&&");
static_assert(MemberRead<S>, "member read: int&");

template <class F>
requires RRef<F> int pick(F)
{
  return 2;
}
template <class F>
requires LRef<F> int pick(F)
{
  return 1;
}

int main()
{
  __CPROVER_assert(
    pick(&lval) == 1 && pick(&xval) == 2, "overloads by value category");
  __CPROVER_assert(pick(&xval) == 1, "WRONG (must FAIL)");
}

extern "C" void __CPROVER_assert(bool, const char *);
// N5008 [dcl.ref]/1, [expr.ref]/7: a data member of type "reference to
// function" names the function, so `h.f' is a function lvalue that can be
// passed and called (the MSVC STL's _Binder stores a reference to the
// bound function this way)
template <class F, class... A>
auto call(F obj, A... a) -> decltype(obj(a...))
{
  return obj(a...);
}
long add(long a, long b)
{
  return a + b + 1;
}
struct holder
{
  long (&f)(long, long);
};
int main()
{
  long (&r)(long, long) = add;
  __CPROVER_assert(call(r, 2L, 3L) == 6, "1 reference variable");
  holder h{add};
  __CPROVER_assert(call(h.f, 2L, 3L) == 6, "2 reference member");
  __CPROVER_assert(call(add, 2L, 3L) == 6, "3 function name");
  __CPROVER_assert(h.f(1L, 1L) == 2, "WRONG (must FAIL)");
}

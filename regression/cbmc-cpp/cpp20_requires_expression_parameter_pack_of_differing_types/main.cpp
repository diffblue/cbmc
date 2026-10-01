extern "C" void __CPROVER_assert(bool, const char *);
bool g(const int &, int &)
{
  return true;
}
// [expr.prim.req.general]/4, [temp.variadic]/5: the parameter pack `a'
// declares one parameter per element of A, the k-th of type A_k &&; libc++'s
// std::invocable has this shape (requires(_Fn &&__fn, _Args &&...__args))
template <class... A>
concept invocable_g = requires(A &&...a) { g(static_cast<A &&>(a)...); };
int main()
{
  __CPROVER_assert(invocable_g<const int &, int &>, "differing element types");
  __CPROVER_assert(
    !invocable_g<const int &, const int &>,
    "second argument of g is not const");
  __CPROVER_assert(!invocable_g<const int &, int &>, "WRONG (must FAIL)");
}

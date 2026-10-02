extern "C" void __CPROVER_assert(bool, const char *);
// [expr.prim.req.general]/4, [temp.variadic]/5: requires-expression
// parameter packs by forwarding reference and by value, in simple and
// compound requirements, including an empty pack
long k(int &, long)
{
  return 2;
}
template <class T>
concept same_long = __is_same(T, long);
template <class A, class B>
concept k_long2 = requires(A &&a, B &&b) {
                    {
                      k(static_cast<A &&>(a), static_cast<B &&>(b))
                      } -> same_long;
                  };
template <class... A>
concept k_long = requires(A &&...a) {
                   {
                     k(static_cast<A &&>(a)...)
                     } -> same_long;
                 };
template <class... A>
concept k_call = requires(A &&...a) { k(static_cast<A &&>(a)...); };
int h()
{
  return 0;
}
int h(int, char)
{
  return 1;
}
template <class... A>
concept callable_h = requires(A... a) { h(a...); };
int main()
{
  __CPROVER_assert(k_long2<int &, long>, "two parameters");
  __CPROVER_assert(
    k_call<int &, long> && !k_call<int, long>, "pack, simple requirement");
  __CPROVER_assert(k_long<int &, long>, "pack, compound requirement");
  __CPROVER_assert(
    callable_h<> && callable_h<int, char> && !callable_h<int>,
    "pack by value, empty pack");
  __CPROVER_assert(!k_call<int &, long>, "WRONG (must FAIL)");
}

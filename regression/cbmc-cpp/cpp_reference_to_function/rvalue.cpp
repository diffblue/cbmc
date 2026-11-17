extern "C" void __CPROVER_assert(bool, const char *);
int hit;
void cb(int k)
{
  hit = k;
}
template <class A, class B>
struct same
{
  static const bool value = false;
};
template <class A>
struct same<A, A>
{
  static const bool value = true;
};
// [temp.deduct.call]/3: a forwarding reference deduces T = void (&)(int)
// from the function lvalue cb
template <class T>
bool forward_call(T &&f)
{
  f(2);
  return same<T, void (&)(int)>::value;
}
int main()
{
  // [dcl.init.ref]/5.3.1: an rvalue reference to function binds to the
  // function lvalue
  void (&&r)(int) = cb;
  r(1);
  __CPROVER_assert(hit == 1, "rvalue reference");
  __CPROVER_assert(forward_call(cb) && hit == 2, "forwarding reference");
  __CPROVER_assert(hit != 2, "WRONG (must FAIL)");
}

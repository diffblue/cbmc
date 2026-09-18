extern "C" void __CPROVER_assert(bool, const char *);
template <class Sig> struct fn;
template <class R, class... A> struct fn<R(A...)>
{
  R (*f)(A...);
  fn(R (*g)(A...)) : f(g) {}
  R operator()(A... a) const { return f(a...); }
};
struct hard { int v; };
void bump(hard &h) { h.v += 5; }
void take(fn<void(hard &)> handler, hard &h) { handler(h); }
int main()
{
  hard h{1};
  fn<void(hard &)> f(&bump);
  f(h);
  __CPROVER_assert(h.v == 6, "A: direct construction from a function pointer, pack in the ctor parameter");
  fn<void(hard &)> g = &bump;
  g(h);
  __CPROVER_assert(h.v == 11, "B: copy-initialisation");
  take(&bump, h);
  __CPROVER_assert(h.v == 16, "C: implicit conversion at a call");
  return 0;
}

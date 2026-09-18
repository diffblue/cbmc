extern "C" void __CPROVER_assert(bool, const char *);
#include <functional>
// N5008 [dcl.fct]/3 + [temp.type]: parameter names are not part of a function
// type; `fn<void(hard &hardness)>' and `fn<void(hard &)>' are the same
// specialization.  The named spelling used to produce a distinct, never
// elaborated instance ("member operator got incomplete type on left hand
// side" when calling the handler) -- goto-symex's with_solver_hardness.
template <class Sig> struct fn;
template <class R, class... A> struct fn<R(A...)>
{
  R (*f)(A...);
  fn(R (*g)(A...)) : f(g) {}
  R operator()(A... a) const { return f(a...); }
};
struct hard { int v; };
void bump(hard &h) { h.v += 5; }
static inline void with_hard(hard &h, fn<void(hard &hardness)> handler) { handler(h); }
static inline void with_std(hard &h, std::function<void(hard &hardness)> handler) { handler(h); }
static inline void never_called(hard *p, std::function<void(hard &hardness)> handler)
{
  if(p)
  {
    auto &h = static_cast<hard &>(*p);
    handler(h);
  }
}
int main()
{
  hard h{1};
  with_hard(h, &bump);
  __CPROVER_assert(h.v == 6, "own fn<void(hard &hardness)>");
  with_std(h, [](hard &x) { x.v += 10; });
  __CPROVER_assert(h.v == 16, "std::function<void(hard &hardness)>");
  fn<void(hard &)> same = &bump;
  fn<void(hard &hardness)> &alias = same;
  alias(h);
  __CPROVER_assert(h.v == 21, "the two spellings are one type");
  return 0;
}

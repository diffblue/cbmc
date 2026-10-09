// N5008 [expr.prim.req.compound]/1 + [temp.constr.op]: a
// compound-requirement's return-type-requirement `{ E } -> C<A...>`
// checks C<decltype((E)), A...>; C's body here is a CONJUNCTION of
// type predicates (`__is_same(_Tp,_Up) && __is_same(_Up,_Tp)`, the
// libc++ same_as shape).  template_mapt::apply(exprt) recursed into
// unnamed children AS TYPES, so a predicate nested under `&&` kept
// its parameter names unbound, the concept body failed to typecheck,
// and every such requirement evaluated FALSE (assertion 1 failed;
// the negative cases masked the defect by failing "correctly").
extern "C" void __CPROVER_assert(bool, const char *);
template <class _Tp, class _Up>
concept same_as_ = __is_same(_Tp, _Up) && __is_same(_Up, _Tp);

template <class _Tp>
concept has_self_add = requires(_Tp __t)
{
  {
    __t + __t
    } -> same_as_<_Tp>;
};

struct vec2
{
  int x;
  vec2 operator+(vec2 o) const
  {
    return {x + o.x};
  }
};
struct weird
{
  int operator+(weird) const
  {
    return 0;
  }
};

int main()
{
  __CPROVER_assert(has_self_add<vec2>, "vec2 + vec2 -> vec2");
  __CPROVER_assert(!has_self_add<weird>, "weird + weird -> int, not weird");
  __CPROVER_assert(!has_self_add<void *>, "no + on void*");
  return 0;
}

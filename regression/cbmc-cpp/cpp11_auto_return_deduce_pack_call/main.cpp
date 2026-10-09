// N5008 [dcl.spec.auto]/3-4,11 + [temp.variadic]/4-5: a function template with
// a DEDUCED return type (`auto` / `decltype(auto)`) whose body returns a call
// with a pack expansion, `decltype(auto) impl(seq<I...>) { return add(I...); }`.
// The return type is deduced from the (expanded) return expression.
//
// CORE (was KNOWNBUG): CBMC previously left such a body incomplete ("could not
// fully type-check 'main'") because the eager auto-return type-check ran on the
// unexpanded pack call.  Fixed by expanding the body's call-argument packs (from
// the instance's pack_expr_map) before the eager return-type deduction and body
// type-check.  A trailing return type over the same call
// (`-> decltype(add(I...))`) was already handled
// (cpp11_decltype_return_nontype_pack_call, CORE).
//
// This is the auto/decltype(auto)-return layer used by libstdc++'s std::apply
// and its `__apply_impl` helper.  g++ and clang++ compute the same values.
//
// Non-vacuous: the returned value is a concrete function of the deduced pack
// (3 / 6), which under the old behaviour was never really checked (incomplete
// body).

extern "C" void __CPROVER_assert(int, const char *);

int add(int a, int b)
{
  return a + b;
}

int add3(int a, int b, int c)
{
  return a + b + c;
}

template <int...>
struct seq
{
};

// deduced pack + decltype(auto) return
template <int... I>
decltype(auto) impl(seq<I...>)
{
  return add(I...);
}

// deduced pack + plain auto return
template <int... I>
auto impl3(seq<I...>)
{
  return add3(I...);
}

// explicit pack + auto return
template <int... I>
auto g()
{
  return add(I...);
}

int main()
{
  __CPROVER_assert(impl(seq<1, 2>{}) == 3, "decltype(auto) add(1,2)==3");
  __CPROVER_assert(impl3(seq<1, 2, 3>{}) == 6, "auto add3(1,2,3)==6");
  __CPROVER_assert(g<4, 5>() == 9, "explicit auto add(4,5)==9");
  return 0;
}

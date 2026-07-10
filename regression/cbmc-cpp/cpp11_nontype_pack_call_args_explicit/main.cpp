// N5008 [temp.variadic]/4-5: a NON-type parameter pack expanded as CALL
// ARGUMENTS -- `add(I...)` -- expands to one argument per pack element, both in
// a function-template body and inside a `decltype` return type.  This is the
// call-argument analogue of the type-pack `f(T{}...)` and the value-pack
// `f(args...)` expansions.
//
// CORE (previously mis-handled: the non-type pack's element values were not
// substituted into the call, so `add(I...)` produced a nondeterministic
// result).  Fixed by expanding a non-type call-argument pack from the template
// map's pack_expr_map in both expand_call_argument_packs (decltype operands)
// and the function-template body.  This is the explicitly-argumented core of
// std::apply's `__invoke(f, get<I>(t)...)` helper.
//
// Non-vacuous: under the old behaviour every assertion would read a
// nondeterministic value.

extern "C" void __CPROVER_assert(int, const char *);

int add(int a, int b)
{
  return a + b;
}

int add3(int a, int b, int c)
{
  return a + b + c;
}

// non-type pack in a plain function-template body
template <int... I>
int body()
{
  return add(I...);
}

// non-type pack inside a decltype return type (+ body)
template <int... I>
auto dt() -> decltype(add(I...))
{
  return add(I...);
}

template <int... I>
int body3()
{
  return add3(I...);
}

int main()
{
  __CPROVER_assert(body<1, 2>() == 3, "body: add(1,2)==3");
  __CPROVER_assert(dt<10, 20>() == 30, "decltype-return: add(10,20)==30");
  __CPROVER_assert(body3<1, 2, 3>() == 6, "body: add3(1,2,3)==6");
  return 0;
}

// N5008 [temp.deduct.type] + [temp.variadic]/4-5: a NON-type parameter pack
// DEDUCED from a class-template-id argument (`I` deduced by matching the
// parameter `seq<I...>` against the argument `seq<1,2>`) and then expanded as
// call arguments in the function body (`add(I...)`).
//
// CORE.  Previously the deduced non-type pack recorded only its size, and the
// guessed template arguments collapsed the pack to a single element, so the
// call had the wrong arity / value.  Fixed by (1) recording the deduced
// non-type pack's element values in pack_expr_map during guess_template_args,
// (2) expanding that pack to its full set of values in the guessed template
// arguments, and (3) expanding a non-type call-argument pack in the body.  This
// is the index_sequence-style deduction at the core of std::apply's
// `__invoke(f, get<I>(t)...)`.
//
// Non-vacuous: under the old behaviour the assertions would read a
// nondeterministic / wrong value.

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

template <int... I>
int impl(seq<I...>)
{
  return add(I...);
}

template <int... I>
int impl3(seq<I...>)
{
  return add3(I...);
}

int main()
{
  __CPROVER_assert(impl(seq<1, 2>{}) == 3, "deduced add(1,2)==3");
  __CPROVER_assert(impl3(seq<4, 5, 6>{}) == 15, "deduced add3(4,5,6)==15");
  return 0;
}

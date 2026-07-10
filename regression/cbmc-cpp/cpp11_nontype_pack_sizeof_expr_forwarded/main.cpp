// N5008 [temp.variadic]/4-5: a pack expansion whose pattern is a `sizeof`
// unary-expression, `sizeof(Us)...`, forwarded from an enclosing function
// template, expands to one element per pack member.
//
// `box<sizeof(Us)...>::n` (with `box<int... Vs>` and `n = sizeof...(Vs)`)
// evaluated inside a function template `chk` that forwards its own pack `Us`
// yields the correct element count.  This previously collapsed to a single
// element (a non-type pack -- here the sizeof values -- was scalar-bound to its
// first argument in the template map).  Now fixed.
//
// CORE (was KNOWNBUG cpp11_nontype_pack_sizeof_expr_forwarded).  Non-vacuous:
// under the old collapse the count would be 1, not the number of arguments.

extern "C" void __CPROVER_assert(int, const char *);

template <int... Vs>
struct box
{
  static constexpr int n = sizeof...(Vs);
};

template <class... Us>
constexpr int chk(Us...)
{
  return box<sizeof(Us)...>::n;
}

int main()
{
  __CPROVER_assert(chk() == 0, "0 forwarded elements");
  __CPROVER_assert(chk((char)1) == 1, "1 forwarded element");
  __CPROVER_assert(chk((char)1, (char)2) == 2, "2 forwarded elements");
  __CPROVER_assert(chk((char)1, (char)2, (char)3) == 3, "3 forwarded elements");
  return 0;
}

// Reproducer for the MSVC `<map>` _Try_emplace multi-element braced
// return failure.  The key ingredient is that the non-POD return
// class type has MULTIPLE overloaded constructors (including SFINAE-
// guarded variadic ones), so CBMC's implicit_typecast path — which
// tries one-arg conversions — doesn't find a match and falls through.
//
// Per [stmt.return]/3 (C++11), `return { a, b };` in a function whose
// return type is a class type must perform list-initialization of a
// temporary of the return type with the braced-init-list.
//
// The fix in cpp_typecheck_code.cpp:typecheck_return adds explicit
// handling for multi-element braced returns to non-POD class types:
// construct the temporary via new_temporary/cpp_constructor which
// does proper [over.match.list] overload resolution.

// Variadic helpers used by the SFINAE-guarded constructor to make
// the pair ambiguous-looking to the naive conversion path.
template <class...>
using void_t = void;

template <bool, class T = void>
struct enable_if
{
};
template <class T>
struct enable_if<true, T>
{
  using type = T;
};

template <bool B, class T = void>
using enable_if_t = typename enable_if<B, T>::type;

template <class T, class U>
struct is_constructible
{
  static constexpr bool value = true;
};

struct my_pair
{
  int *first;
  bool second;

  // Regular two-argument constructor (the one that should be picked).
  my_pair(int *a, bool b) : first(a), second(b)
  {
  }

  // Templated SFINAE-guarded constructor to mimic MSVC's
  //   template <class U1, class U2, enable_if_t<...>> pair(U1&&, U2&&);
  // With this present, the naive
  // implicit-typecast-from-initializer-list path doesn't find a
  // unique match.
  template <
    class U1,
    class U2,
    enable_if_t<
      is_constructible<int *, U1>::value && is_constructible<bool, U2>::value,
      int> = 0>
  my_pair(U1 &&a, U2 &&b) : first(static_cast<int *>(a)), second(bool(b))
  {
  }
};

my_pair make_via_brace_return(int *p, bool b)
{
  return {p, b};
}

int main()
{
  int x = 17;
  my_pair r = make_via_brace_return(&x, true);
  __CPROVER_assert(
    *r.first == 17 && r.second == true,
    "multi-element braced return picks correct ctor");
  return 0;
}

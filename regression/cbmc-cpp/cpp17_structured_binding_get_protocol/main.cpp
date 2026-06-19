// [dcl.struct.bind]/4: when std::tuple_size<E> is a complete type with a member
// `value`, a structured binding `auto [a, b] = e;` binds each name to get<i>(e)
// (with type std::tuple_element<i, E>::type), NOT to the i-th data member.  For
// std::tuple the internal data-member order differs from the get<i> order, so
// decomposing by data members (as CBMC currently does) binds the wrong members.
// Here the get-protocol order is deliberately the reverse of the declared
// data-member order to capture the bug without headers.

namespace std
{
template <class T>
struct tuple_size;
template <unsigned I, class T>
struct tuple_element;
} // namespace std

struct Pair
{
  long stored_second; // first in declaration/memory order
  int stored_first;   // second in declaration/memory order
};

// get<0> yields the logical first element (stored_first), get<1> the second
template <unsigned I>
auto get(const Pair &p)
{
  if constexpr(I == 0)
    return p.stored_first;
  else
    return p.stored_second;
}

namespace std
{
template <>
struct tuple_size<Pair>
{
  static const unsigned value = 2;
};
template <>
struct tuple_element<0, Pair>
{
  using type = int;
};
template <>
struct tuple_element<1, Pair>
{
  using type = long;
};
} // namespace std

int main()
{
  Pair p{2, 1}; // stored_second = 2, stored_first = 1
  auto [a, b] = p; // a = get<0>(p) = 1, b = get<1>(p) = 2
  __CPROVER_assert(a == 1, "structured binding 0 uses get<0>");
  __CPROVER_assert(b == 2, "structured binding 1 uses get<1>");
  return 0;
}

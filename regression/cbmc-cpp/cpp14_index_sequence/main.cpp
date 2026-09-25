// C++17 std::apply-like with index_sequence
template <typename T, T... Is>
struct integer_sequence
{
};
template <unsigned long... Is>
using index_sequence = integer_sequence<unsigned long, Is...>;
template <typename F, typename Tuple, unsigned long... Is>
auto apply_impl(F f, Tuple &t, index_sequence<Is...>)
{
  return f(t.data[Is]...);
}
int main()
{
  // Just test that index_sequence compiles
  index_sequence<0, 1, 2> seq;
  (void)seq;
  return 0;
}

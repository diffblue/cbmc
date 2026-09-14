extern "C" void __CPROVER_assert(bool, const char *);
template <class _Tp, _Tp... _Ip>
struct integer_sequence
{
  static constexpr int size = sizeof...(_Ip);
};
template <unsigned long _Np>
using make_index_sequence =
  __make_integer_seq<integer_sequence, unsigned long, _Np>;
template <class>
struct sum_of;
template <unsigned long... _Ip>
struct sum_of<integer_sequence<unsigned long, _Ip...>>
{
  static constexpr int value = (static_cast<int>(_Ip) + ... + 0);
};
int main()
{
  __CPROVER_assert(
    sum_of<make_index_sequence<3>>::value == 3, "0+1+2 via __make_integer_seq");
  return 0;
}

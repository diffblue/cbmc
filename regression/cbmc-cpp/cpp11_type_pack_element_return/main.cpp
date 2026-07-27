// Clang's builtin alias template __type_pack_element<N, Ts...> naming
// the N-th pack element, used as a function template's RETURN TYPE
// (the shape of libc++'s std::get<I>(tuple&), whose return type is
// tuple_element<_Ip, tuple<_Tp...>>::type& = __type_pack_element<_Ip,
// _Tp...>&).  During overload resolution the return type is
// substituted with the deduced arguments ([temp.deduct]/5); CBMC
// fails to evaluate the builtin there and rejects the only candidate
// ("found no match for symbol 'get_'").  __type_pack_element in a
// LOCAL typedef inside the body works, and evaluating it as a
// standalone type works -- only the return-type substitution path is
// affected.  libc++ mode only (the builtin is clang-gated); this is
// the residual blocking cpp11_tuple_basic / cpp11_libcxx_tuple after
// the _BaseT chain was fixed.
extern "C" void __CPROVER_assert(bool, const char *);
typedef unsigned long size_t_;

template <class... Ts>
struct tuplet
{
  int head = 41;
};

template <size_t_ I, class... Ts>
__type_pack_element<I, Ts...> &get_(tuplet<Ts...> &t)
{
  return t.head;
}

int main()
{
  tuplet<int, long> t;
  __CPROVER_assert(get_<0>(t) == 41, "__type_pack_element as return type");
  return 0;
}

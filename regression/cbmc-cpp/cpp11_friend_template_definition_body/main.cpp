// N5008 [temp.over.link]/6 + [class.friend]/1 + [temp.friend]/1: an
// in-class FRIEND declaration of a function template and its later
// namespace-scope DEFINITION -- spelled with different template
// parameter names -- declare the SAME entity, and friendship extends
// to that template's specializations.  CBMC materialized TWO template
// symbols (the identifier embeds the parameter spelling): calls
// resolved to the friend's bodiless one ("no body for callee get"),
// and the definition's body failed the access check on the private
// member.  The exact libc++ <tuple> get shape.
extern "C" void __CPROVER_assert(bool, const char *);
typedef unsigned long size_t;
template <size_t, class> struct tuple_element;
template <class... _Tp> class tuple;
template <size_t _Ip, class... _Tp>
struct tuple_element<_Ip, tuple<_Tp...>> {
  typedef int type;
};
template <class... _Tp> class tuple {
  int __x_;
  template <size_t _Jp, class... _Up>
  friend typename tuple_element<_Jp, tuple<_Up...>>::type &
  get(tuple<_Up...> &) noexcept;

public:
  tuple(int v) : __x_(v) {}
};
template <size_t _Ip, class... _Tp>
inline typename tuple_element<_Ip, tuple<_Tp...>>::type &
get(tuple<_Tp...> &__t) noexcept {
  return __t.__x_;
}
int main() {
  tuple<int, int> t(5);
  __CPROVER_assert(get<0>(t) == 5, "friend get");
  return 0;
}

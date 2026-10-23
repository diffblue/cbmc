extern "C" void __CPROVER_assert(bool, const char *);
template <class T>
struct ident
{
  using type = T;
};
template <class T>
ident<T> *as_ptr()
{
  return nullptr;
}
template <class... A>
ident<char[sizeof...(A)]> count(A...);
template <class... Ts>
struct L
{
};
template <class>
struct Y;
// N5008 [temp.variadic]/5, [expr.prim.id.qual]/1: a pack expansion in the
// operand of a decltype-specifier that is a nested-name-specifier expands
// like any other (the MSVC STL's _Meta_at_)
template <class... Ts>
struct Y<L<Ts...>>
{
  using type = typename decltype(count(as_ptr<Ts>()...))::type;
};
int main()
{
  __CPROVER_assert(
    sizeof(Y<L<int, int, double>>::type) == 3, "one argument per element");
  __CPROVER_assert(
    sizeof(Y<L<int, int, double>>::type) == 1, "WRONG (must FAIL)");
  return 0;
}

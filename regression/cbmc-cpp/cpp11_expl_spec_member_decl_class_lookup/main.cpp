// N5008 [basic.lookup.unqual]/5 + [dcl.fct]/6: for a member declared
// outside its class -- here the explicit-specialization DECLARATION
// `template <> void messages<char>::do_close(catalog) const;`
// (libstdc++'s <locale>/<regex> shape) -- names after the
// declarator-id are looked up in the member's class, including
// inherited members ([class.member.lookup]).  The [dcl.ambig.res]/1
// re-disambiguation probed `catalog` at NAMESPACE scope, missed the
// class typedef, and re-interpreted the declaration as a void
// variable with a parenthesized initializer ("void-typed symbol not
// permitted").  A trailing cv-qualifier also forces the function
// interpretation outright ([dcl.fct]/6: only function declarators
// carry one).
extern "C" void __CPROVER_assert(bool, const char *);
struct messages_base
{
  typedef int catalog;
};
template <typename> struct messages : messages_base
{
  void do_close(catalog) const;
};
template <> void messages<char>::do_close(catalog) const;
int main()
{
  __CPROVER_assert(sizeof(messages_base::catalog) == sizeof(int), "converts");
  return 0;
}

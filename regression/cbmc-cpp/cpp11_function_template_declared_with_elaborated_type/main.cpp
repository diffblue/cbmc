// N5008 [dcl.type.elab]/3, [temp.over.link]/6: `template <class T> int
// g(const struct S &)' declared before S is defined, and the definition
// `template <class T> int g(const S &)', declare the same function template
// -- `struct S' and `S' name the same class.  The front end compared the
// parameter spellings, made the definition a second template, and the call
// g<int>(s) used the bodiless declaration (a nondeterministic result).
// Found while reducing libstdc++'s friend `__try_use_facet'.
extern "C" void __CPROVER_assert(bool, const char *);
// N5008 [basic.scope.pdecl]/7.2, [dcl.type.elab]/3: `struct S' first named
// in a parameter-declaration of a function declared at namespace scope
// declares S in that namespace; the later definition is the same class
int f(struct S *s);
template <typename T>
int g(const struct S &s);
struct S
{
  int v = 5;
};
int f(S *s)
{
  return s->v;
}
template <typename T>
int g(const S &s)
{
  return s.v + 1;
}
int main()
{
  S s;
  __CPROVER_assert(f(&s) == 5, "function");
  __CPROVER_assert(g<int>(s) == 6, "function template");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}

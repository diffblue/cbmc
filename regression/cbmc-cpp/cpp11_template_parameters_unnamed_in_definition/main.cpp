// N5008 [temp.param]/15, [temp.local]/7: a template parameter's name is
// local to its template-head; a default argument naming an earlier
// parameter of a declaration (`class = C') applies to a definition whose
// parameters are unnamed
extern "C" void __CPROVER_assert(bool, const char *);
template <class C, class = C>
struct S;
template <class, class>
struct S
{
  int k;
};
int main()
{
  S<char> s;
  s.k = 1;
  __CPROVER_assert(s.k == 1, "unnamed parameters in the definition");
  __CPROVER_assert(s.k == 0, "WRONG (must FAIL)");
}

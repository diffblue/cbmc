// The front end does not declare tag_t in the enclosing namespace when it is
// first named in an alias template; the defaulted template argument `=
// tag_t' then fails and box's constructor template is not viable ("found no
// match for symbol 'box'").  Found as a cvise artifact in round 185.
extern "C" void __CPROVER_assert(bool, const char *);
// N5008 [dcl.type.elab]/3 (with [basic.scope.pdecl]): `struct tag_t' first
// named in the alias template's type-id declares tag_t in the enclosing
// namespace, so it is usable after the alias template
template <bool>
using pick = struct tag_t;
struct box
{
  int v = 0;
  box() = default;
  template <typename U, typename = tag_t>
  box(U u) : v(u)
  {
  }
};
int main()
{
  box b = box(5);
  tag_t *p = nullptr;
  pick<true> *q = p;
  __CPROVER_assert(
    b.v == 5 && q == nullptr, "elaborated type in alias template");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}

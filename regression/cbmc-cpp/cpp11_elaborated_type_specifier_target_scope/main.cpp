// N5008 [dcl.type.elab]/3: an elaborated-type-specifier `class-key
// identifier' whose identifier lookup does not find declares it as a
// class-name of the nearest enclosing namespace or block scope: from an
// alias template, a member declaration, a parameter declaration, and a block.
extern "C" void __CPROVER_assert(bool, const char *);
namespace N
{
template <bool>
using pick = struct tag;
struct holder
{
  struct inner_ref *p;
};
void take(struct param_t *);
} // namespace N
struct N::tag
{
  int v;
};
struct N::inner_ref
{
  int w;
};
struct N::param_t
{
  int u;
};
void N::take(N::param_t *q)
{
  q->u = 4;
}
int block()
{
  struct local *p = nullptr;
  struct local
  {
    int x;
  };
  local l{7};
  p = &l;
  return p->x;
}
int main()
{
  N::tag t{1};
  N::pick<false> *a = &t;
  N::inner_ref r{2};
  N::holder h{&r};
  N::param_t q{0};
  N::take(&q);
  __CPROVER_assert(a->v == 1, "alias in namespace");
  __CPROVER_assert(h.p->w == 2, "member declarator in namespace");
  __CPROVER_assert(q.u == 4, "parameter in namespace");
  __CPROVER_assert(block() == 7, "block scope");
  __CPROVER_assert(a->v == 2, "WRONG (must FAIL)");
}

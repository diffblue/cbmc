// N5008 [class.access.base]/4-5: a base class B of N is accessible at a
// point R if R occurs in a member or FRIEND of class N; the
// derived-to-base conversion is then permitted regardless of the
// base-specifier's access.  libstdc++'s _Hashtable derives PRIVATELY
// from _Hashtable_alloc and befriends its _Insert mixins, whose members
// convert _Hashtable& to _Hashtable_alloc& (constructing an _AllocNode)
// -- rejecting the conversion silently dropped the mixin member's body
// and made unordered_set::insert a no-op.
//
// The front end used to judge the conversion only from the scope
// current at binding time (the constructor's own class), missing the
// caller's friendship.
extern "C" void __CPROVER_assert(bool, const char *);

struct alloc_base
{
  int alloc()
  {
    return 7;
  }
};

struct node_gen
{
  alloc_base &b;
  node_gen(alloc_base &bb) : b(bb)
  {
  }
  int use()
  {
    return b.alloc();
  }
};

struct table : private alloc_base
{
  friend struct helper;
};

struct helper
{
  int go(table &t)
  {
    node_gen n(t); // derived-to-PRIVATE-base: OK, helper is a friend
    return n.use();
  }
};

int main()
{
  table t;
  helper h;
  __CPROVER_assert(h.go(t) == 7, "friend may convert to private base");
  return 0;
}

// N5008 [stmt.pre]/6: a name introduced by a condition declaration is
// in scope from its point of declaration until the end of the
// statement's SUBSTATEMENTS; it is not visible in the rest of the
// enclosing block, so redeclaring the same name after the statement is
// well-formed.  (libstdc++'s _Hashtable::_M_insert_unique declares
// `__node_ptr __node` in an if-condition and a `_Scoped_node __node`
// local after it; the leaked condition name made the member's body
// fail conversion -- "already declared with different type" -- and the
// function was silently dropped.)
extern "C" void __CPROVER_assert(bool, const char *);

struct P
{
  int a;
};

int f(int x)
{
  if(int v = x)
    return v + 1;
  P v = {5}; // same name, different type: OK per [stmt.pre]/6
  return v.a;
}

int main()
{
  __CPROVER_assert(f(3) == 4, "condition value used in branch");
  __CPROVER_assert(f(0) == 5, "redeclaration after the if");
  return 0;
}

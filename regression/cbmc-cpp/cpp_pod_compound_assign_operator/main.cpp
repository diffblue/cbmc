// N5008 [expr.ass]/2-7: there is no built-in compound assignment for a class
// type; `a @= b` on a class type calls the overloaded operator@=, even when the
// class is a POD (a user-defined operator does not make the class non-POD).
//
// KNOWNBUG: CBMC took the C built-in assignment path for a POD class and
// rejected the compound assignment with
// "assignment 'assign_shr' not defined for types 'struct Size' ...".
struct Size
{
  unsigned long v = 0;
  Size &operator>>=(const Size &r)
  {
    v >>= r.v;
    return *this;
  }
};
int main()
{
  Size a;
  a.v = 16;
  Size b;
  b.v = 2;
  a >>= b; // POD class, user operator>>=
  __CPROVER_assert(a.v == 4, "16 >>= 2 yields 4 via POD operator>>=");
  return 0;
}

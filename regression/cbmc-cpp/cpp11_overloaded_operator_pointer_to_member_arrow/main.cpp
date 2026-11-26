// N5008 [over.match.oper]/3: for `a->*b' with a left operand of class type
// the overloaded `operator->*' (member and non-member candidates) takes
// part in overload resolution; the built-in applies to a pointer to a
// class and a pointer to member of it ([expr.mptr.oper]).  Only `.*' is
// not overloadable ([over.oper.general]/3).  A user-declared operator->*
// (the smart-pointer idiom) was never found: `w->*&Idx::other' failed
// with "pointer-to-member type error".
extern "C" void __CPROVER_assert(bool, const char *);
struct Idx
{
  int base;
  int other;
  int operator->*(int Idx::*pm) const
  {
    return this->*pm + 1000;
  }
};
struct Wrap
{
  Idx *p;
  template <class M>
  M &operator->*(M Idx::*pm) const
  {
    return p->*pm;
  }
};
int main()
{
  Idx i{18, 3};
  __CPROVER_assert(
    (i->*&Idx::base) == 1018, "user operator->* overloads the built-in");
  __CPROVER_assert((i->*&Idx::other) == 1003, "user operator->* second member");
  Wrap w{&i};
  w->*&Idx::other = 9;
  __CPROVER_assert(i.other == 9, "smart-pointer style operator->* template");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}

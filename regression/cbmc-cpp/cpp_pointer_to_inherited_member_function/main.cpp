extern "C" void __CPROVER_assert(bool, const char *);
struct B
{
  int in(int k) const
  {
    return k + 1;
  }
};
struct D : B
{
};
// [expr.unary.op]/3.1: &D::in names B::in, a member of B, so its type is
// int (B::*)(int) const; [conv.mem]/2 converts it to int (D::*)(int) const
// (libstdc++'s __str_codecvt_in: `_ConvFn __fn = &codecvt<...>::in;')
typedef int (D::*F)(int) const;
int main()
{
  F f = &D::in;
  int (B::*g)(int) const = &D::in;
  D d;
  __CPROVER_assert((d.*f)(1) == 2, "converted to the derived class");
  __CPROVER_assert((d.*g)(2) == 3, "pointer to member of the base");
  __CPROVER_assert((d.*f)(1) != 2, "WRONG (must FAIL)");
}

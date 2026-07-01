// N5008 [temp.param]/6, [temp.arg.nontype]/2: a non-type template parameter may
// have pointer type, and its argument is the address of an object with static
// storage duration.  rc<&g> binds p to &g, so r.val() == g.x == 5.  g++/clang++
// agree.  This verifies pointer (not just reference) non-type parameters keep
// their pointer type and their address argument's object identity.
// assertion.2 must FAIL, proving non-vacuity.

extern "C" void __CPROVER_assert(int, const char *);

struct S
{
  int x;
};
static S g = {5};

template <S *p>
struct rc
{
  int val() const
  {
    return p->x;
  }
};

int main()
{
  rc<&g> r;
  __CPROVER_assert(r.val() == 5, "pointer NTTP dereferences g");
  __CPROVER_assert(r.val() != 5, "WRONG must FAIL");
  return 0;
}

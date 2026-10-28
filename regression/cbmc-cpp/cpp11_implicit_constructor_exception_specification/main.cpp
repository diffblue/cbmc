// N5008 [except.spec]/6: an implicitly-declared constructor of X is
// potentially-throwing if and only if a constructor it invokes for a
// potentially constructed subobject is; [expr.unary.noexcept]/3.
extern "C" void __CPROVER_assert(bool, const char *);

struct Throws
{
  Throws()
  {
  }
  Throws(const Throws &)
  {
  }
};
struct Holder
{
  Throws t;
};
struct Plain
{
  int i;
};

int main()
{
  Holder h;
  Plain p{1};
  __CPROVER_assert(!noexcept(Holder()), "implicit default constructor");
  __CPROVER_assert(!noexcept(Holder(h)), "implicit copy constructor");
  __CPROVER_assert(noexcept(Plain(p)), "trivial copy constructor");
  __CPROVER_assert(noexcept(Holder(h)), "WRONG (must FAIL)");
  return 0;
}

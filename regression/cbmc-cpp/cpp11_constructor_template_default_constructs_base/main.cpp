// N5008 [class.base.init]/9.3: a base class not named in a constructor's
// mem-initializer-list is default-initialized -- also by a constructor
// template's specializations
extern "C" void __CPROVER_assert(bool, const char *);
struct leaf
{
  int value;
  leaf() : value(7)
  {
  }
};
struct impl : leaf
{
  template <class U>
  impl(U)
  {
  }
  impl() = default;
};
int main()
{
  impl d;
  __CPROVER_assert(d.value == 7, "non-template constructor");
  impl t(1);
  __CPROVER_assert(t.value == 7, "constructor template");
  __CPROVER_assert(t.value == 8, "WRONG (must FAIL)");
}

// N5008 [class.dtor]/7-8: E's implicit destructor destroys its base D,
// whose two A subobjects (through B and through C) are destroyed by D's
// destructor; [class.mi]/3 makes A an ambiguous base of D only for
// conversions, which E's destructor does not need.
extern "C" void __CPROVER_assert(bool, const char *);
int destroyed = 0;
struct V
{
  virtual ~V() = default;
};
struct A : virtual V
{
  ~A()
  {
    ++destroyed;
  }
};
struct B : A
{
};
struct C : A
{
};
struct D : B, C
{
};
struct E : D
{
};
int main()
{
  {
    E e;
  }
  __CPROVER_assert(destroyed == 2, "both A subobjects destroyed");
  __CPROVER_assert(destroyed == 1, "WRONG (must FAIL)");
}

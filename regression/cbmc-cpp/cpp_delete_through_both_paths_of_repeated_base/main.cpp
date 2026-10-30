// N5008 [expr.delete]/3, /6: an E object deleted through either of the B
// and C base pointers is destroyed as an E ([class.dtor]/14: virtual
// destructor), and its storage is deallocated at the address the
// allocation returned.  E's base D has two A subobjects ([class.mi]/3).
extern "C" void __CPROVER_assert(bool, const char *);
int destroyed_a = 0, destroyed_e = 0;
struct V
{
  virtual ~V() = default;
};
struct A : V
{
  ~A()
  {
    ++destroyed_a;
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
  ~E()
  {
    ++destroyed_e;
  }
};
int main()
{
  B *b = new E;
  delete b;
  __CPROVER_assert(destroyed_e == 1 && destroyed_a == 2, "through B");
  C *c = new E;
  delete c;
  __CPROVER_assert(destroyed_e == 2 && destroyed_a == 4, "through C");
  __CPROVER_assert(destroyed_a == 3, "WRONG (must FAIL)");
}

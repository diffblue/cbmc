// N5008 [class.base.init]/7 + [dcl.init.list]/3.4: a braced
// mem-initializer aggregate-initializes a POD base subobject
// member-wise; a single same-type element is copy-initialization
// ([dcl.init.list]/3.2); trailing members without initializers are
// value-initialized ([dcl.init.aggr]/5).  The POD-base lowering used
// to assign the bare operand (rejecting Base{42}) and drop
// multi-operand lists (nondet base).
extern "C" void __CPROVER_assert(bool, const char *);

struct Base
{
  int x;
  int y;
};

struct D1 : Base
{
  D1() : Base{42}
  {
  }
};

struct D2 : Base
{
  D2() : Base{1, 2}
  {
  }
};

struct D3 : Base
{
  D3(Base b) : Base(b)
  {
  }
};

int main()
{
  D1 a;
  __CPROVER_assert(a.x == 42 && a.y == 0, "single element + value-init");
  D2 b;
  __CPROVER_assert(b.x == 1 && b.y == 2, "member-wise");
  Base src;
  src.x = 7;
  src.y = 9;
  D3 c(src);
  __CPROVER_assert(c.x == 7 && c.y == 9, "same-type copy");
}

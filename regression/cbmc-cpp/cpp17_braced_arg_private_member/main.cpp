extern "C" void __CPROVER_assert(bool, const char *);

// N5008 [class.access.general]/5: access control is applied uniformly;
// a member function of guardt may name its own private member
// wherever an expression may appear -- including inside a
// braced-init-list ARGUMENT to a constructor call.  CBMC used to
// judge the access from the wrong scope for exactly this shape
// ("member 'guardt::expr' is not accessible (private)"); the same
// access as a plain argument works.  The shape of guard_exprt::add's
// `and_exprt a({this->expr})`, which blocks dog-fooding
// src/analyses/guard_expr.cpp.
// g++/clang++ accept and verify at runtime.

struct wrapt
{
  int inner;
  explicit wrapt(const int &i) : inner(i)
  {
  }
};

class guardt
{
public:
  void bump();
  int get() const
  {
    return expr;
  }

private:
  int expr = 3;
};

void guardt::bump()
{
  wrapt w({this->expr}); // member access inside a braced-init argument
  expr = w.inner + 1;
}

int main()
{
  guardt g;
  g.bump();
  __CPROVER_assert(g.get() == 4, "private member usable in braced arg");
  return 0;
}

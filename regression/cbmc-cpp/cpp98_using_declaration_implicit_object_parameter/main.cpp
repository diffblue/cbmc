extern "C" void __CPROVER_assert(bool, const char *);

// [over.match.funcs.general]/4: a member function nominated by a
// using-declaration is a member of the derived class for the type of its
// implicit object parameter
struct base
{
  int f() const
  {
    return 1;
  }
  int f(int) const
  {
    return 2;
  }
};

struct derived : base
{
  using base::f;
  int f(double) const
  {
    return 3;
  }
  int g() const
  {
    return f(1);
  }
};

// without the using-declaration, derived::f hides base::f
struct hiding : base
{
  int f(double) const
  {
    return 4;
  }
};

// [namespace.udecl]/14: a member function with the same parameter-type-list
// and cv-qualification hides the one the using-declaration brings in
// (libstdc++'s _List_node_header::_M_base)
struct node_base
{
  int m()
  {
    return 5;
  }
  int m() const
  {
    return 6;
  }
};

struct node_header : node_base
{
  using node_base::m;
  int m()
  {
    return 7;
  }
  int n()
  {
    return this->m();
  }
};

int main()
{
  derived d;
  const derived &cd = d;
  hiding h;
  __CPROVER_assert(
    d.f() == 1 && d.f(1) == 2 && d.f(1.0) == 3 && cd.f(1) == 2 && d.g() == 2,
    "using-declaration");
  __CPROVER_assert(h.f(1) == 4, "hidden");
  node_header nh;
  const node_header &cnh = nh;
  __CPROVER_assert(
    nh.m() == 7 && cnh.m() == 6 && nh.n() == 7, "hidden by a redeclaration");

  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}

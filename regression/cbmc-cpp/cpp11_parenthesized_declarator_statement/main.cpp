// N5008 [stmt.ambig]/1: a statement that can be a declaration is a
// declaration; `T(x);' declares x with a parenthesised declarator
// ([dcl.decl.general]: `( ptr-declarator )'), as do `int (i) = k;' and
// `int (*p) = &i;'.  The parser took `T(x)' for a call (a functional cast
// with an unknown argument: "symbol 'x' is unknown").  [class.mem.general]/7:
// a member function body is a complete-class context, so `T' may be a
// nested class declared LATER in the class -- unknown to the parser, the
// statement is turned into the declaration by the type checker (libstdc++
// 16's `__location_type (__trans_tmp_3);' in _Hashtable::find).
extern "C" void __CPROVER_assert(bool, const char *);
struct Known
{
  int v;
};
struct T
{
  int v;
  T() : v(7)
  {
  }
  explicit T(int x) : v(x)
  {
  }
  int get() const
  {
    return v;
  }
};
int declarations(int k)
{
  Known(kn); // Known kn;
  kn.v = k;
  T(t);         // T t;
  int(i) = k;   // int i = k;
  T(u)(k);      // T u(k);
  int(*p) = &i; // int *p = &i;
  return (T(k)).get() + t.v + i + u.v + *p + kn.v;
}
struct NT
{
  int find(int k) const
  {
    loc_t(loc); // loc_t loc; -- loc_t is declared below
    loc.v = k;
    return loc.v;
  }
  struct loc_t
  {
    int v;
  };
};
template <class X>
struct TT
{
  auto find(const int k) const -> int
  {
    __location_type(__trans_tmp_3);
    __trans_tmp_3.v = k;
    return __trans_tmp_3.v;
  }
  auto count(const int k) const -> long
  {
    return find(k); // a member function call, not a declaration
  }
  struct __location_type
  {
    int v;
  };
};
int main()
{
  __CPROVER_assert(declarations(2) == 2 + 7 + 2 + 2 + 2 + 2, "declarations");
  NT n;
  __CPROVER_assert(n.find(3) == 3, "nested class declared later");
  TT<int> t;
  __CPROVER_assert(t.count(4) == 4, "template, nested class declared later");
  __CPROVER_assert(t.count(4) == 5, "WRONG (must FAIL)");
}

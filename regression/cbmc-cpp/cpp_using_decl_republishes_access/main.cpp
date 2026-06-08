#include <cassert>

// [namespace.udecl]/19: a using-declaration republishes an inherited
// member with the access of the using-declaration (independent of the
// member's access in the base), and -- through public derivation --
// that access propagates to further-derived classes.  This mirrors
// CBMC's own expr.h idiom (binary_exprt: `using exprt::op0;`).

struct base
{
protected:
  int v;
  int get() const { return v; }

public:
  void set(int x) { v = x; }
};

struct mid : base
{
public:
  using base::get; // republish protected get() as public
};

struct leaf : mid
{
};

int call_mid(const mid &m)
{
  return m.get(); // direct republish
}

int call_leaf(const leaf &l)
{
  return l.get(); // republished access inherited through derivation
}

int main()
{
  leaf l;
  l.set(42);
  assert(call_mid(l) == 42);
  assert(call_leaf(l) == 42);
}

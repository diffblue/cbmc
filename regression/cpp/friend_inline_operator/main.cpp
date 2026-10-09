// Friend functions defined inside a class body must be visible
// in the enclosing namespace via argument-dependent lookup.

struct Base
{
  int x;

  friend bool operator<(const Base &a, const Base &b)
  {
    return a.x < b.x;
  }

  friend bool operator>(const Base &a, const Base &b)
  {
    return b < a;
  }

  friend bool less_than(const Base &a, const Base &b)
  {
    return a.x < b.x;
  }
};

bool test_op(const Base &a, const Base &b)
{
  return a < b;
}

bool test_fn(const Base &a, const Base &b)
{
  return less_than(a, b);
}

// Friend function body should see class-scope typedefs
struct Iter
{
  typedef int diff_type;
  int pos;

  friend Iter operator+(const Iter &x, diff_type n)
  {
    diff_type d = n;
    Iter tmp = x;
    tmp.pos += d;
    return tmp;
  }
};

int main()
{
  Base a, b;
  a.x = 1;
  b.x = 2;
  bool r1 = test_op(a, b);
  bool r2 = test_fn(a, b);

  // Friend function body can access class-scope typedefs
  Iter it;
  it.pos = 0;
  Iter it2 = it + 3;

  return 0;
}

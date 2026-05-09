// Per [class.copy.ctor]/1,7 and [class.copy.ctor]/8,9:
//
// Behaviours checked:
//  * the implicitly-declared copy constructor (=default) copies each
//    subobject;
//  * user-defined copy constructor correctly initialises members;
//  * presence of a user-defined copy constructor suppresses the move
//    constructor being implicitly generated for a type with move-only
//    members — but here we verify the positive: a type with only a
//    copy constructor is still copyable.

struct payload
{
  int x;
  int y;
};

struct wrapper
{
  payload p;
  // implicit copy constructor: copies p subobject.
};

struct counting
{
  static int copy_count;
  int v;
  counting(int v_) : v(v_)
  {
  }
  counting(const counting &other) : v(other.v)
  {
    ++copy_count;
  }
};

int counting::copy_count = 0;

int main()
{
  // Implicit copy constructor.
  wrapper w1;
  w1.p.x = 7;
  w1.p.y = 42;
  wrapper w2 = w1;
  __CPROVER_assert(w2.p.x == 7, "implicit copy copied .p.x");
  __CPROVER_assert(w2.p.y == 42, "implicit copy copied .p.y");

  // User-defined copy constructor runs on copy-init.
  counting a(5);
  counting b = a;
  __CPROVER_assert(b.v == 5, "user copy ctor copied v");
  __CPROVER_assert(
    counting::copy_count == 1, "user copy ctor ran exactly once");

  // Another copy runs the user-defined ctor again.
  counting c = b;
  __CPROVER_assert(c.v == 5, "second copy preserves value");
  __CPROVER_assert(
    counting::copy_count == 2, "user copy ctor ran twice after two copies");

  return 0;
}

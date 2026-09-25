// Per [expr.new]/24 and [expr.delete]/6: for a non-array new of
// class type T(args), the constructor is invoked on the newly
// allocated object, and delete invokes the destructor.
//
// The array variants have two known issues in CBMC (this file is
// the KNOWNBUG case):
//
//  1. `new T[N]` does not run T's default constructor for each
//     element.  ctor_count stays 0.
//  2. `new T[N]{...}` (braced-init-list initialising array new)
//     crashes with an invariant violation in std_expr.h: op0()
//     Precondition: operands().size() >= 1.
//
// This test exercises the default-initialising array-new form.

struct counted
{
  static int ctor_count;
  static int dtor_count;
  int v;
  counted() : v(0)
  {
    ++ctor_count;
  }
  ~counted()
  {
    ++dtor_count;
  }
};

int counted::ctor_count = 0;
int counted::dtor_count = 0;

int main()
{
  counted *arr = new counted[3];
  __CPROVER_assert(
    counted::ctor_count == 3, "array new ran default ctor 3 times");
  delete[] arr;
  __CPROVER_assert(
    counted::dtor_count == 3, "array delete[] ran 3 destructors");
  return 0;
}

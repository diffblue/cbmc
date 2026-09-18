extern "C" void __CPROVER_assert(bool, const char *);
// Every class is laid out with the ABI's alignment padding ([class.mem],
// [basic.align], [expr.sizeof]/2: sizeof includes padding), as g++/clang do
// on x86-64 (System V / Itanium C++ ABI).
struct A { char c; int i; };
struct B { char c; double d; char e; };
union U { char c[5]; int i; };
struct C { char c; U u; short s; };
struct L { char a; };
struct BF { char c; int b : 3; char d; };
struct AL { char c; alignas(8) int i; char d; };
struct Nested { A a; char c; };
int f(A a) { return a.c + a.i; }
int main()
{
  __CPROVER_assert(sizeof(A) == 8 && alignof(A) == 4, "A");
  __CPROVER_assert(sizeof(B) == 24 && __builtin_offsetof(B, e) == 16, "B");
  __CPROVER_assert(sizeof(U) == 8 && alignof(U) == 4, "union padded to its alignment");
  __CPROVER_assert(sizeof(C) == 16 && __builtin_offsetof(C, s) == 12, "C");
  __CPROVER_assert(sizeof(L) == 1, "L");
  __CPROVER_assert(sizeof(BF) == 4 && __builtin_offsetof(BF, d) == 2, "bit-field shares its unit, d follows in the next byte");
  __CPROVER_assert(sizeof(AL) == 16 && __builtin_offsetof(AL, d) == 12, "alignas");
  __CPROVER_assert(sizeof(Nested) == 12, "nested padded struct");
  // values built by the front end carry the padding: aggregate init, copies,
  // by-value calls, lambda captures, nested aggregates
  A a{1, 2};
  A b = a;
  __CPROVER_assert(b.c == 1 && b.i == 2 && f(b) == 3, "copy and by-value call");
  int x = 3;
  auto lam = [a, &x]() { return a.i + x; };
  __CPROVER_assert(lam() == 5, "lambda capture of a padded struct");
  C c{1, {"ab"}, 7};
  __CPROVER_assert(c.s == 7 && c.u.c[1] == 'b', "nested union aggregate");
  BF bf{1, 2, 3};
  __CPROVER_assert(bf.c == 1 && bf.b == 2 && bf.d == 3, "aggregate init with bit-field");
  A arr[2] = {{1, 1}, {2, 2}};
  __CPROVER_assert(arr[1].i == 2 && sizeof(arr) == 16, "array of padded structs");
  return 0;
}

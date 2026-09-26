// The cases below were checked against clang++-18 -std=c++17 (every
// static_assert holds there); N5008 [dcl.init.ref]/5 references in the
// comments.
extern "C" void __CPROVER_assert(bool, const char *);
struct S
{
  int v;
};
struct D : S
{
};
struct C
{
  operator S() const;
};
struct L
{
  operator S &() const;
};
// /5.1.1: lvalue, reference-compatible
static_assert(!__reference_binds_to_temporary(const int &, int &), "");
// /5.4.2: converted to a prvalue int
static_assert(__reference_binds_to_temporary(const int &, long), "");
static_assert(__reference_binds_to_temporary(const int &, long &), "");
static_assert(__reference_binds_to_temporary(const int &, char), "");
// /5.3.1: prvalue of the referenced type -- materialized, not converted
static_assert(!__reference_binds_to_temporary(const int &, int), "");
static_assert(!__reference_binds_to_temporary(const S &, S), "");
static_assert(!__reference_binds_to_temporary(S &&, S), "");
// /5.3.1: xvalue
static_assert(!__reference_binds_to_temporary(const S &, S &&), "");
// /5.3.1: prvalue of a derived class (base class subobject)
static_assert(!__reference_binds_to_temporary(const S &, D), "");
// /5.3.2: conversion function to a prvalue S
static_assert(__reference_binds_to_temporary(const S &, C), "");
static_assert(__reference_binds_to_temporary(S &&, C), "");
// /5.1.2: conversion function to an lvalue
static_assert(!__reference_binds_to_temporary(const S &, L), "");
// ill-formed bindings and a non-reference T are false
static_assert(!__reference_binds_to_temporary(int &, long), "");
static_assert(!__reference_binds_to_temporary(int, long), "");
static_assert(!__reference_binds_to_temporary(const S &, int), "");
// /5.4.2: pointer conversion yields a new pointer object
static_assert(__reference_binds_to_temporary(const void *const &, int *), "");
// arrays cannot be converted; binding an array prvalue directly
static_assert(!__reference_binds_to_temporary(int (&)[3], int[3]), "");

int main()
{
  __CPROVER_assert(
    __reference_binds_to_temporary(const S &, C), "conversion function");
  __CPROVER_assert(
    __reference_binds_to_temporary(const S &, D), "WRONG (must FAIL)");
}

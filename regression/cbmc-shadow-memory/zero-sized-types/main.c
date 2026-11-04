// Regression test for zero-sized types (ZSTs) in shadow memory operations
// This test verifies that CBMC doesn't crash when shadow memory operations
// are used with structures containing ZST fields.

struct ZeroSized
{
};

struct WithZST
{
  int i;
  struct ZeroSized zst;
};

struct TopStruct
{
  int f1;
  struct WithZST f2;
};

// Test with nested ZST
struct NestedZST
{
  struct ZeroSized zst1;
  struct ZeroSized zst2;
  int value;
};

// Test with only ZST members
struct OnlyZST
{
  struct ZeroSized zst;
};

void main()
{
  __CPROVER_field_decl_local("shadow", (_Bool)0);

  // Test 1: Basic struct with ZST field
  struct TopStruct top;
  __CPROVER_set_field(&top.f1, "shadow", 1);
  __CPROVER_assert(
    __CPROVER_get_field(&top.f1, "shadow") == 1,
    "expected success: set field to value 1");

  // Test 2: Get field on struct containing ZST
  // This used to crash with invariant violation in boolbv.cpp
  __CPROVER_assert(
    __CPROVER_get_field(&top.f2, "shadow") == 0,
    "expected success: default value is 0");

  // Test 3: Set and get field on struct containing ZST
  __CPROVER_set_field(&top.f2, "shadow", 1);
  __CPROVER_assert(
    __CPROVER_get_field(&top.f2, "shadow") == 1,
    "expected success: set/get field on struct with ZST");

  // Test 4: Test with member access on struct with ZST
  __CPROVER_set_field(&top.f2.i, "shadow", 1);
  __CPROVER_assert(
    __CPROVER_get_field(&top.f2.i, "shadow") == 1,
    "expected success: set/get on int member of struct with ZST");

  // Test 5: Nested ZST fields
  struct NestedZST nested;
  __CPROVER_set_field(&nested.value, "shadow", 1);
  __CPROVER_assert(
    __CPROVER_get_field(&nested.value, "shadow") == 1,
    "expected success: nested ZST fields");

  __CPROVER_assert(
    __CPROVER_get_field(&nested, "shadow") == 1,
    "expected success: get field on entire struct with multiple ZSTs");

  // Test 6: Struct with only ZST members
  struct OnlyZST only_zst;
  // Getting/setting shadow memory on a struct with only ZST members
  // should work and return the default value
  __CPROVER_assert(
    __CPROVER_get_field(&only_zst, "shadow") == 0,
    "expected success: struct with only ZST members has default value");
}

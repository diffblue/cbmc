#define NULL (void *)0

int main()
{
  int foo;

  // The identifiers are allocated deterministically, so we want to check the
  // following properties hold:

  // The pointer object of NULL is always going to be zero.
  __CPROVER_assert(
    __CPROVER_POINTER_OBJECT(NULL) != 0,
    "expected to fail with object ID == 0");
  // In the case where the program contains a single address of operation,
  // the pointer object is going to be 1.
  __CPROVER_assert(
    __CPROVER_POINTER_OBJECT(&foo) != 1,
    "expected to fail with object ID == 1");
}

// This test checks that dereferencing a pointer to an incomplete array type
// does not trigger an invariant violation.
// Related to issues #5293 and #4930

int (*a)[];

void b()
{
  *a; // This should not cause an invariant violation
}

void c()
{
  int(*p)[];
  *p; // Another case with a local variable
}

void test_pointer_arithmetic()
{
  int(*p)[] = a;
  int(*q)[] = p + 1; // Pointer arithmetic on incomplete array type
  int(*r)[] = q - 1; // Subtraction
}

int main()
{
  b();
  c();
  test_pointer_arithmetic();
  return 0;
}

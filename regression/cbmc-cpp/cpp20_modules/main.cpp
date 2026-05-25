// C++20 modules — basic syntax support
// CBMC parses module declarations and treats the file as a normal TU.
export module hello;

// Single exported function
export int f()
{
  return 42;
}

// Exported class
export class Widget
{
public:
  int value;
  int get() const
  {
    return value;
  }
};

// Export block with multiple declarations
export
{
  int add(int a, int b)
  {
    return a + b;
  }
  int sub(int a, int b)
  {
    return a - b;
  }
}

// Non-exported (module-internal) declaration
int internal_helper()
{
  return 1;
}

// Private module fragment
module :private;

int secret()
{
  return 99;
}

int main()
{
  __CPROVER_assert(f() == 42, "f returns 42");
  Widget w;
  w.value = 10;
  __CPROVER_assert(w.get() == 10, "get returns value");
  __CPROVER_assert(add(2, 3) == 5, "add works");
  __CPROVER_assert(sub(5, 3) == 2, "sub works");
  __CPROVER_assert(secret() == 99, "secret works");
}

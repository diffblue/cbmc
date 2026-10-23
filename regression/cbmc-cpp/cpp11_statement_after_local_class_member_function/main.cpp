// The statements of main after the definition of a local class with a
// member function body ([class.local]) are still in main: their properties
// are main.assertion.N.  The parser cleared the enclosing function's name
// at the end of the nested body.
extern "C" void __CPROVER_assert(bool, const char *);

int main()
{
  struct L
  {
    int f() const
    {
      return 1;
    }
  };
  __CPROVER_assert(L{}.f() == 1, "after local class");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}

int main()
{
  int a = 3;
  // Nested __auto_type inside GCC statement expressions used to trigger a
  // spurious 'redeclaration with no linkage' error (the parser turns
  // __auto_type into typeof(init), typechecking the inner block twice).
  int x = ({
    __auto_type v = ({
      __auto_type p = a;
      p;
    });
    v;
  });
  __CPROVER_assert(x == 3, "nested __auto_type in statement expression");
  return 0;
}

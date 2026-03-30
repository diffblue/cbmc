// Exercises the `type_qualifier_list identifier_declarator` alternative of
// gcc_nested_function_definition: a qualifier-only nested function head such
// as `const add1(int x) { ... }` (return type defaults to a const-qualified
// int). GCC accepts this with -Wimplicit-int.
int main(void)
{
  const add1(int x)
  {
    return x + 1;
  }

  __CPROVER_assert(add1(4) == 5, "const-qualified nested function");

  return 0;
}

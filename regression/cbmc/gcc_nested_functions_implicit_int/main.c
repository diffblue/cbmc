// Negative test documenting a deliberate boundary: GCC does not permit
// implicit-int nested functions, so a bare `identifier_declarator` head
// (no type specifier, e.g. `add1(int x) { ... }`) is rejected. The
// gcc_nested_function_definition grammar deliberately does not mirror this
// `function_head` alternative.
int main(void)
{
  add1(int x)
  {
    return x + 1;
  }

  return add1(4) == 5 ? 0 : 1;
}

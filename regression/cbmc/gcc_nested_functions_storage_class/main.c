// Negative test documenting a deliberate boundary: a storage-class qualifier
// with implicit int (a `declaration_qualifier_list identifier_declarator`
// head, e.g. `static g(void) { ... }`) is rejected for nested functions, as
// GCC does not permit implicit int there. This `function_head` alternative is
// deliberately not mirrored in gcc_nested_function_definition.
int main(void)
{
  static g(void)
  {
    return 7;
  }

  return g() == 7 ? 0 : 1;
}

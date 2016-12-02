// Tests a parsing issue regarding array declarators, see Array_Declarator1

int main(void)
{
  // bar0 should fail, , e.g., gcc says
  // error: static or type qualifiers in non-parameter array declarator
  int bar0[restrict] = {0};
  return 0;
}

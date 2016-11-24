// Tests a parsing issue regarding array declarators, see Array_Declarator1

int main(void)
{
  // bar4 should fail, e.g., gcc says
  // error: static or type qualifiers in non-parameter array declarator
  int bar4[static restrict 4U] = {1, 2, 3, 4};
  return 0;
}

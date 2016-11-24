// Tests a parsing issue regarding array declarators, see Array_Declarator1

int main(void)
{
  // bar2 should fail, , e.g., gcc says
  // error: static or type qualifiers in non-parameter array declarator
  int bar2[restrict 2U] = {1, 2};
  return 0;
}

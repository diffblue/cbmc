// Tests a parsing issue regarding array declarators, see Array_Declarator1

int main(void)
{
  // bar3 should fail, , e.g., gcc says
  // error: static or type qualifiers in non-parameter array declarator
  int bar3[restrict static 3U] = {1, 2, 3};
  return 0;
}

inline int inline_function_with_postfix_attributes(void)
  __attribute__((not_a_real_attribute))
{
  return 0;
}

int non_inline_with_postfix_attributes(void)
  __attribute__((not_a_real_attribute))
{
  return 0;
}

int main(void)
{
}

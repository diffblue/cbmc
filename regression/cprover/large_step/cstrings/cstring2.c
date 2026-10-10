int main()
{
  char buffer[100];

  // simply state equality + uninterpreted function
  if(__CPROVER_is_cstring(buffer))
    __CPROVER_assert(__CPROVER_is_cstring(buffer), "property 1"); // passes

  return 0;
}

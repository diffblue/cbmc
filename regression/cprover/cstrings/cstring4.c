int main()
{
  char buffer[100], ch;
  __CPROVER_assume(__CPROVER_is_cstring(buffer));
  ch = 'a'; // does not affect 'buffer'
  __CPROVER_assert(__CPROVER_is_cstring(buffer), "property 1"); // passes
  return 0;
}

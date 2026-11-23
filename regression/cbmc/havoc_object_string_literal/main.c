int main()
{
  char *s = "abc";
  int i = 0;
  _Bool c;
  char *p = c ? s : (char *)&i;

  // String literals cannot be modified, havocking them has no effect.
  __CPROVER_havoc_object(s);
  __CPROVER_assert(s[0] == 'a', "string literal unchanged");

  __CPROVER_havoc_object(p);
  __CPROVER_assert(i == 0, "i may be havocked"); // should fail
  return 0;
}

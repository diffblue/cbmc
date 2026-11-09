void cstring_preserved(const char *p)
  __CPROVER_requires(__CPROVER_is_cstring(p))
{
  // unrelated
  __CPROVER_size_t i = 0;

  __CPROVER_assert(__CPROVER_is_cstring(p), "p is still a cstring");
}

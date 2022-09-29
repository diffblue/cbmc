void string_access(__CPROVER_size_t length, const char *p)
  __CPROVER_requires(__CPROVER_is_cstring(p) && __CPROVER_cstrlen(p) == length)
{
  __CPROVER_assert(p[length] == 0, "property 1"); // passes
}

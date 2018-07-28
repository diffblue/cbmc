int main()
{
  // general types
  short s;
  int i;
  long l;
  long long ll;

  __CPROVER_assert(sizeof(s) == 2, "");
  __CPROVER_assert(sizeof(i) == 4, "");
  __CPROVER_assert(sizeof(l) == 4, "");
  __CPROVER_assert(sizeof(ll) == 8, "");

  // oh, and these pointer qualifiers are MS-specific
  int * __ptr32 p32;
  int * __ptr64 p64;

  // requires --winx64 to work
  __CPROVER_assert(sizeof(p32) == 4, "");
  __CPROVER_assert(sizeof(p64) == 8, "");

  __CPROVER_assert(sizeof(void *) == 8, "");
}

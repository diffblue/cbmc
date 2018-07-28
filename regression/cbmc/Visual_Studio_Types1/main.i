int main()
{
  // these types are Visual Studio-specific
  __int8 i1;
  __int16 i2;
  __int32 i3;
  __int64 i4;

  __CPROVER_assert(sizeof(i1) == 1, "");
  __CPROVER_assert(sizeof(i2) == 2, "");
  __CPROVER_assert(sizeof(i3) == 4, "");
  __CPROVER_assert(sizeof(i4) == 8, "");

  // general types

  char c;
  short s;
  int i;
  long l;
  long long ll;

  __CPROVER_assert(sizeof(c) == 1, "");
  __CPROVER_assert(sizeof(s) == 2, "");
  __CPROVER_assert(sizeof(i) == 4, "");
  __CPROVER_assert(sizeof(l) == 4, "");
  __CPROVER_assert(sizeof(ll) == 8, "");

  // these constants are Visual Studio-specific
  __CPROVER_assert(sizeof(1i8) == 1, "");
  __CPROVER_assert(sizeof(1i16) == 2, "");
  __CPROVER_assert(sizeof(1i32) == 4, "");
  __CPROVER_assert(sizeof(1i64) == 8, "");
  __CPROVER_assert(sizeof(1i128) == 16, "");

  // oh, and these pointer qualifiers are Visual Studio-specific
  int * __ptr32 p32;
  //int * __ptr64 p64;

  // requires --i386-win32 to work
  __CPROVER_assert(sizeof(p32) == 4, "");
  //__CPROVER_assert(sizeof(p64) == 8, "");

  __CPROVER_assert(sizeof(void *) == 4, "");
}

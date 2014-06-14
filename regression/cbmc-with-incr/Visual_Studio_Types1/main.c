int main()
{
  // these types are MS-specific  
  __int8 i1;
  __int16 i2;
  __int32 i3;
  __int64 i4;

  assert(sizeof(i1)==1);
  assert(sizeof(i2)==2);
  assert(sizeof(i3)==4);
  assert(sizeof(i4)==8);
  
  // general types
  
  char c;
  short s;
  int i;
  long l;
  long long ll;
  
  assert(sizeof(c)==1);
  assert(sizeof(s)==2);
  assert(sizeof(i)==4);
  assert(sizeof(l)==4);
  assert(sizeof(ll)==8);
  
  // these constants are MS-specific  
  assert(sizeof(1i8)==1);
  assert(sizeof(1i16)==2);
  assert(sizeof(1i32)==4);
  assert(sizeof(1i64)==8);
  assert(sizeof(1i128)==16);
  
  // oh, and these pointer qualifiers are MS-specific
  int * __ptr32 p32;
  //int * __ptr64 p64;

  // requires --i386-win32 to work
  assert(sizeof(p32)==4);
  //assert(sizeof(p64)==8);
  assert(sizeof(void *)==4);
}

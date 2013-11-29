int main()
{
  // general types
  short s;
  int i;
  long l;
  long long ll;
  
  assert(sizeof(s)==2);
  assert(sizeof(i)==4);
  assert(sizeof(l)==4);
  assert(sizeof(ll)==8);
  
  // oh, and these pointer qualifiers are MS-specific
  int * __ptr32 p32;
  int * __ptr64 p64;

  // requires --winx64 to work
  assert(sizeof(p32)==4);
  assert(sizeof(p64)==8);
  assert(sizeof(void *)==8);
}

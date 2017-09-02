static unsigned bar()
{
  unsigned r;
  return r;
}

#ifdef _MSC_VER

static void foo()
{
}

#else

static void foo()
{
 unsigned len=bar();
 struct {
   int a;
   union {
     int s;
     unsigned char b[len];
   } __attribute__ (( packed )) S;
   int c;
 } __attribute__ (( packed )) *l;
}

#endif

int main()
{
  foo();
  return 0;
}

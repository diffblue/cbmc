#define STATIC_ASSERT(condition) \
  int some_array##__LINE__[(condition) ? 1 : -1];    

STATIC_ASSERT('\''==39);
STATIC_ASSERT(L'\''==39);

STATIC_ASSERT('\0'==0);
STATIC_ASSERT('\10'==8); // octal!
STATIC_ASSERT((signed char)'\xab'==(signed char)0xab); // negative!
STATIC_ASSERT(L'\xab'==0xab);
STATIC_ASSERT(L'\xabcd'==0xabcd);

// multi-byte
STATIC_ASSERT('abcd'==('a'<<24)+('b'<<16)+('c'<<8)+'d');

// sizes
STATIC_ASSERT(sizeof(1)==sizeof(int));
STATIC_ASSERT(sizeof(1l)==sizeof(long int));
STATIC_ASSERT(sizeof(1ll)==sizeof(long long int));
STATIC_ASSERT(sizeof(0xaaaabbbbcccc)==sizeof(long long int));
STATIC_ASSERT(sizeof('x')==sizeof(int)); // int in C, char in C++

// binary, which is newer versions of gcc only
#ifdef __GNUC__
STATIC_ASSERT(0b101010==42);
STATIC_ASSERT(0B101010==42);
STATIC_ASSERT(sizeof(0B101010)==sizeof(int));
STATIC_ASSERT(sizeof(0B101010LL)==sizeof(long long));
STATIC_ASSERT(sizeof(0B101010)==sizeof(int));
STATIC_ASSERT(0b10000000000000000000000000000000==2147483648);
STATIC_ASSERT(sizeof(0b10000000000000000000000000000000)==sizeof(int));
#endif

#ifdef _WIN32
STATIC_ASSERT(sizeof(L'x')==2);
#else
STATIC_ASSERT(sizeof(L'x')==sizeof(int));
STATIC_ASSERT(L'\xabcdabcd'==0xabcdabcd);
STATIC_ASSERT(L'\xfbcdabcd'==0xfbcdabcd);
#endif

int main()
{
}

#define STATIC_ASSERT(condition) \
  int some_array##__LINE__[(condition) ? 1 : -1];    

STATIC_ASSERT('\''==39);
STATIC_ASSERT(L'\''==39);

STATIC_ASSERT('\0'==0);
STATIC_ASSERT('\10'==8); // octal!
STATIC_ASSERT('\xab'==(signed char)0xab); // negative!
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
STATIC_ASSERT(sizeof(L'x')==sizeof(int));

int main()
{
}

#define CONCAT(a, b) a##b
#define CONCAT2(a, b) CONCAT(a, b)

#define STATIC_ASSERT(condition)                                               \
  int CONCAT2(some_array, __LINE__)[(condition) ? 1 : -1]

#if defined(__GNUC__)

enum  { E1v1, E1v2 } __attribute__((packed)) e1;
enum __attribute__((packed)) { E2v1=-1, E2v2 } e2;
enum __attribute__((packed)) { E3v1=1000, E3v2 } e3;
enum { E4v1=-1, E4v2 } e4; // not packed
enum { E5v0=10, E5v1=0x100000000ll } e5;
enum { E6 = E3v1 | 1 };
enum { E7v1=0, E7v2=sizeof(E7v1), E7v3=0x100000000ll };

STATIC_ASSERT(sizeof e1 == 1);
STATIC_ASSERT(sizeof E1v1 == sizeof(int)); // but the constant is still at least int
STATIC_ASSERT(sizeof e2 == 1);
STATIC_ASSERT(sizeof e3 == 2);
STATIC_ASSERT(sizeof E4v1 == sizeof(int));
STATIC_ASSERT(sizeof e4 == sizeof(int));
STATIC_ASSERT(sizeof e5 == 8);
STATIC_ASSERT(E5v1 == 0x100000000ll);
STATIC_ASSERT(E3v1 == 1000);
STATIC_ASSERT(E6 == 1001);
STATIC_ASSERT(E7v2 == sizeof(int));
STATIC_ASSERT(sizeof E7v3 == sizeof(long long));

int main()
{
  e5+=1;
  e5|=1;
  e5|=e5;
  e5&=1;
  e5&=(_Bool)1;
  e5^=(_Bool)1;
  e5<<=1;
}

#elif defined(_MSC_VER)

// In Visual Studio, everything is 'signed int'

enum { E4v1=-1, E4v2 } e4;
enum { E5v0=10, E5v1=0x100000000ll } e5;
enum { E6 = E4v1 + 10 };
enum { E7v1=0, E7v2=sizeof(E7v1), E7v3=0x100000000ll };

STATIC_ASSERT(sizeof E4v1 == sizeof(int));
STATIC_ASSERT(sizeof e4 == sizeof(int));
STATIC_ASSERT(sizeof e5 == sizeof(int));
STATIC_ASSERT(E5v1 == (int)0x100000000ll);
STATIC_ASSERT(E6 == 9);
STATIC_ASSERT(E7v2 == sizeof(int));
STATIC_ASSERT(sizeof E7v3 == sizeof(int));

int main()
{
}

#else

int main()
{
}
#endif

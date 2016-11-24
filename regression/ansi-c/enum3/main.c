#ifdef __GNUC__

#define STATIC_ASSERT(condition) \
  int some_array##__LINE__[(condition) ? 1 : -1]

enum  { E1v1, E1v2 } __attribute__((packed)) e1;
enum __attribute__((packed)) { E2v1=-1, E2v2 } e2;
enum __attribute__((packed)) { E3v1=1000, E3v2 } e3;
enum { E4v1=-1, E4v2 } e4; // not packed
enum { E5v0=10, E5v1=0x100000000ll } e5;
enum { E6 = E3v1 | 1 };

STATIC_ASSERT(sizeof(e1) == 1);
STATIC_ASSERT(sizeof(e2) == 1);
STATIC_ASSERT(sizeof(e3) == 2);
STATIC_ASSERT(sizeof(E1v1) == sizeof(int));
STATIC_ASSERT(sizeof(e4) == sizeof(int));
// STATIC_ASSERT(sizeof(e5) == 8); // todo
STATIC_ASSERT(E6 == 1001);

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

#else

int main()
{
}

#endif


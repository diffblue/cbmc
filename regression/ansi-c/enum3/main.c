#ifdef __GNUC__

#define STATIC_ASSERT(condition) \
  int some_array##__LINE__[(condition) ? 1 : -1]

enum  { E1v1, E1v2 } __attribute__((packed)) e1;
enum __attribute__((packed)) { E2v1=-1, E2v2 } e2;
enum __attribute__((packed)) { E3v1=1000, E3v2 } e3;

STATIC_ASSERT(sizeof(e1) == 1);
STATIC_ASSERT(sizeof(e2) == 1);
STATIC_ASSERT(sizeof(e3) == 2);
STATIC_ASSERT(sizeof(E1v1) == 4);
#endif

int main()
{
}


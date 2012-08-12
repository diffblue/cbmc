#include <wchar.h>

#define STATIC_ASSERT(condition) \
  int some_array##__LINE__[(condition) ? 1 : -1];    

#ifdef _WIN32

#ifdef _WIN64

STATIC_ASSERT(sizeof(void *)==8);
STATIC_ASSERT(sizeof(int)==4);
STATIC_ASSERT(sizeof(long int)==4);
STATIC_ASSERT(sizeof(long long int)==8);
STATIC_ASSERT(sizeof(wchar_t)==2);
STATIC_ASSERT(sizeof(long double)==8);

#else

STATIC_ASSERT(sizeof(void *)==4);
STATIC_ASSERT(sizeof(int)==4);
STATIC_ASSERT(sizeof(long int)==4);
STATIC_ASSERT(sizeof(long long int)==8);
STATIC_ASSERT(sizeof(wchar_t)==2);
STATIC_ASSERT(sizeof(long double)==8);

#endif

#else

// the following does both 32 and 64 bit architectures

STATIC_ASSERT(sizeof(void *)==sizeof(long int));
STATIC_ASSERT(sizeof(int)==4);
STATIC_ASSERT(sizeof(long int)==4 || sizeof(long int)==8);
STATIC_ASSERT(sizeof(long long int)==8);
STATIC_ASSERT(sizeof(wchar_t)==4);
STATIC_ASSERT(sizeof(float)==4);
STATIC_ASSERT(sizeof(double)==8);
STATIC_ASSERT(sizeof(long double)>=sizeof(double));

#endif

int main()
{
}

#include <wchar.h>
#include <stdlib.h> // for size_t

#define CONCAT(a, b) a##b
#define CONCAT2(a, b) CONCAT(a, b)

#define STATIC_ASSERT(condition)                                               \
  int CONCAT2(some_array, __LINE__)[(condition) ? 1 : -1]

// check size_t
STATIC_ASSERT(sizeof(void *)==sizeof(size_t));

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

// Note that there are architectures (e.g., x32) with
// 64-bit long int and 32-bit pointers. However,
// a long int should always be able to hold a pointer.
STATIC_ASSERT(sizeof(void *)<=sizeof(long int));

STATIC_ASSERT(sizeof(int)==4);
STATIC_ASSERT(sizeof(long int)==4 || sizeof(long int)==8);
STATIC_ASSERT(sizeof(long long int)==8);

#ifdef __CYGWIN__
STATIC_ASSERT(sizeof(wchar_t)==2);
#else
STATIC_ASSERT(sizeof(wchar_t)==4);
#endif

STATIC_ASSERT(sizeof(float)==4);
STATIC_ASSERT(sizeof(double)==8);
STATIC_ASSERT(sizeof(long double)>=sizeof(double));

#endif

int main()
{
}

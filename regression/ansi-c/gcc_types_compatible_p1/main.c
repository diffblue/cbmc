#define STATIC_ASSERT(condition) \
  int some_array[(condition) ? 1 : -1];

int i;
double d;

typedef enum T1 { hot, dog, poo, bear } dingos;
typedef enum T2 { janette, laura, amanda } cranberry;

typedef enum AnonEnum { jim, bob, fred } names;

typedef dingos altdingos;
typedef dingos diffdingos;

typedef names altnames;
typedef names diffnames;

typedef float same1;
typedef float same2;

dingos _dingos;
cranberry _cranberry;

#ifdef __GNUC__

#define __intN_t(N, MODE) \
  typedef int int##N##_t __attribute__ ((__mode__ (MODE))); \
  typedef unsigned int uint##N##_t __attribute__ ((__mode__ (MODE)))

__intN_t (8, __QI__);
__intN_t (16, __HI__);
__intN_t (32, __SI__);
__intN_t (64, __DI__);

/* Compatible types */

// the size type varies according to architecture
STATIC_ASSERT(
     __builtin_types_compatible_p(typeof(sizeof(int)), unsigned int)
  || __builtin_types_compatible_p(typeof(sizeof(int)), unsigned long int)
  || __builtin_types_compatible_p(typeof(sizeof(int)), unsigned long long int));

STATIC_ASSERT(__builtin_types_compatible_p(int8_t, signed char));
STATIC_ASSERT(__builtin_types_compatible_p(int16_t, signed short));
STATIC_ASSERT(__builtin_types_compatible_p(int32_t, signed int));
STATIC_ASSERT(__builtin_types_compatible_p(uint8_t, unsigned char));
STATIC_ASSERT(__builtin_types_compatible_p(uint16_t, unsigned short));
STATIC_ASSERT(__builtin_types_compatible_p(uint32_t, unsigned int));

// the 64-bit types may vary
STATIC_ASSERT(sizeof(long)!=8 || __builtin_types_compatible_p(int64_t, signed long));
STATIC_ASSERT(sizeof(long)!=8 || __builtin_types_compatible_p(uint64_t, unsigned long));
STATIC_ASSERT(sizeof(long)!=4 || __builtin_types_compatible_p(int64_t, signed long long));
STATIC_ASSERT(sizeof(long)!=4 || __builtin_types_compatible_p(uint64_t, unsigned long long));

STATIC_ASSERT(__builtin_types_compatible_p(int, const int));
STATIC_ASSERT(__builtin_types_compatible_p(int, signed));
STATIC_ASSERT(__builtin_types_compatible_p(typeof (hot), int));
STATIC_ASSERT(__builtin_types_compatible_p(typeof (dingos), unsigned)); // ha!
STATIC_ASSERT(__builtin_types_compatible_p(typeof (hot), typeof (laura)));
STATIC_ASSERT(__builtin_types_compatible_p(int[5], int[]));
STATIC_ASSERT(__builtin_types_compatible_p(same1, same2));
STATIC_ASSERT(__builtin_types_compatible_p(dingos, altdingos));
STATIC_ASSERT(__builtin_types_compatible_p(diffdingos, altdingos));
STATIC_ASSERT(__builtin_types_compatible_p(diffnames, altnames));
STATIC_ASSERT(__builtin_types_compatible_p(typeof (hot) *, int *));
STATIC_ASSERT(__builtin_types_compatible_p(typeof (hot), typeof (janette)));
STATIC_ASSERT(__builtin_types_compatible_p(__int128, signed __int128));

// clang doesn't have these
#if !defined(__clang__) && __GNUC__ >= 7
#if defined(__x86_64__) || defined(__i386__)
STATIC_ASSERT(__builtin_types_compatible_p(__float128, _Float128));
#endif
#endif

/* Incompatible types */

STATIC_ASSERT(!__builtin_types_compatible_p(char, _Bool));
STATIC_ASSERT(!__builtin_types_compatible_p(char, signed char));
STATIC_ASSERT(!__builtin_types_compatible_p(int8_t, char));
STATIC_ASSERT(!__builtin_types_compatible_p(char *, int));
STATIC_ASSERT(!__builtin_types_compatible_p(char *, const char *));
STATIC_ASSERT(!__builtin_types_compatible_p(const char *, char *));
STATIC_ASSERT(!__builtin_types_compatible_p(long double, double));
STATIC_ASSERT(!__builtin_types_compatible_p(double, float));
STATIC_ASSERT(!__builtin_types_compatible_p(typeof (i), typeof (d)));
STATIC_ASSERT(!__builtin_types_compatible_p(dingos, cranberry));
STATIC_ASSERT(!__builtin_types_compatible_p(typeof (_dingos), typeof (_cranberry)));
STATIC_ASSERT(!__builtin_types_compatible_p(char, int));
STATIC_ASSERT(!__builtin_types_compatible_p(char *, char **));
STATIC_ASSERT(!__builtin_types_compatible_p(typeof (hot), unsigned int));
STATIC_ASSERT(!__builtin_types_compatible_p(int[], int *));
STATIC_ASSERT(!__builtin_types_compatible_p(long int, int));
STATIC_ASSERT(!__builtin_types_compatible_p(long long int, long int));
STATIC_ASSERT(!__builtin_types_compatible_p(unsigned, signed));

STATIC_ASSERT(!__builtin_types_compatible_p(__int128, unsigned __int128));

// clang doesn't have these
#if !defined(__clang__) && \
    (defined(__ia64__) || defined(__x86_64__) || defined(__i386__))
#if __GNUC__ >= 7
STATIC_ASSERT(!__builtin_types_compatible_p(_Float32, float));
STATIC_ASSERT(!__builtin_types_compatible_p(_Float64, double));
STATIC_ASSERT(!__builtin_types_compatible_p(_Float32x, float));
STATIC_ASSERT(!__builtin_types_compatible_p(_Float64x, double));
#endif
STATIC_ASSERT(!__builtin_types_compatible_p(__float80, double));
STATIC_ASSERT(!__builtin_types_compatible_p(__float128, long double));
STATIC_ASSERT(!__builtin_types_compatible_p(__float128, double));
#endif
#endif

int main(void)
{
}

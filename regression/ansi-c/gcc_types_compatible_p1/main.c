#define STATIC_ASSERT(condition) \
  int some_array[(condition) ? 1 : -1];
  
int i;
double d;

typedef enum T1 { hot, dog, poo, bear } dingos;
typedef enum T2 { janette, laura, amanda } cranberry;

typedef float same1;
typedef float same2;

dingos _dingos;
cranberry _cranberry;

/* Compatible types.  */

#ifdef __GNUC__

STATIC_ASSERT(__builtin_types_compatible_p(int, const int));
STATIC_ASSERT(__builtin_types_compatible_p(typeof (hot), int));
STATIC_ASSERT(__builtin_types_compatible_p(typeof (hot), typeof (laura)));
STATIC_ASSERT(__builtin_types_compatible_p(int[5], int[]));
STATIC_ASSERT(__builtin_types_compatible_p(same1, same2));
STATIC_ASSERT(__builtin_types_compatible_p(typeof (hot) *, int *));

/* Incompatible types.  */
STATIC_ASSERT(!__builtin_types_compatible_p(char *, int));
STATIC_ASSERT(!__builtin_types_compatible_p(char *, const char *));
STATIC_ASSERT(!__builtin_types_compatible_p(const char *, char *));
STATIC_ASSERT(!__builtin_types_compatible_p(long double, double));
STATIC_ASSERT(!__builtin_types_compatible_p(typeof (i), typeof (d)));
STATIC_ASSERT(!__builtin_types_compatible_p(typeof (dingos), typeof (cranberry)));
STATIC_ASSERT(!__builtin_types_compatible_p(typeof (_dingos), typeof (_cranberry)));
STATIC_ASSERT(!__builtin_types_compatible_p(char, int));
STATIC_ASSERT(!__builtin_types_compatible_p(char *, char **));
STATIC_ASSERT(!__builtin_types_compatible_p(typeof (hot), unsigned int));
STATIC_ASSERT(!__builtin_types_compatible_p(int[], int *));

#endif

int main (void)
{
}


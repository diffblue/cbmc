#ifdef __GNUC__

#  define CONCAT(a, b) a##b
#  define CONCAT2(a, b) CONCAT(a, b)

#  define STATIC_ASSERT(condition)                                             \
    int CONCAT2(some_array, __LINE__)[(condition) ? 1 : -1]

int getopt_long(int i, char * const* s);
int getopt_long_nn(int, char * const*);
int getopt_long2(int i, char const * const* s);
int getopt_long_nn2(int, char const * const*);
int getopt_long3(int i, const char ** s);
int getopt_long_nn3(int, const char **);
int getopt_long4(int i, char ** const s);
int getopt_long_nn4(int, char ** const);

STATIC_ASSERT(__builtin_types_compatible_p(
    typeof(getopt_long), typeof(getopt_long_nn)));
STATIC_ASSERT(__builtin_types_compatible_p(
    typeof(getopt_long2), typeof(getopt_long_nn2)));
STATIC_ASSERT(__builtin_types_compatible_p(
    typeof(getopt_long3), typeof(getopt_long_nn3)));
STATIC_ASSERT(__builtin_types_compatible_p(
    typeof(getopt_long4), typeof(getopt_long_nn4)));

STATIC_ASSERT(!__builtin_types_compatible_p(
    typeof(getopt_long), typeof(getopt_long2)));
STATIC_ASSERT(!__builtin_types_compatible_p(
    typeof(getopt_long), typeof(getopt_long3)));
STATIC_ASSERT(!__builtin_types_compatible_p(
    typeof(getopt_long), typeof(getopt_long4)));
STATIC_ASSERT(!__builtin_types_compatible_p(
    typeof(getopt_long2), typeof(getopt_long3)));
STATIC_ASSERT(!__builtin_types_compatible_p(
    typeof(getopt_long2), typeof(getopt_long4)));
STATIC_ASSERT(!__builtin_types_compatible_p(
    typeof(getopt_long3), typeof(getopt_long4)));

typedef char * const * X;

int getopt_long5(int i, X s);
int getopt_long_nn5(int, X);

STATIC_ASSERT(__builtin_types_compatible_p(
    typeof(getopt_long5), typeof(getopt_long_nn5)));
STATIC_ASSERT(__builtin_types_compatible_p(
    typeof(getopt_long), typeof(getopt_long5)));

#endif

int main()
{
  return 0;
}

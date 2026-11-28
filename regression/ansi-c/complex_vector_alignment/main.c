// complex numbers are aligned like their real and imaginary parts, vectors to
// their size
typedef float v4f __attribute__((vector_size(16)));
typedef int v2i __attribute__((vector_size(8)));
typedef char v32c __attribute__((vector_size(32)));

#define OFFSET_IN_STRUCT(T)                                                    \
  __builtin_offsetof(                                                          \
    struct {                                                                   \
      char c;                                                                  \
      T m;                                                                     \
    },                                                                         \
    m)

_Static_assert(OFFSET_IN_STRUCT(_Complex float) == OFFSET_IN_STRUCT(float), "");
_Static_assert(
  OFFSET_IN_STRUCT(_Complex double) == OFFSET_IN_STRUCT(double),
  "");
_Static_assert(
  OFFSET_IN_STRUCT(_Complex long double) == OFFSET_IN_STRUCT(long double),
  "");
_Static_assert(_Alignof(_Complex double) == _Alignof(double), "");
_Static_assert(__alignof__(_Complex double) == __alignof__(double), "");

_Static_assert(OFFSET_IN_STRUCT(v2i) == 8, "");
_Static_assert(OFFSET_IN_STRUCT(v4f) == 16, "");
_Static_assert(OFFSET_IN_STRUCT(v32c) == 32, "");
_Static_assert(_Alignof(v4f) == 16 && __alignof__(v4f) == 16, "");

struct S
{
  char c;
  v4f v;
  _Complex double z;
};
_Static_assert(sizeof(struct S) == 32 + 2 * sizeof(double), "");

int main()
{
  return 0;
}

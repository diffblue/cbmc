#define CONCAT(a, b) a##b
#define CONCAT2(a, b) CONCAT(a, b)

#define STATIC_ASSERT(condition)                                               \
  int CONCAT2(some_array, __LINE__)[(condition) ? 1 : -1]

#ifdef __GNUC__
#ifndef __clang__

int  x   __attribute__ ((__vector_size__ (16), __may_alias__));
int  x2   __attribute__ ((__may_alias__));
int  x3   __attribute__ ((__may_alias__, __vector_size__ (16)));

STATIC_ASSERT(sizeof(x)==16);
STATIC_ASSERT(sizeof(x2)==sizeof(int));
STATIC_ASSERT(sizeof(x3)==16);

#endif
#endif

int main(int argc, char* argv[])
{
  return 0;
}

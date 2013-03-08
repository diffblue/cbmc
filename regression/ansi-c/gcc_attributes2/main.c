#define static_assert(x, y) ((struct { int field : (x)?1:-1; } *)0)

// Copied from sys/types.h

/* For GCC 2.7 and later, we can use specific type-size attributes.  */
# define __intN_t(N, MODE) \
  typedef int int##N##_t __attribute__ ((__mode__ (MODE)))

__intN_t (8, __QI__);
__intN_t (16, __HI__);
__intN_t (32, __SI__);
__intN_t (64, __DI__);

int main()
{
  static_assert(sizeof(int8_t)==1, "width of int8_t");
  static_assert(sizeof(int16_t)==2, "width of int16_t");
  static_assert(sizeof(int32_t)==4, "width of int32_t");
  static_assert(sizeof(int64_t)==8, "width of int64_t");
  
  // also directly in the sizeof
  static_assert(sizeof(int __attribute__((__mode__(__DI__))))==8, "width of int64_t");
  static_assert(sizeof(__attribute__((__mode__(__DI__))) int)==8, "width of int64_t");
  
}


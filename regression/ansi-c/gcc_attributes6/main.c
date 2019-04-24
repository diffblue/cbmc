#define CONCAT(a, b) a##b
#define CONCAT2(a, b) CONCAT(a, b)

#define STATIC_ASSERT(condition)                                               \
  int CONCAT2(some_array, __LINE__)[(condition) ? 1 : -1]

#ifdef __GNUC__

// gcc allows mode attributes on enums, but clang doesn't
enum E_QI { E_QI } __attribute__ ((__mode__ (__QI__)));
enum E_HI { E_HI } __attribute__ ((__mode__ (__HI__)));
enum E_SI { E_SI } __attribute__ ((__mode__ (__SI__)));
enum E_DI { E_DI } __attribute__ ((__mode__ (__DI__)));
enum E_TI { E_TI } __attribute__ ((__mode__ (__TI__)));

STATIC_ASSERT(sizeof(enum E_QI)==1);
STATIC_ASSERT(sizeof(enum E_HI)==2);
STATIC_ASSERT(sizeof(enum E_SI)==4);
STATIC_ASSERT(sizeof(enum E_DI)==8);
STATIC_ASSERT(sizeof(enum E_TI)==16);

// and they can be changed afterwards!

STATIC_ASSERT(sizeof(enum E_DI __attribute__ ((__mode__ (__QI__))))==1);
STATIC_ASSERT(sizeof(enum E_DI __attribute__ ((__mode__ (__HI__))))==2);
STATIC_ASSERT(sizeof(enum E_DI __attribute__ ((__mode__ (__SI__))))==4);
STATIC_ASSERT(sizeof(enum E_DI __attribute__ ((__mode__ (__DI__))))==8);

// gcc (but not clang) also allows mode attributes on _Complex
// from fftw3.h -- this means TF on the underlying floats
typedef _Complex float __attribute__ ((__mode__ (TC))) fftwq_complex;

#endif

int main()
{
}

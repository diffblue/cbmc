#define STATIC_ASSERT(condition) \
  int some_array[(condition) ? 1 : -1];  

#ifdef __GNUC__

// gcc allows mode attributes on enums, but clang doesn't
enum E_QI { E_QI } __attribute__ ((__mode__ (__QI__)));
enum E_HI { E_HI } __attribute__ ((__mode__ (__HI__)));
enum E_SI { E_SI } __attribute__ ((__mode__ (__SI__)));
enum E_DI { E_DI } __attribute__ ((__mode__ (__DI__)));

STATIC_ASSERT(sizeof(enum E_QI)==1);
STATIC_ASSERT(sizeof(enum E_HI)==2);
STATIC_ASSERT(sizeof(enum E_SI)==4);
STATIC_ASSERT(sizeof(enum E_DI)==8);

// and they can be changed afterwards!

STATIC_ASSERT(sizeof(enum E_DI __attribute__ ((__mode__ (__QI__))))==1);
STATIC_ASSERT(sizeof(enum E_DI __attribute__ ((__mode__ (__HI__))))==2);
STATIC_ASSERT(sizeof(enum E_DI __attribute__ ((__mode__ (__SI__))))==4);
STATIC_ASSERT(sizeof(enum E_DI __attribute__ ((__mode__ (__DI__))))==8);

#endif

int main()
{
}

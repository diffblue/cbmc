#define CONCAT(a, b) a##b
#define CONCAT2(a, b) CONCAT(a, b)

#define STATIC_ASSERT(condition)                                               \
  int CONCAT2(some_array, __LINE__)[(condition) ? 1 : -1]

#ifdef __GNUC__

char __attribute__((aligned(16))) var1;
__attribute__((aligned(16))) char var2;
char var3 __attribute__((aligned(16)));
int (__attribute__((aligned(16))) var4);
int (__attribute__((aligned(16))) (var5));
int (__attribute__((aligned(16))) *var6);
int __attribute__((aligned(16))) *var7;
__attribute__((aligned(16))) int *var8;

STATIC_ASSERT(__alignof(var1)==16);
STATIC_ASSERT(__alignof(var2)==16);
STATIC_ASSERT(__alignof(var3)==16);
STATIC_ASSERT(__alignof(var4)==16);
STATIC_ASSERT(__alignof(var5)==16);
#ifdef __clang__
STATIC_ASSERT(__alignof(var6)==16);
STATIC_ASSERT(__alignof(*var6)==__alignof(int));
#else
STATIC_ASSERT(__alignof(var6)==__alignof(void *));
STATIC_ASSERT(__alignof(*var6)==16);
#endif
STATIC_ASSERT(__alignof(var7)==16);
STATIC_ASSERT(__alignof(var8)==16);

void (__attribute__((aligned)) *****f1)(void);
void (__attribute__((aligned)) f2)(void);

int __attribute__((cdecl,regparm(0))) *foo1(int x);
int __attribute__((cdecl,regparm(0))) *(foo2)(int x);
int (__attribute__((cdecl,regparm(0))) *foo3)(int x);
int (* __attribute__((cdecl,regparm(0))) foo4)(int x);
typedef int (__attribute__((cdecl,regparm(0))) foo5)(int x);
typedef int (__attribute__((cdecl,regparm(0))) *foo6)(int x);
typedef int* (__attribute__((cdecl,regparm(0))) *foo7)(int x);

#endif

int main()
{
}

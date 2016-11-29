#define STATIC_ASSERT(condition) \
  int some_array##__LINE__[(condition) ? 1 : -1];

#ifdef __GNUC__

char __attribute__((aligned(8))) var1;
__attribute__((aligned(8))) char var2;
char var3 __attribute__((aligned(8)));
int (__attribute__((aligned(8))) var4);
int (__attribute__((aligned(8))) (var5));
int (__attribute__((aligned(8))) *var6);
int __attribute__((aligned(8))) *var7;

STATIC_ASSERT(__alignof(var1)==8);
STATIC_ASSERT(__alignof(var2)==8);
STATIC_ASSERT(__alignof(var3)==8);
STATIC_ASSERT(__alignof(var4)==8);
STATIC_ASSERT(__alignof(var5)==8);
STATIC_ASSERT(__alignof(var6)==__alignof(void *));
STATIC_ASSERT(__alignof(var7)==8);

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

#ifdef __GNUC__

#define STATIC_ASSERT(a) int __dummy__[(a)?1:-1]

struct { int i; _Bool bit_field : 1; } s;
union { int i; } u;
enum { Econst } e;
int a[10];

STATIC_ASSERT(__builtin_classify_type((int)0)==1);
STATIC_ASSERT(__builtin_classify_type((char)0)==1);
STATIC_ASSERT(__builtin_classify_type(e)==1);
#ifndef __clang__
STATIC_ASSERT(__builtin_classify_type((_Bool)0)==1);
STATIC_ASSERT(__builtin_classify_type(s.bit_field)==1);
#else
STATIC_ASSERT(__builtin_classify_type((_Bool)0)==4);
STATIC_ASSERT(__builtin_classify_type(s.bit_field)==4);
#endif
STATIC_ASSERT(__builtin_classify_type((int *)0)==5);
STATIC_ASSERT(__builtin_classify_type(1.0)==8);
STATIC_ASSERT(__builtin_classify_type(*(0?(void *)0:(double *)0))==8);
STATIC_ASSERT(__builtin_classify_type(*(0?(double *)0:(void *)0))==8);
STATIC_ASSERT(__builtin_classify_type((_Complex double)0)==9);
STATIC_ASSERT(__builtin_classify_type(s)==12);
STATIC_ASSERT(__builtin_classify_type(u)==13);
STATIC_ASSERT(__builtin_classify_type(a)==5);

#endif

int main()
{
}

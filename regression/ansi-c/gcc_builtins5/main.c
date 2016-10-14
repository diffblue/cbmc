#ifdef __GNUC__

typedef unsigned long int uintptr_t;
typedef unsigned long int uint64_t;
typedef long int __intptr_t;

typedef struct
{
  uintptr_t stack_guard;
} tcbhead_t;

struct pthread
{
  union
  {
    tcbhead_t header;
  };
};

#define STATIC_ASSERT(a) int __dummy__[(a)?1:-1]

int main()
{
  uintptr_t stack_chk_guard;
  STATIC_ASSERT(!(__builtin_classify_type ((__typeof__ (stack_chk_guard)) 0) == 5));

  __typeof__((__typeof__ (
                0 ?
                (__typeof__ (
                    (__typeof__ (stack_chk_guard)) 0) *) 0 :
                (void *) (
                  (__builtin_classify_type (
                      (__typeof__ (stack_chk_guard)) 0) == 5))
                )) 0) p1;
  if(*p1<0)
    return 0;

  asm volatile ("movq %q0,%%fs:%P1" : :
  "ir" ((uint64_t) (
      (__typeof__ (
          *(0 ?
            (__typeof__ (
                0 ?
                (__typeof__ (
                    (__typeof__ (stack_chk_guard)) 0) *) 0 :
                (void *) (
                  (__builtin_classify_type (
                      (__typeof__ (stack_chk_guard)) 0) == 5))
                )) 0 :
            (__typeof__ (
                0 ?
                (__intptr_t *) 0 :
                (void *) (
                  !((__builtin_classify_type ((__typeof__ (stack_chk_guard)) 0) == 5))
                  ))
              ) 0))) (stack_chk_guard))),
  "i" (__builtin_offsetof (struct pthread, header.stack_guard)));
}

#else

int main()
{
}

#endif

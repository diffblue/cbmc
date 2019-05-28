#ifdef __GNUC__

struct __va_list_tag;
typedef struct __va_list_tag __va_list_tag;
typedef __builtin_va_list __gnuc_va_list[1U];
typedef __gnuc_va_list va_list[1U];

void foo(int n, ...);

int main()
{
  foo(1, 1u);
  foo(2, 2l);
  foo(3, 3.0);
  return 0;
}

void foo(int n, ...)
{
  va_list args;
  __builtin_va_start((__va_list_tag *)(&args), n);

  switch(n)
  {
  case 1:
    __CPROVER_assert(__builtin_va_arg(&args, unsigned) == 1, "1");
    break;
  case 2:
    __CPROVER_assert(__builtin_va_arg(&args, long) == 2, "2");
    break;
  case 3:
    __CPROVER_assert(__builtin_va_arg(&args, double) == 3.0, "3");
    break;
  }

  __builtin_va_end((__va_list_tag *)(&args));
}

#else

// __builtin_va_list is GCC/Clang-only

int main()
{
}

#endif

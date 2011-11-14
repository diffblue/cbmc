#define GCC_BUILTIN_HEADERS \
  "typedef void* __builtin_va_list;\n" \
  "void __builtin_va_start(void *ap, const void *x);\n" \
  "void __builtin_va_end(void *ap);\n" \
  "void __builtin_va_copy(__builtin_va_list dest, __builtin_va_list src);\n" \
  "int __builtin_constant_p(int);\n" \
  "\n" \
  "int __builtin_abs(int);\n" \
  "long int __builtin_labs(long);\n" \
  "double __builtin_cos(double);\n" \
  "double __builtin_cosf(double);\n" \
  "double __builtin_fabs(double);\n" \
  "double __builtin_fabsf(double);\n" \
  "int __builtin_memcmp(const void *s1, const void *s2, unsigned n);\n" \
  "void *__builtin_memcpy(void *dest, const void *src, unsigned n);\n" \
  "void *__builtin___memcpy_chk(void *dest, const void *src, unsigned n, unsigned size);\n" \
  "char *__builtin___memmove_chk(void *dest, const void *src, unsigned n, unsigned size);\n" \
  "double __builtin_sin(double);\n" \
  "float __builtin_sinf(float);\n" \
  "double __builtin_sqrt(double);\n" \
  "float __builtin_sqrtf(float);\n" \
  "int __builtin_strcmp(const char *s1, const char *s2);\n" \
  "unsigned __builtin_strlen(const char *s);\n" \
  "int __builtin_strncmp(const char *s1, const char *s2, unsigned n);\n" \
  "void __builtin_abort();\n" \
  "void __builtin_prefetch(void *, ...);\n" \
  "int __builtin_printf(const char *fmt, ...);\n" \
  "int __builtin_fprintf(void *stream, const char *fmt, ...);\n" \
  "int __builtin_fscanf(void *stream, const char *fmt, ...);\n" \
  "int __builtin_scanf(const char *str, const char *fmt, ...);\n" \
  "int __builtin_fputs(const char *s, void *stream);\n" \
  "long __builtin_expect(long, long);\n" \
  "void *__builtin_memset(void *s, int c, unsigned n);\n" \
  "void *__builtin___memset_chk(void *s, int c, unsigned n, unsigned size);\n" \
  "char *__builtin_strcat(char *dest, const char *src);\n" \
  "char *__builtin___strcat_chk(char *dest, const char *src, unsigned size);\n" \
  "char *__builtin_strcpy(char *dest, const char *src);\n" \
  "char *__builtin___strcpy_chk(char *dest, const char *src, unsigned size);\n" \
  "char *__builtin_strncpy(char *dest, const char *src, unsigned n);\n" \
  "char *__builtin___strncpy_chk(char *dest, const char *src, unsigned n, unsigned size);\n" \
  "char *__builtin___stpcpy(char *s1, const char *s2);\n" \
  "char *__builtin___stpncpy_chk(char *s1, const char *s2, unsigned n, unsigned size);\n" \
  "void __builtin_exit(int status);\n" \
  "char *__builtin_strchr(const char *s, int c);\n" \
  "unsigned __builtin_strspn(const char *s, const char *accept);\n" \
  "unsigned __builtin_strcspn(const char *s, const char *reject);\n" \
  "char *__builtin_strstr(const char *a, const char *b);\n" \
  "char *__builtin_strpbrk(const char *s, const char *accept);\n" \
  "char *__builtin_strrchr(const char *s, int c);\n" \
  "char *__builtin_strncat(char *dest, const char *src, unsigned n);\n" \
  "char *__builtin___strncat_chk(char *dest, const char *src, unsigned n, unsigned size);\n" \
  "char *__builtin___stpcpy_chk(char *dest, const char *src, unsigned size);\n" \
  "void *__builtin_alloca(unsigned s);\n" \
  "int __builtin_ffs(int i);\n" \
  "char *__builtin_index(const char *s, int c);\n" \
  "char *__builtin_rindex(const char *s, int c);\n" \
  "int __builtin_bcmp(const void *s1, const void *s2, unsigned n);\n" \
  "int __builtin_bzero(void *s, unsigned n);\n" \
  "long double __builtin_sinl(long double x);\n" \
  "long double __builtin_cosl(long double x);\n" \
  "long double __builtin_sqrtl(long double x);\n" \
  "long double __builtin_fabsl(long double x);\n" \
  "int __builtin_popcount(unsigned int x);\n" \
  "int __builtin_popcountll(unsigned long long int x);\n" \
  "float __builtin_huge_valf();\n" \
  "double __builtin_huge_val();\n" \
  "float __builtin_inff();\n" \
  "double __builtin_inf();\n" \
  "float __builtin_nanf(const char *);\n" \
  "double __builtin_nan(const char *);\n" \
  "float __builtin_nansf(const char *);\n" \
  "double __builtin_nans(const char *);\n" \
  "long double __builtin_infl();\n" \
  "unsigned __builtin_object_size();\n" \
  "void *__builtin_return_address(unsigned level);\n" \
  "void *__builtin_extract_return_addr(void *);\n" \
  "int __builtin_choose_expr(_Bool, ...);\n" \
  "int __sync_fetch_and_add(volatile void *, int, ...);\n" \
  "int __sync_fetch_and_sub(volatile void *, int, ...);\n" \
  "int __sync_fetch_and_or(volatile void *, int, ...);\n" \
  "int __sync_fetch_and_and(volatile void *, int, ...);\n" \
  "int __sync_fetch_and_xor(volatile void *, int, ...);\n" \
  "int __sync_fetch_and_nand(volatile void *, int, ...);\n" \
  "int __sync_add_and_fetch(volatile void *, int, ...);\n" \
  "int __sync_sub_and_fetch(volatile void *, int, ...);\n" \
  "int __sync_or_and_fetch(volatile void *, int, ...);\n" \
  "int __sync_and_and_fetch(volatile void *, int, ...);\n" \
  "int __sync_xor_and_fetch(volatile void *, int, ...);\n" \
  "int __sync_nand_and_fetch(volatile void *, int, ...);\n" \
  "_Bool __sync_bool_compare_and_swap(volatile void *, int oldval, int newval, ...);\n" \
  "int __sync_val_compare_and_swap(volatile void *, int oldval, int newval, ...);\n" \
  "void __sync_synchronize();\n" \
  "int __sync_lock_test_and_set(volatile void *, ...);\n" \
  "void __sync_lock_release(volatile void *, ...);\n" \
  "\n\n"

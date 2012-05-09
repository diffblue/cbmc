#define GCC_BUILTIN_HEADERS \
  "typedef void* __builtin_va_list;\n" \
  "void __builtin_va_start(void *ap, ...);\n" \
  "void __builtin_va_end(void *ap);\n" \
  "void __builtin_va_copy(__builtin_va_list dest, __builtin_va_list src);\n" \
  "int __builtin_constant_p(int);\n" \
  "\n" \
  "int __builtin_abs(int);\n" \
  "long int __builtin_labs(long);\n" \
  "double __builtin_cos(double);\n" \
  "float __builtin_cosf(float);\n" \
  "double __builtin_fabs(double);\n" \
  "float __builtin_fabsf(float);\n" \
  "int __builtin_memcmp(const void *s1, const void *s2, unsigned n);\n" \
  "void *__builtin_memcpy(void *dest, const void *src, unsigned n);\n" \
  "void *__builtin___memcpy_chk(void *dest, const void *src, unsigned n, __CPROVER_size_t size);\n" \
  "char *__builtin___memmove_chk(void *dest, const void *src, unsigned n, __CPROVER_size_t size);\n" \
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
  "int __builtin_vsnprintf(char * restrict str, __CPROVER_size_t size, const char * restrict format, __builtin_va_list ap);\n" \
  "long __builtin_expect(long, long);\n" \
  "void *__builtin_memset(void *s, int c, unsigned n);\n" \
  "void *__builtin___memset_chk(void *s, int c, unsigned n, __CPROVER_size_t size);\n" \
  "void *__builtin_memchr(const void *s, int c, __CPROVER_size_t n);\n" \
  "void *__builtin_memmove(void *s1, const void *s2, __CPROVER_size_t n);\n" \
  "char *__builtin_strcat(char *dest, const char *src);\n" \
  "char *__builtin___strcat_chk(char *dest, const char *src, __CPROVER_size_t size);\n" \
  "char *__builtin_strcpy(char *dest, const char *src);\n" \
  "char *__builtin___strcpy_chk(char *dest, const char *src, __CPROVER_size_t size);\n" \
  "char *__builtin_strncpy(char *dest, const char *src, unsigned n);\n" \
  "char *__builtin___strncpy_chk(char *dest, const char *src, unsigned n, __CPROVER_size_t size);\n" \
  "char *__builtin___stpcpy(char *s1, const char *s2);\n" \
  "char *__builtin___stpncpy_chk(char *s1, const char *s2, unsigned n, __CPROVER_size_t size);\n" \
  "void __builtin_exit(int status);\n" \
  "char *__builtin_strchr(const char *s, int c);\n" \
  "unsigned __builtin_strspn(const char *s, const char *accept);\n" \
  "unsigned __builtin_strcspn(const char *s, const char *reject);\n" \
  "char *__builtin_strstr(const char *a, const char *b);\n" \
  "char *__builtin_strpbrk(const char *s, const char *accept);\n" \
  "char *__builtin_strrchr(const char *s, int c);\n" \
  "char *__builtin_strncat(char *dest, const char *src, unsigned n);\n" \
  "char *__builtin___strncat_chk(char *dest, const char *src, unsigned n, __CPROVER_size_t size);\n" \
  "char *__builtin___stpcpy_chk(char *dest, const char *src, __CPROVER_size_t size);\n" \
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
  "float __builtin_acosf(float);\n" \
  "long double __builtin_acosl(long double);\n" \
  "float __builtin_asinf(float);\n" \
  "long double __builtin_asinl(long double);\n" \
  "float __builtin_atanf(float);\n" \
  "long double __builtin_atanl(long double);\n" \
  "float __builtin_atan2f(float, float);\n" \
  "long double __builtin_atan2l(long double, long double);\n" \
  "float __builtin_ceilf(float);\n" \
  "long double __builtin_ceill(long double);\n" \
  "float __builtin_coshf(float);\n" \
  "long double __builtin_coshl(long double);\n" \
  "float __builtin_expf(float);\n" \
  "long double __builtin_expl(long double);\n" \
  "float __builtin_floorf(float);\n" \
  "long double __builtin_floorl(long double);\n" \
  "float __builtin_fmodf(float, float);\n" \
  "long double __builtin_fmodl(long double, long double);\n" \
  "float __builtin_frexpf(float, int*);\n" \
  "long double __builtin_frexpl(long double, int*);\n" \
  "float __builtin_ldexpf(float , int exp);\n" \
  "long double __builtin_ldexpl(long double, int);\n" \
  "float __builtin_logf(float);\n" \
  "long double __builtin_logl(long double);\n" \
  "float __builtin_log10f(float);\n" \
  "long double __builtin_log10l(long double);\n" \
  "float __builtin_modff(float, float*);\n" \
  "long double __builtin_modfl(long double, long double*);\n" \
  "float __builtin_powf(float, float);\n" \
  "long double __builtin_powl(long double, long double);\n" \
  "double __builtin_powi(double, int);\n" \
  "float __builtin_powif(float, int);\n" \
  "long double __builtin_powil(long double, int);\n" \
  "float __builtin_sinhf(float);\n" \
  "long double __builtin_sinhl(long double);\n" \
  "float __builtin_tanf(float);\n" \
  "long double __builtin_tanl(long double);\n" \
  "float __builtin_tanhf(float);\n" \
  "long double __builtin_tanhl(long double);\n" \
  "long double __builtin_parityl(long double);\n" \
  "long double __builtin_parityll(long double);\n" \
  "void __builtin_trap(void);\n" \
  "void __builtin___clear_cache(char *begin, char *end);\n" \
  "int __builtin_clz(unsigned int x);\n" \
  "int __builtin_ctz(unsigned int x);\n" \
  "int __builtin_parity(unsigned int x);\n" \
  "int __builtin_ffsl(unsigned long);\n" \
  "int __builtin_clzl(unsigned long);\n" \
  "int __builtin_ctzl(unsigned long);\n" \
  "long int __builtin_bswap32(long int x);\n" \
  "long long int __builtin_bswap64(long long int x);\n" \
  "typedef int   __gccxml_m64  __attribute__ ((__vector_size__ (8), __may_alias__));\n" \
  "typedef int   __gccxml_v2si __attribute__ ((__vector_size__ (8)));\n" \
  "typedef int   __gccxml_v4si __attribute__ ((__vector_size__ (16)));\n" \
  "typedef short __gccxml_v4hi __attribute__ ((__vector_size__ (8)));\n" \
  "typedef char  __gccxml_v8qi __attribute__ ((__vector_size__ (8)));\n" \
  "typedef float __gccxml_v4sf __attribute__ ((__vector_size__ (16)));\n" \
  "void          __builtin_ia32_emms(void);\n" \
  "int           __builtin_ia32_vec_ext_v2si();\n" \
  "__gccxml_v8qi __builtin_ia32_packsswb();\n" \
  "__gccxml_v4hi __builtin_ia32_packssdw();\n" \
  "__gccxml_v8qi __builtin_ia32_packuswb();\n" \
  "__gccxml_v8qi __builtin_ia32_punpckhbw();\n" \
  "__gccxml_v4hi __builtin_ia32_punpckhwd();\n" \
  "__gccxml_v2si __builtin_ia32_punpckhdq();\n" \
  "__gccxml_v8qi __builtin_ia32_punpcklbw();\n" \
  "__gccxml_v4hi __builtin_ia32_punpcklwd();\n" \
  "__gccxml_v2si __builtin_ia32_punpckldq();\n" \
  "__gccxml_v8qi __builtin_ia32_paddb();\n" \
  "__gccxml_v4hi __builtin_ia32_paddw();\n" \
  "__gccxml_v2si __builtin_ia32_paddd();\n" \
  "__gccxml_m64  __builtin_ia32_paddq();\n" \
  "__gccxml_v8qi __builtin_ia32_paddsb();\n" \
  "__gccxml_v4hi __builtin_ia32_paddsw();\n" \
  "__gccxml_v8qi __builtin_ia32_paddusb();\n" \
  "__gccxml_v4hi __builtin_ia32_paddusw();\n" \
  "__gccxml_v8qi __builtin_ia32_psubb();\n" \
  "__gccxml_v4hi __builtin_ia32_psubw();\n" \
  "__gccxml_v2si __builtin_ia32_psubd();\n" \
  "__gccxml_m64  __builtin_ia32_psubq();\n" \
  "__gccxml_v8qi __builtin_ia32_psubsb();\n" \
  "__gccxml_v4hi __builtin_ia32_psubsw();\n" \
  "__gccxml_v8qi __builtin_ia32_psubusb();\n" \
  "__gccxml_v4hi __builtin_ia32_psubusw();\n" \
  "__gccxml_v2si __builtin_ia32_pmaddwd();\n" \
  "__gccxml_v4hi __builtin_ia32_pmulhw();\n" \
  "__gccxml_v4hi __builtin_ia32_pmullw();\n" \
  "__gccxml_v4hi __builtin_ia32_psllw();\n" \
  "__gccxml_v4hi __builtin_ia32_psllwi();\n" \
  "__gccxml_v2si __builtin_ia32_pslld();\n" \
  "__gccxml_v2si __builtin_ia32_pslldi();\n" \
  "__gccxml_m64  __builtin_ia32_psllq();\n" \
  "__gccxml_m64  __builtin_ia32_psllqi();\n" \
  "__gccxml_v4hi __builtin_ia32_psraw();\n" \
  "__gccxml_v4hi __builtin_ia32_psrawi();\n" \
  "__gccxml_v2si __builtin_ia32_psrad();\n" \
  "__gccxml_v2si __builtin_ia32_psradi();\n" \
  "__gccxml_v4hi __builtin_ia32_psrlw();\n" \
  "__gccxml_v4hi __builtin_ia32_psrlwi();\n" \
  "__gccxml_v2si __builtin_ia32_psrld();\n" \
  "__gccxml_v2si __builtin_ia32_psrldi();\n" \
  "__gccxml_m64  __builtin_ia32_psrlq();\n" \
  "__gccxml_m64  __builtin_ia32_psrlqi();\n" \
  "__gccxml_v2si __builtin_ia32_pand();\n" \
  "__gccxml_v2si __builtin_ia32_pandn();\n" \
  "__gccxml_v2si __builtin_ia32_por();\n" \
  "__gccxml_v2si __builtin_ia32_pxor();\n" \
  "__gccxml_v8qi __builtin_ia32_pcmpeqb();\n" \
  "__gccxml_v8qi __builtin_ia32_pcmpgtb();\n" \
  "__gccxml_v4hi __builtin_ia32_pcmpeqw();\n" \
  "__gccxml_v4hi __builtin_ia32_pcmpgtw();\n" \
  "__gccxml_v2si __builtin_ia32_pcmpeqd();\n" \
  "__gccxml_v2si __builtin_ia32_pcmpgtd();\n" \
  "__gccxml_v2si __builtin_ia32_vec_init_v2si();\n" \
  "__gccxml_v4hi __builtin_ia32_vec_init_v4hi();\n" \
  "__gccxml_v8qi __builtin_ia32_vec_init_v8qi();\n" \
  "int __builtin_ia32_comieq (__gccxml_v4sf, __gccxml_v4sf);\n" \
  "int __builtin_ia32_comineq (__gccxml_v4sf, __gccxml_v4sf);\n" \
  "int __builtin_ia32_comilt (__gccxml_v4sf, __gccxml_v4sf);\n" \
  "int __builtin_ia32_comile (__gccxml_v4sf, __gccxml_v4sf);\n" \
  "int __builtin_ia32_comigt (__gccxml_v4sf, __gccxml_v4sf);\n" \
  "int __builtin_ia32_comige (__gccxml_v4sf, __gccxml_v4sf);\n" \
  "int __builtin_ia32_ucomieq (__gccxml_v4sf, __gccxml_v4sf);\n" \
  "int __builtin_ia32_ucomineq (__gccxml_v4sf, __gccxml_v4sf);\n" \
  "int __builtin_ia32_ucomilt (__gccxml_v4sf, __gccxml_v4sf);\n" \
  "int __builtin_ia32_ucomile (__gccxml_v4sf, __gccxml_v4sf);\n" \
  "int __builtin_ia32_ucomigt (__gccxml_v4sf, __gccxml_v4sf);\n" \
  "int __builtin_ia32_ucomige (__gccxml_v4sf, __gccxml_v4sf);\n" \
  "__gccxml_v4sf __builtin_ia32_addps (__gccxml_v4sf, __gccxml_v4sf);\n" \
  "__gccxml_v4sf __builtin_ia32_subps (__gccxml_v4sf, __gccxml_v4sf);\n" \
  "__gccxml_v4sf __builtin_ia32_mulps (__gccxml_v4sf, __gccxml_v4sf);\n" \
  "__gccxml_v4sf __builtin_ia32_divps (__gccxml_v4sf, __gccxml_v4sf);\n" \
  "__gccxml_v4sf __builtin_ia32_addss (__gccxml_v4sf, __gccxml_v4sf);\n" \
  "__gccxml_v4sf __builtin_ia32_subss (__gccxml_v4sf, __gccxml_v4sf);\n" \
  "__gccxml_v4sf __builtin_ia32_mulss (__gccxml_v4sf, __gccxml_v4sf);\n" \
  "__gccxml_v4sf __builtin_ia32_divss (__gccxml_v4sf, __gccxml_v4sf);\n" \
  "__gccxml_v4si __builtin_ia32_cmpeqps (__gccxml_v4sf, __gccxml_v4sf);\n" \
  "__gccxml_v4si __builtin_ia32_cmpltps (__gccxml_v4sf, __gccxml_v4sf);\n" \
  "__gccxml_v4si __builtin_ia32_cmpleps (__gccxml_v4sf, __gccxml_v4sf);\n" \
  "__gccxml_v4si __builtin_ia32_cmpgtps (__gccxml_v4sf, __gccxml_v4sf);\n" \
  "__gccxml_v4si __builtin_ia32_cmpgeps (__gccxml_v4sf, __gccxml_v4sf);\n" \
  "__gccxml_v4si __builtin_ia32_cmpunordps (__gccxml_v4sf, __gccxml_v4sf);\n" \
  "__gccxml_v4si __builtin_ia32_cmpneqps (__gccxml_v4sf, __gccxml_v4sf);\n" \
  "__gccxml_v4si __builtin_ia32_cmpnltps (__gccxml_v4sf, __gccxml_v4sf);\n" \
  "__gccxml_v4si __builtin_ia32_cmpnleps (__gccxml_v4sf, __gccxml_v4sf);\n" \
  "__gccxml_v4si __builtin_ia32_cmpngtps (__gccxml_v4sf, __gccxml_v4sf);\n" \
  "__gccxml_v4si __builtin_ia32_cmpngeps (__gccxml_v4sf, __gccxml_v4sf);\n" \
  "__gccxml_v4si __builtin_ia32_cmpordps (__gccxml_v4sf, __gccxml_v4sf);\n" \
  "__gccxml_v4si __builtin_ia32_cmpeqss (__gccxml_v4sf, __gccxml_v4sf);\n" \
  "__gccxml_v4si __builtin_ia32_cmpltss (__gccxml_v4sf, __gccxml_v4sf);\n" \
  "__gccxml_v4si __builtin_ia32_cmpless (__gccxml_v4sf, __gccxml_v4sf);\n" \
  "__gccxml_v4si __builtin_ia32_cmpgtss (__gccxml_v4sf, __gccxml_v4sf);\n" \
  "__gccxml_v4si __builtin_ia32_cmpgess (__gccxml_v4sf, __gccxml_v4sf);\n" \
  "__gccxml_v4si __builtin_ia32_cmpunordss (__gccxml_v4sf, __gccxml_v4sf);\n" \
  "__gccxml_v4si __builtin_ia32_cmpneqss (__gccxml_v4sf, __gccxml_v4sf);\n" \
  "__gccxml_v4si __builtin_ia32_cmpnlts (__gccxml_v4sf, __gccxml_v4sf);\n" \
  "__gccxml_v4si __builtin_ia32_cmpnless (__gccxml_v4sf, __gccxml_v4sf);\n" \
  "__gccxml_v4si __builtin_ia32_cmpngtss (__gccxml_v4sf, __gccxml_v4sf);\n" \
  "__gccxml_v4si __builtin_ia32_cmpngess (__gccxml_v4sf, __gccxml_v4sf);\n" \
  "__gccxml_v4si __builtin_ia32_cmpordss (__gccxml_v4sf, __gccxml_v4sf);\n" \
  "__gccxml_v4sf __builtin_ia32_maxps (__gccxml_v4sf, __gccxml_v4sf);\n" \
  "__gccxml_v4sf __builtin_ia32_maxss (__gccxml_v4sf, __gccxml_v4sf);\n" \
  "__gccxml_v4sf __builtin_ia32_minps (__gccxml_v4sf, __gccxml_v4sf);\n" \
  "__gccxml_v4sf __builtin_ia32_minss (__gccxml_v4sf, __gccxml_v4sf);\n" \
  "__gccxml_v4sf __builtin_ia32_andps (__gccxml_v4sf, __gccxml_v4sf);\n" \
  "__gccxml_v4sf __builtin_ia32_andnps (__gccxml_v4sf, __gccxml_v4sf);\n" \
  "__gccxml_v4sf __builtin_ia32_orps (__gccxml_v4sf, __gccxml_v4sf);\n" \
  "__gccxml_v4sf __builtin_ia32_xorps (__gccxml_v4sf, __gccxml_v4sf);\n" \
  "__gccxml_v4sf __builtin_ia32_movss (__gccxml_v4sf, __gccxml_v4sf);\n" \
  "__gccxml_v4sf __builtin_ia32_movhlps (__gccxml_v4sf, __gccxml_v4sf);\n" \
  "__gccxml_v4sf __builtin_ia32_movlhps (__gccxml_v4sf, __gccxml_v4sf);\n" \
  "__gccxml_v4sf __builtin_ia32_unpckhps (__gccxml_v4sf, __gccxml_v4sf);\n" \
  "__gccxml_v4sf __builtin_ia32_unpcklps (__gccxml_v4sf, __gccxml_v4sf);\n" \
  "__gccxml_v4sf __builtin_ia32_cvtpi2ps (__gccxml_v4sf, __gccxml_v2si);\n" \
  "__gccxml_v4sf __builtin_ia32_cvtsi2ss (__gccxml_v4sf, int);\n" \
  "__gccxml_v2si __builtin_ia32_cvtps2pi (__gccxml_v4sf);\n" \
  "int __builtin_ia32_cvtss2si (__gccxml_v4sf);\n" \
  "__gccxml_v2si __builtin_ia32_cvttps2pi (__gccxml_v4sf);\n" \
  "int __builtin_ia32_cvttss2si (__gccxml_v4sf);\n" \
  "__gccxml_v4sf __builtin_ia32_rcpps (__gccxml_v4sf);\n" \
  "__gccxml_v4sf __builtin_ia32_rsqrtps (__gccxml_v4sf);\n" \
  "__gccxml_v4sf __builtin_ia32_sqrtps (__gccxml_v4sf);\n" \
  "__gccxml_v4sf __builtin_ia32_rcpss (__gccxml_v4sf);\n" \
  "__gccxml_v4sf __builtin_ia32_rsqrtss (__gccxml_v4sf);\n" \
  "__gccxml_v4sf __builtin_ia32_sqrtss (__gccxml_v4sf);\n" \
  "__gccxml_v4sf __builtin_ia32_shufps (__gccxml_v4sf, __gccxml_v4sf, int);\n" \
  "void __builtin_ia32_movntps (float *, __gccxml_v4sf);\n" \
  "int __builtin_ia32_movmskps (__gccxml_v4sf);\n" \
  "\n\n"

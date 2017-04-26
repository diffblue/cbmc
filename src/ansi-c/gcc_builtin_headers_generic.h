typedef void ** __builtin_va_list;
typedef void ** __builtin_ms_va_list;

// stdarg
void* __builtin_apply_args();
void __builtin_ms_va_end(void *ap);
void __builtin_ms_va_start(void *ap, ...);
void* __builtin_next_arg();
int __builtin_va_arg_pack();
int __builtin_va_arg_pack_len();
void __builtin_va_copy(__builtin_va_list dest, __builtin_va_list src);
void __builtin_va_end(void *ap);
void __builtin_va_start(void *ap, ...);

// stdlib
void __builtin__Exit(int);
void __builtin__exit(int);
void __builtin_abort();
int __builtin_execl(const char*, const char*, ...);
int __builtin_execle(const char*, const char*, ...);
int __builtin_execlp(const char*, const char*, ...);
int __builtin_execv(const char*, const char**);
int __builtin_execve(const char*, const char**, const char**);
int __builtin_execvp(const char*, const char**);
void __builtin_exit(int);

// stdio
int __builtin___fprintf_chk(void*, int, const char*, ...);
int __builtin___printf_chk(int, const char*, ...);
int __builtin___snprintf_chk(char*, __CPROVER_size_t, int, __CPROVER_size_t, const char*, ...);
int __builtin___sprintf_chk(char*, int, __CPROVER_size_t, const char*, ...);
int __builtin___vfprintf_chk(void*, int, const char*, __builtin_va_list);
int __builtin___vprintf_chk(int, const char*, __builtin_va_list);
int __builtin___vsnprintf_chk (char *s, __CPROVER_size_t maxlen, int flag, __CPROVER_size_t os, const char *fmt, __builtin_va_list ap);
int __builtin___vsnprintf_chk(char*, __CPROVER_size_t, int, __CPROVER_size_t, const char*, __builtin_va_list);
int __builtin___vsprintf_chk(char*, int, __CPROVER_size_t, const char*, __builtin_va_list);
long __builtin_expect(long, long);
int __builtin_fprintf(void *stream, const char *fmt, ...);
int __builtin_fprintf_unlocked(void*, const char*, ...);
int __builtin_fputc(int, void*);
int __builtin_fputc_unlocked(int, void*);
int __builtin_fputs(const char *s, void *stream);
int __builtin_fputs_unlocked(const char*, void*);
int __builtin_fscanf(void *stream, const char *fmt, ...);
__CPROVER_size_t __builtin_fwrite(const void*, __CPROVER_size_t, __CPROVER_size_t, void*);
__CPROVER_size_t __builtin_fwrite_unlocked(const void*, __CPROVER_size_t, __CPROVER_size_t, void*);
int __builtin_printf(const char*, ...);
int __builtin_printf_unlocked(const char*, ...);
int __builtin_putc(int, void*);
int __builtin_putc_unlocked(int, void*);
int __builtin_putchar(int);
int __builtin_putchar_unlocked(int);
int __builtin_puts(const char*);
int __builtin_puts_unlocked(const char*);
int __builtin_scanf(const char *str, const char *fmt, ...);
int __builtin_snprintf(char*, __CPROVER_size_t, const char*, ...);
int __builtin_sprintf(char*, const char*, ...);
int __builtin_sscanf(const char*, const char*, ...);
int __builtin_vfprintf(void*, const char*, __builtin_va_list);
int __builtin_vfscanf(void*, const char*, __builtin_va_list);
int __builtin_vprintf(const char*, __builtin_va_list);
int __builtin_vscanf(const char*, __builtin_va_list);
int __builtin_vsnprintf(char*, __CPROVER_size_t, const char*, __builtin_va_list);
int __builtin_vsprintf(char*, const char*, __builtin_va_list);
int __builtin_vsscanf(const char*, const char*, __builtin_va_list);

// atomics
int __sync_fetch_and_add();
int __sync_fetch_and_sub();
int __sync_fetch_and_or();
int __sync_fetch_and_and();
int __sync_fetch_and_xor();
int __sync_fetch_and_nand();
int __sync_add_and_fetch();
int __sync_sub_and_fetch();
int __sync_or_and_fetch();
int __sync_and_and_fetch();
int __sync_xor_and_fetch();
int __sync_nand_and_fetch();
_Bool __sync_bool_compare_and_swap();
int __sync_val_compare_and_swap();
void __sync_synchronize();
int __sync_lock_test_and_set();
void __sync_lock_release();

// other
int __builtin_choose_expr(_Bool, ...);
int __builtin_classify_type();
int __builtin_constant_p();
void __builtin_trap(void);
void __builtin_unreachable(void);

void* __builtin_dwarf_cfa();
unsigned __builtin_dwarf_sp_column();
int __builtin_eh_return_data_regno(int);
void __builtin_init_dwarf_reg___CPROVER_size_table(void*);
void __builtin_unwind_init();

const char* __builtin_FILE();
const char* __builtin_FUNCTION();
int __builtin_LINE();

void __builtin_longjmp(void*, int);
void __builtin_return(void*);
void* __builtin_saveregs();
int __builtin_setjmp(void*);
void __builtin_update_setjmp_buf(void*);


typedef int    __gcc_m64   __attribute__ ((__vector_size__ (8), __may_alias__));

typedef char   __gcc_v8qi  __attribute__ ((__vector_size__ (8)));
typedef char   __gcc_v16qi __attribute__ ((__vector_size__ (16)));
typedef char   __gcc_v32qi __attribute__ ((__vector_size__ (32)));
typedef char   __gcc_v64qi __attribute__ ((__vector_size__ (64)));
typedef int    __gcc_v2si  __attribute__ ((__vector_size__ (8)));
typedef int    __gcc_v4si  __attribute__ ((__vector_size__ (16)));
typedef int    __gcc_v8si  __attribute__ ((__vector_size__ (32)));
typedef int    __gcc_v16si  __attribute__ ((__vector_size__ (64)));
typedef short  __gcc_v4hi  __attribute__ ((__vector_size__ (8)));
typedef short  __gcc_v8hi  __attribute__ ((__vector_size__ (16)));
typedef short  __gcc_v16hi __attribute__ ((__vector_size__ (32)));
typedef short  __gcc_v32hi __attribute__ ((__vector_size__ (64)));
typedef float  __gcc_v2sf  __attribute__ ((__vector_size__ (8)));
typedef float  __gcc_v4sf  __attribute__ ((__vector_size__ (16)));
typedef float  __gcc_v8sf  __attribute__ ((__vector_size__ (32)));
typedef float  __gcc_v16sf  __attribute__ ((__vector_size__ (64)));
typedef double __gcc_v2df  __attribute__ ((__vector_size__ (16)));
typedef double __gcc_v4df  __attribute__ ((__vector_size__ (32)));
typedef double __gcc_v8df  __attribute__ ((__vector_size__ (64)));
typedef long long __gcc_v1di __attribute__ ((__vector_size__ (8)));
typedef long long __gcc_v2di __attribute__ ((__vector_size__ (16)));
typedef long long __gcc_v4di __attribute__ ((__vector_size__ (32)));
typedef long long __gcc_v8di __attribute__ ((__vector_size__ (64)));
typedef unsigned long long __gcc_di;

enum __gcc_atomic_memmodels {
  __ATOMIC_RELAXED, __ATOMIC_CONSUME, __ATOMIC_ACQUIRE, __ATOMIC_RELEASE, __ATOMIC_ACQ_REL, __ATOMIC_SEQ_CST
};

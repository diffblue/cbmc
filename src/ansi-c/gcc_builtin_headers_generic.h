// clang-format off
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
void __sync_synchronize();
_Bool __atomic_test_and_set(void *, int);
void __atomic_clear(_Bool *, int);
void __atomic_thread_fence(int);
void __atomic_signal_fence(int);
_Bool __atomic_always_lock_free(__CPROVER_size_t, void *);
_Bool __atomic_is_lock_free(__CPROVER_size_t, void *);

// other
int __builtin_choose_expr(_Bool, ...);
int __builtin_classify_type();
int __builtin_constant_p(int);
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
// clang-format on

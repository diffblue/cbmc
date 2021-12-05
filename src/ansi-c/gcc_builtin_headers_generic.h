// clang-format off
// stdarg
void* __builtin_apply_args();
void* __builtin_apply(void (*)(), void*, __CPROVER_size_t);
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
pid_t __builtin_fork();

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
long __builtin_expect(long, long);
long __builtin_expect_with_probability(long, long, double);
void __builtin_clear_padding();
void __builtin_speculation_safe_value();
void* __builtin_speculation_safe_value_ptr(void*, ...);

void* __builtin_dwarf_cfa();
unsigned __builtin_dwarf_sp_column();
int __builtin_eh_return_data_regno(int);
void __builtin_init_dwarf_reg_size_table(void*);
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

/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_ANSI_C_LIBRARY_CPROVER_H
#define CPROVER_ANSI_C_LIBRARY_CPROVER_H

typedef __typeof__(sizeof(int)) __CPROVER_size_t;
void *__CPROVER_allocate(__CPROVER_size_t size, __CPROVER_bool zero);
extern const void *__CPROVER_deallocated;
extern const void *__CPROVER_malloc_object;
extern _Bool __CPROVER_malloc_is_new_array;
extern const void *__CPROVER_memory_leak;

extern int __CPROVER_malloc_failure_mode;
extern __CPROVER_size_t __CPROVER_max_malloc_size;
extern _Bool __CPROVER_malloc_may_fail;

// malloc failure modes
extern int __CPROVER_malloc_failure_mode_return_null;
extern int __CPROVER_malloc_failure_mode_assert_then_assume;

void __CPROVER_assume(__CPROVER_bool assumption) __attribute__((__noreturn__));
void __CPROVER_assert(__CPROVER_bool assertion, const char *description);
void __CPROVER_precondition(__CPROVER_bool assertion, const char *description);
void __CPROVER_postcondition(__CPROVER_bool assertion, const char *description);

_Bool __CPROVER_is_zero_string(const void *);
__CPROVER_size_t __CPROVER_zero_string_length(const void *);
__CPROVER_size_t __CPROVER_buffer_size(const void *);
__CPROVER_bool __CPROVER_r_ok();
__CPROVER_bool __CPROVER_w_ok();
__CPROVER_bool __CPROVER_rw_ok();

#if 0
__CPROVER_bool __CPROVER_equal();
__CPROVER_bool __CPROVER_same_object(const void *, const void *);

const unsigned __CPROVER_constant_infinity_uint;
typedef void __CPROVER_integer;
typedef void __CPROVER_rational;
void __CPROVER_initialize(void);
void __CPROVER_cover(__CPROVER_bool condition);
#endif

void __CPROVER_printf(const char *format, ...);
void __CPROVER_input(const char *id, ...);
void __CPROVER_output(const char *id, ...);

// concurrency-related
void __CPROVER_atomic_begin();
void __CPROVER_atomic_end();
void __CPROVER_fence(const char *kind, ...);
#if 0
__CPROVER_thread_local unsigned long __CPROVER_thread_id=0;
__CPROVER_bool __CPROVER_threads_exited[__CPROVER_constant_infinity_uint];
unsigned long __CPROVER_next_thread_id=0;

// traces
void CBMC_trace(int lvl, const char *event, ...);
#endif

// pointers
unsigned __CPROVER_POINTER_OBJECT(const void *p);
signed __CPROVER_POINTER_OFFSET(const void *p);
__CPROVER_bool __CPROVER_DYNAMIC_OBJECT(const void *p);
#if 0
extern unsigned char __CPROVER_memory[__CPROVER_constant_infinity_uint];
void __CPROVER_allocated_memory(
  __CPROVER_size_t address, __CPROVER_size_t extent);

// this is ANSI-C
extern __CPROVER_thread_local const char __func__[__CPROVER_constant_infinity_uint];

// this is GCC
extern __CPROVER_thread_local const char __FUNCTION__[__CPROVER_constant_infinity_uint];
extern __CPROVER_thread_local const char __PRETTY_FUNCTION__[__CPROVER_constant_infinity_uint];
#endif

// float stuff
int __CPROVER_fpclassify(int, int, int, int, int, ...);
__CPROVER_bool __CPROVER_isfinite(double f);
__CPROVER_bool __CPROVER_isinf(double f);
__CPROVER_bool __CPROVER_isnormal(double f);
__CPROVER_bool __CPROVER_sign(double f);
__CPROVER_bool __CPROVER_isnanf(float f);
__CPROVER_bool __CPROVER_isnand(double f);
__CPROVER_bool __CPROVER_isnanld(long double f);
__CPROVER_bool __CPROVER_isfinitef(float f);
__CPROVER_bool __CPROVER_isfinited(double f);
__CPROVER_bool __CPROVER_isfiniteld(long double f);
__CPROVER_bool __CPROVER_isinff(float f);
__CPROVER_bool __CPROVER_isinfd(double f);
__CPROVER_bool __CPROVER_isinfld(long double f);
__CPROVER_bool __CPROVER_isnormalf(float f);
__CPROVER_bool __CPROVER_isnormald(double f);
__CPROVER_bool __CPROVER_isnormalld(long double f);
__CPROVER_bool __CPROVER_signf(float f);
__CPROVER_bool __CPROVER_signd(double f);
__CPROVER_bool __CPROVER_signld(long double f);
double __CPROVER_inf(void);
float __CPROVER_inff(void);
long double __CPROVER_infl(void);
//extern int __CPROVER_thread_local __CPROVER_rounding_mode;
int __CPROVER_isgreaterd(double f, double g);

// absolute value
int __CPROVER_abs(int);
long int __CPROVER_labs(long int);
long long int __CPROVER_llabs(long long int);
double __CPROVER_fabs(double);
long double __CPROVER_fabsl(long double);
float __CPROVER_fabsf(float);

// modulo and remainder
double __CPROVER_fmod(double, double);
float __CPROVER_fmodf(float, float);
long double __CPROVER_fmodl(long double, long double);
double __CPROVER_remainder(double, double);
float __CPROVER_remainderf(float, float);
long double __CPROVER_remainderl(long double, long double);

// arrays
//__CPROVER_bool __CPROVER_array_equal(const void *array1, const void *array2);
void __CPROVER_array_copy(const void *dest, const void *src);
void __CPROVER_array_set(const void *dest, ...);
void __CPROVER_array_replace(const void *dest, const void *src);

#if 0
// k-induction
void __CPROVER_k_induction_hint(unsigned min, unsigned max,
unsigned step, unsigned loop_free);

// manual specification of predicates
void __CPROVER_predicate(__CPROVER_bool predicate);
void __CPROVER_parameter_predicates();
void __CPROVER_return_predicates();
#endif

// pipes, write, read, close
struct __CPROVER_pipet {
  _Bool widowed;
  char data[4];
  short next_avail;
  short next_unread;
};
#if 0
extern struct __CPROVER_pipet __CPROVER_pipes[__CPROVER_constant_infinity_uint];
// offset to make sure we don't collide with other fds
extern const int __CPROVER_pipe_offset;
extern unsigned __CPROVER_pipe_count;
#endif

void __CPROVER_set_must(const void *, const char *);
void __CPROVER_set_may(const void *, const char *);
void __CPROVER_clear_must(const void *, const char *);
void __CPROVER_clear_may(const void *, const char *);
void __CPROVER_cleanup(const void *, void (*)(void *));
__CPROVER_bool __CPROVER_get_must(const void *, const char *);
__CPROVER_bool __CPROVER_get_may(const void *, const char *);

#define __CPROVER_danger_number_of_ops 1
#define __CPROVER_danger_max_solution_size 1
#define __CPROVER_danger_number_of_vars 1
#define __CPROVER_danger_number_of_consts 1

// detect overflow
__CPROVER_bool __CPROVER_overflow_minus();
__CPROVER_bool __CPROVER_overflow_mult();
__CPROVER_bool __CPROVER_overflow_plus();
__CPROVER_bool __CPROVER_overflow_shl();
__CPROVER_bool __CPROVER_overflow_unary_minus();

#endif // CPROVER_ANSI_C_LIBRARY_CPROVER_H

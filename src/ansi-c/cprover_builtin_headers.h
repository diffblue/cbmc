void __CPROVER_assume(__CPROVER_bool assumption);
void __VERIFIER_assume(__CPROVER_bool assumption);
void __CPROVER_assert(__CPROVER_bool assertion, const char *description);
void __CPROVER_precondition(__CPROVER_bool precondition, const char *description);
void __CPROVER_postcondition(__CPROVER_bool assertion, const char *description);
void __CPROVER_havoc_object(void *);
void __CPROVER_havoc_slice(void *, __CPROVER_size_t);
__CPROVER_bool __CPROVER_equal();
__CPROVER_bool __CPROVER_same_object(const void *, const void *);
__CPROVER_bool __CPROVER_is_invalid_pointer(const void *);
_Bool __CPROVER_is_zero_string(const void *);
__CPROVER_size_t __CPROVER_zero_string_length(const void *);
__CPROVER_size_t __CPROVER_buffer_size(const void *);
__CPROVER_bool __CPROVER_r_ok();
__CPROVER_bool __CPROVER_w_ok();
__CPROVER_bool __CPROVER_rw_ok();

// bitvector analysis
__CPROVER_bool __CPROVER_get_flag(const void *, const char *);
void __CPROVER_set_must(const void *, const char *);
void __CPROVER_clear_must(const void *, const char *);
void __CPROVER_set_may(const void *, const char *);
void __CPROVER_clear_may(const void *, const char *);
void __CPROVER_cleanup(const void *, const void *);
__CPROVER_bool __CPROVER_get_must(const void *, const char *);
__CPROVER_bool __CPROVER_get_may(const void *, const char *);

void __CPROVER_printf(const char *format, ...);
void __CPROVER_input(const char *id, ...);
void __CPROVER_output(const char *id, ...);
void __CPROVER_cover(__CPROVER_bool condition);

// concurrency-related
void __CPROVER_atomic_begin();
void __CPROVER_atomic_end();
void __CPROVER_fence(const char *kind, ...);

// contract-related functions
__CPROVER_bool __CPROVER_is_fresh(const void *mem, __CPROVER_size_t size);
void __CPROVER_old(const void *);
void __CPROVER_loop_entry(const void *);

// pointers
__CPROVER_size_t __CPROVER_POINTER_OBJECT(const void *);
__CPROVER_ssize_t __CPROVER_POINTER_OFFSET(const void *);
__CPROVER_size_t __CPROVER_OBJECT_SIZE(const void *);
__CPROVER_bool __CPROVER_DYNAMIC_OBJECT(const void *);
void __CPROVER_allocated_memory(__CPROVER_size_t address, __CPROVER_size_t extent);

// float stuff
int __CPROVER_fpclassify(int, int, int, int, int, ...);
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
int __CPROVER_isgreaterf(float f, float g);
int __CPROVER_isgreaterd(double f, double g);
int __CPROVER_isgreaterequalf(float f, float g);
int __CPROVER_isgreaterequald(double f, double g);
int __CPROVER_islessf(float f, float g);
int __CPROVER_islessd(double f, double g);
int __CPROVER_islessequalf(float f, float g);
int __CPROVER_islessequald(double f, double g);
int __CPROVER_islessgreaterf(float f, float g);
int __CPROVER_islessgreaterd(double f, double g);
int __CPROVER_isunorderedf(float f, float g);
int __CPROVER_isunorderedd(double f, double g);

// absolute value
int __CPROVER_abs(int x);
long int __CPROVER_labs(long int x);
long int __CPROVER_llabs(long long int x);
double __CPROVER_fabs(double x);
long double __CPROVER_fabsl(long double x);
float __CPROVER_fabsf(float x);

// modulo and remainder
double __CPROVER_fmod(double, double);
float __CPROVER_fmodf(float, float);
long double __CPROVER_fmodl(long double, long double);
double __CPROVER_remainder(double, double);
float __CPROVER_remainderf(float, float);
long double __CPROVER_remainderl(long double, long double);

// arrays
__CPROVER_bool __CPROVER_array_equal(const void *array1, const void *array2);
// overwrite all of *dest (possibly using nondet values), even
// if *src is smaller
void __CPROVER_array_copy(const void *dest, const void *src);
// replace at most size-of-*src bytes in *dest
void __CPROVER_array_replace(const void *dest, const void *src);
void __CPROVER_array_set(const void *dest, ...);

// k-induction
void __CPROVER_k_induction_hint(unsigned min, unsigned max, 
  unsigned step, unsigned loop_free);

// format string-related
int __CPROVER_scanf(const char *, ...);

// detect overflow
__CPROVER_bool __CPROVER_overflow_minus();
__CPROVER_bool __CPROVER_overflow_mult();
__CPROVER_bool __CPROVER_overflow_plus();
__CPROVER_bool __CPROVER_overflow_shl();
__CPROVER_bool __CPROVER_overflow_unary_minus();

// enumerations
__CPROVER_bool __CPROVER_enum_is_in_range();

typedef __typeof__(sizeof(int)) __CPROVER_size_t;
void *__CPROVER_malloc(__CPROVER_size_t size);
extern const void *__CPROVER_deallocated;
extern const void *__CPROVER_malloc_object;
extern __CPROVER_size_t __CPROVER_malloc_size;
extern _Bool __CPROVER_malloc_is_new_array;

void __CPROVER_assume(__CPROVER_bool assumption) __attribute__((__noreturn__));
void __CPROVER_assert(__CPROVER_bool assertion, const char *description);

__CPROVER_bool __CPROVER_is_zero_string(const void *);
__CPROVER_size_t __CPROVER_zero_string_length(const void *);
__CPROVER_size_t __CPROVER_buffer_size(const void *);

#if 0
__CPROVER_bool __CPROVER_equal();
__CPROVER_bool __CPROVER_same_object(const void *, const void *);

const unsigned __CPROVER_constant_infinity_uint;
typedef void __CPROVER_integer;
typedef void __CPROVER_rational;
void __CPROVER_initialize(void);
void __CPROVER_input(const char *id, ...);
void __CPROVER_output(const char *id, ...);
void __CPROVER_cover(__CPROVER_bool condition);
#endif

// concurrency-related
void __CPROVER_atomic_begin();
void __CPROVER_atomic_end();
void __CPROVER_fence(const char *kind, ...);
#if 0
unsigned long long __CPROVER_threads_exited=0;
unsigned long __CPROVER_next_thread_id=0;

// traces
void CBMC_trace(int lvl, const char *event, ...);
#endif

// pointers
//unsigned __CPROVER_POINTER_OBJECT(const void *p);
signed __CPROVER_POINTER_OFFSET(const void *p);
__CPROVER_bool __CPROVER_DYNAMIC_OBJECT(const void *p);
#if 0
extern unsigned char __CPROVER_memory[__CPROVER_constant_infinity_uint];

// this is ANSI-C
extern __CPROVER_thread_local const char __func__[__CPROVER_constant_infinity_uint];

// this is GCC
extern __CPROVER_thread_local const char __FUNCTION__[__CPROVER_constant_infinity_uint];
extern __CPROVER_thread_local const char __PRETTY_FUNCTION__[__CPROVER_constant_infinity_uint];
#endif

// float stuff
__CPROVER_bool __CPROVER_isnan(double f);
__CPROVER_bool __CPROVER_isfinite(double f);
__CPROVER_bool __CPROVER_isinf(double f);
__CPROVER_bool __CPROVER_isnormal(double f);
__CPROVER_bool __CPROVER_sign(double f);
double __CPROVER_inf(void);
float __CPROVER_inff(void);
//extern int __CPROVER_thread_local __CPROVER_rounding_mode;

// absolute value
int __CPROVER_abs(int x);
long int __CPROVER_labs(long int x);
double __CPROVER_fabs(double x);
long double __CPROVER_fabsl(long double x);
float __CPROVER_fabsf(float x);

// arrays
//__CPROVER_bool __CPROVER_array_equal(const void *array1, const void *array2);
void __CPROVER_array_copy(const void *dest, const void *src);
//void __CPROVER_array_set(const void *dest, ...);

#if 0
// k-induction
void __CPROVER_k_induction_hint(unsigned min, unsigned max,
unsigned step, unsigned loop_free);

// manual specification of predicates
void __CPROVER_predicate(__CPROVER_bool predicate);
void __CPROVER_parameter_predicates();
void __CPROVER_return_predicates();

// pipes, write, read, close
struct __CPROVER_pipet {
  _Bool widowed;
  char data[4];
  short next_avail;
  short next_unread;
};
struct __CPROVER_pipet __CPROVER_pipes[3];
// magic offset to make sure we don't collide with other fds
const int __CPROVER_magic_pipe_offset=42;
#endif


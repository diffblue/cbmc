// Regression: Clang __c11_atomic_* intrinsics must be declared so that
// libc++'s <atomic> header processes without "symbol '__c11_atomic_X'
// is unknown" errors.  Missing these declarations poisons <atomic>
// and cascades into <string>, <thread>, <condition_variable>, and
// <system_error> on macOS.
//
// The intrinsics themselves are stubs ("no body for callee").  This
// test just takes their address to pin down that the symbols are
// visible from user code — if CBMC fails to parse the declarations,
// type-checking reports "symbol '__c11_atomic_thread_fence' is
// unknown" and the whole translation unit aborts.

typedef void (*fn_void_int)(int);
typedef void (*fn_volatile_variadic)(volatile void *, ...);

fn_void_int t_fence = &__c11_atomic_thread_fence;
fn_void_int s_fence = &__c11_atomic_signal_fence;
fn_volatile_variadic atomic_store = &__c11_atomic_store;
fn_volatile_variadic atomic_exchange = &__c11_atomic_exchange;
fn_volatile_variadic atomic_fetch_add = &__c11_atomic_fetch_add;

int main()
{
  __CPROVER_assert(t_fence != 0, "thread_fence declared");
  __CPROVER_assert(s_fence != 0, "signal_fence declared");
  __CPROVER_assert(atomic_store != 0, "store declared");
  __CPROVER_assert(atomic_exchange != 0, "exchange declared");
  __CPROVER_assert(atomic_fetch_add != 0, "fetch_add declared");
  return 0;
}

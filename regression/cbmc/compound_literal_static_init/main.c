#include <assert.h>

// A compound literal with constant contents is a valid constant initializer
// for a static object.  CBMC's is_compile_time_constantt did not list
// ID_compound_literal, so this failed with "expected constant expression".
// This is the kernel's DEFINE_RATELIMIT_STATE / pr_*_ratelimited pattern:
//   static struct ratelimit_state _rs = { .lock = (raw_spinlock_t){...}, ... };
typedef struct
{
  struct
  {
    union
    {
      int val;
    };
  } raw_lock;
} raw_spinlock_t;

struct rl
{
  raw_spinlock_t lock;
  int interval;
};

int main(void)
{
  static struct rl r = {
    .lock = (raw_spinlock_t){.raw_lock = {{.val = 0}}},
    .interval = 5000,
  };
  assert(r.interval == 5000);
  assert(r.lock.raw_lock.val == 0);
  return 0;
}

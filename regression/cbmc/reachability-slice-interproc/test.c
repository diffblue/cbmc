#include <assert.h>

// After a reachability slice based on the assertion in `target`, we should
// retain both its possible callers (...may_call_target_1, ...may_call_target_2)
// and their callees, but should be more precise concerning before_target and
// after_target, which even though they are also called by
// `unreachable_calls_before_target` and `unreachable_calls_after_target`, those
// functions are not reachable.

void before_target()
{
  const char *local = "before_target_kept";
}

void after_target()
{
  const char *local = "after_target_kept";
}

void target()
{
  const char *local = "target_kept";

  before_target();
  assert(0);
  after_target();
}

void unreachable_calls_before_target()
{
  const char *local = "unreachable_calls_before_target_kept";
  before_target();
}

void unreachable_calls_after_target()
{
  const char *local = "unreachable_calls_after_target_kept";
  after_target();
}

void reachable_before_target_caller_1()
{
  const char *local = "reachable_before_target_caller_1_kept";
}

void reachable_after_target_caller_1()
{
  const char *local = "reachable_after_target_caller_1_kept";
}

void reachable_may_call_target_1()
{
  const char *local = "reachable_may_call_target_1_kept";
  reachable_before_target_caller_1();
  target();
  reachable_after_target_caller_1();
}

void reachable_before_target_caller_2()
{
  const char *local = "reachable_before_target_caller_2_kept";
}

void reachable_after_target_caller_2()
{
  const char *local = "reachable_after_target_caller_2_kept";
}

void reachable_may_call_target_2()
{
  const char *local = "reachable_may_call_target_2_kept";
  reachable_before_target_caller_2();
  target();
  reachable_after_target_caller_2();
}


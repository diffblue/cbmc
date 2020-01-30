/*******************************************************************\

Module: Scope Guard

Author: Diffblue Ltd.

\*******************************************************************/

#ifndef CPROVER_UTIL_SCOPE_GUARD_H
#define CPROVER_UTIL_SCOPE_GUARD_H

#include <stdexcept>
#include <utility>

/// Execute some code if a scope is exited with an exception
template <typename OnErrorHandler>
class on_exit_scope_with_exceptiont
{
  OnErrorHandler handler;
  std::exception_ptr uncaught_exception_at_scope_start;
  bool cancelled = false;

public:
  explicit on_exit_scope_with_exceptiont(OnErrorHandler handler)
    : handler(std::move(handler)),
      uncaught_exception_at_scope_start(std::current_exception())
  {
  }

  on_exit_scope_with_exceptiont(const on_exit_scope_with_exceptiont &) = delete;
  on_exit_scope_with_exceptiont(on_exit_scope_with_exceptiont &&other) noexcept
    : handler{std::move(other.handler)},
      uncaught_exception_at_scope_start{
        std::move(other.uncaught_exception_at_scope_start)},
      cancelled{other.cancelled}
  {
    other.cancelled = true;
  }

  on_exit_scope_with_exceptiont &
  operator=(const on_exit_scope_with_exceptiont &) = delete;
  on_exit_scope_with_exceptiont &
  operator=(on_exit_scope_with_exceptiont &&) = delete;

  ~on_exit_scope_with_exceptiont()
  {
    // there was an uncaught exception in the scope of this guard if
    // the current exception now is different than the current exception
    // at the time of creating this object.
    if(
      !cancelled &&
      std::current_exception() != uncaught_exception_at_scope_start)
    {
      handler();
    }
  }
};

/// This is needed for usability with lambdas, as their types can’t be spelled
/// in C++11
/// \see on_exit_scope_with_exceptiont
template <typename OnErrorHandler>
on_exit_scope_with_exceptiont<OnErrorHandler>
on_exit_scope_with_exception(OnErrorHandler onErrorHandler)
{
  return on_exit_scope_with_exceptiont<OnErrorHandler>{
    std::move(onErrorHandler)};
}

#endif // CPROVER_UTIL_SCOPE_GUARD_H

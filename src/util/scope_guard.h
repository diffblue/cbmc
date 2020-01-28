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
  int uncaught_exceptions_at_scope_start;
  bool cancelled = false;

public:
  explicit on_exit_scope_with_exceptiont(OnErrorHandler handler)
    : handler(std::move(handler)),
      uncaught_exceptions_at_scope_start(std::uncaught_exceptions())
  {
  }

  on_exit_scope_with_exceptiont(const on_exit_scope_with_exceptiont &) = delete;
  on_exit_scope_with_exceptiont(on_exit_scope_with_exceptiont &&other) noexcept
    : handler{std::move(other.handler)},
      uncaught_exceptions_at_scope_start{
        other.uncaught_exceptions_at_scope_start},
      cancelled{false}
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
    // the number of uncaught exceptions has increased since its creation.
    if(
      !cancelled &&
      std::uncaught_exceptions() > uncaught_exceptions_at_scope_start)
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

#endif //CPROVER_UTIL_SCOPE_GUARD_H

/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_UTIL_TYPECHECK_H
#define CPROVER_UTIL_TYPECHECK_H

#include "message.h"

class typecheckt:public messaget
{
public:
  explicit typecheckt(message_handlert &_message_handler):
    messaget(_message_handler)
  {
  }

  virtual ~typecheckt() { }

  class errort final
  {
  public:
    errort() = default;
    errort(errort &&) = default;
    errort(const errort &other)
    {
      // ostringstream does not have a copy constructor
      message << other.message.str();
      __location = other.__location;
    }

    std::string what() const
    {
      return message.str();
    }

    std::ostringstream &message_ostream()
    {
      return message;
    }

    errort with_location(source_locationt _location) &&
    {
      __location = std::move(_location);
      return std::move(*this);
    }

    const source_locationt &source_location() const
    {
      return __location;
    }

  protected:
    std::ostringstream message;
    source_locationt __location = source_locationt::nil();

    template <typename T>
    friend errort operator<<(errort &&e, const T &);
  };

protected:
  // main function -- overload this one
  virtual void typecheck()=0;

public:
  // call that one
  virtual bool typecheck_main();
};

/// add to the diagnostic information in the given typecheckt::errort exception
template <typename T>
typecheckt::errort operator<<(typecheckt::errort &&e, const T &message)
{
  e.message_ostream() << message;
  return std::move(e);
}

#endif // CPROVER_UTIL_TYPECHECK_H

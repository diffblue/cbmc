// Author: Fotis Koutoulakis for Diffblue Ltd, 2023.

#pragma once

#include <string>

// The following type is cloning two types from the `util/exception_utils.h` and
// `util/invariant.h` files.
//
// The reason we need to do this is as follows: We have a fundamental constraint
// in that we don't want to export internal headers to the clients, and our
// current build system architecture on the C++ end doesn't allow us to do so.
//
// At the same time, we want to allow the Rust API to be able to catch at the
// shimlevel the errors generated within CBMC, which are C++ types (and
// subtypes of those), and so because of the mechanism that cxx.rs uses, we
// need to have thetypes present at compilation time (an incomplete type won't
// do - I've tried).
//
// This is the best way that we have currently to be have the type definitions
// around so that the exception handling code knows what our exceptions look
// like (especially given that they don't inherit from `std::exception`), so
// that our system compiles and is functional, without needing include chains
// outside of the API implementation (which we can't expose as well).

// This should mirror the definition in `util/invariant.h`.
class invariant_failedt
{
private:
  const std::string file;
  const std::string function;
  const int line;
  const std::string backtrace;
  const std::string condition;
  const std::string reason;

public:
  virtual ~invariant_failedt() = default;

  virtual std::string what() const noexcept;

  invariant_failedt(
    const std::string &_file,
    const std::string &_function,
    int _line,
    const std::string &_backtrace,
    const std::string &_condition,
    const std::string &_reason)
    : file(_file),
      function(_function),
      line(_line),
      backtrace(_backtrace),
      condition(_condition),
      reason(_reason)
  {
  }
};

// This is needed here because the original definition is in the file
// <util/exception_utils.h> which is including <util/source_location.h>, which
// being an `irep` is a no-go for our needs as we will need to expose internal
// headers as well.
class cprover_exception_baset
{
public:
  /// A human readable description of what went wrong.
  /// For readability, implementors should not add a leading
  /// or trailing newline to this description.
  virtual std::string what() const;
  virtual ~cprover_exception_baset() = default;

protected:
  /// This constructor is marked protected to ensure this class isn't used
  /// directly. Deriving classes should be used to more precisely describe the
  /// problem that occurred.
  explicit cprover_exception_baset(std::string reason)
    : reason(std::move(reason))
  {
  }

  /// The reason this exception was generated. This is the string returned by
  /// `what()` unless that method is overridden
  std::string reason;
};

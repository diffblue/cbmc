/// \file timestamper.h
/// \brief Emit timestamps
/// \author Kareem Khazem <karkhaz@karkhaz.com>

#ifndef CPROVER_UTIL_TIMESTAMPER_H
#define CPROVER_UTIL_TIMESTAMPER_H

#ifdef _WIN32
#define OPT_TIMESTAMP ""
#define HELP_TIMESTAMP ""
#else
#define OPT_TIMESTAMP "(timestamp):"

#define HELP_TIMESTAMP                                                         \
  " --timestamp <monotonic|wall> print microsecond-precision timestamps.\n"    \
  "                              monotonic: stamps increase monotonically.\n"  \
  "                              wall: ISO-8601 wall clock timestamps.\n"
#endif

#include <memory>
#include <string>

/// \brief Timestamp class hierarchy
///
/// This class hierarchy supports generation of timestamps in various textual
/// formats. The timestamps returned by instances of this class are empty; more
/// meaningful timestamps are returned by derived classes.
///
/// Instances of this class can be instantiated to emit empty timestamps, in
/// case the user did not specify `--timestamp` on the command line. The
/// intended use of this class hierarchy is to create a pointer or
/// std::unique_ptr called `time` to a timestampert, and to initialize `time`
/// with either an actual \ref timestampert object or one of the derived
/// classes based on whether the user has asked for timestamps to be emitted.
/// Clients can thus unconditionally call `time->stamp()` and prepend that
/// string to any logging messages; if the user didn't ask for timestamps, then
/// the object pointed to by `time` will be a \ref timestampert and thus
/// timestampert::stamp() will return only an empty string. Derived classes
/// emit an actual timestamp followed by a space, so no conditional checking is
/// needed by the client.
class timestampert
{
public:
  /// \brief Derived types of \ref timestampert
  enum class clockt
  {
    /// \ref timestampert
    NONE,
    /// monotonic_timestampert
    MONOTONIC,
    /// wall_clock_timestampert
    WALL_CLOCK
  };
  virtual ~timestampert() = default;

  /// \brief Default timestamp: the empty string
  virtual std::string stamp() const
  {
    return "";
  }

  /// \brief Factory method to build timestampert subclasses
  static std::unique_ptr<const timestampert> make(clockt clock_type);
};

#ifndef _WIN32
class monotonic_timestampert : public timestampert
{
public:
  /// \brief See \ref HELP_TIMESTAMP in util/timestamper.h for time
  /// stamp format
  virtual std::string stamp() const override;
};

class wall_clock_timestampert : public timestampert
{
public:
  /// \brief See \ref HELP_TIMESTAMP in util/timestamper.h for time
  /// stamp format
  virtual std::string stamp() const override;
};
#endif

#endif /* CPROVER_UTIL_TIMESTAMPER_H */

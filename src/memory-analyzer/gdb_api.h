/*******************************************************************\

Module: GDB Machine Interface API

Author: Malte Mues <mail.mues@gmail.com>
        Daniel Poetzl

\*******************************************************************/

/// \file
/// Low-level interface to gdb
///
/// This provides an API to run a program under gdb up to some
/// breakpoint, and then query the values of expressions. It uses the
/// gdb machine interface (see section "The GDB/MI Interface" in the
/// gdb manual to communicate with gdb.

// clang-format off
#if defined(__linux__) || \
    defined(__FreeBSD_kernel__) || \
    defined(__GNU__) || \
    defined(__unix__) || \
    defined(__CYGWIN__) || \
    defined(__MACH__)
// clang-format on

#ifndef CPROVER_MEMORY_ANALYZER_GDB_API_H
#define CPROVER_MEMORY_ANALYZER_GDB_API_H
#include <unistd.h>

#include <exception>

#include <util/exception_utils.h>

class gdb_apit
{
public:
  explicit gdb_apit(const char *binary, const bool log = false);

  void create_gdb_process();
  void terminate_gdb_process();

  bool run_gdb_to_breakpoint(const std::string &breakpoint);
  void run_gdb_from_core(const std::string &corefile);

  std::string get_value(const std::string &expr);
  std::string get_memory(const std::string &expr);

  const std::vector<std::string> &get_command_log();

protected:
  const char *binary;

  FILE *input_stream;
  FILE *output_stream;

  const bool log;
  std::vector<std::string> command_log;

  enum class gdb_statet
  {
    NOT_CREATED,
    CREATED,
    STOPPED
  };

  gdb_statet gdb_state;

  typedef std::map<std::string, std::string> gdb_output_recordt;
  static gdb_output_recordt parse_gdb_output_record(const std::string &s);

  void write_to_gdb(const std::string &command);

  std::string read_next_line();
  std::string read_most_recent_line();

  std::string eval_expr(const std::string &expr);

  gdb_output_recordt
  get_most_recent_record(const std::string &tag, const bool must_exist = false);

  static bool has_tag(const std::string &tag, const std::string &line);

  bool most_recent_line_has_tag(const std::string &tag);
};

class gdb_interaction_exceptiont : public cprover_exception_baset
{
public:
  explicit gdb_interaction_exceptiont(std::string reason) : reason(reason)
  {
  }
  std::string what() const override
  {
    return reason;
  }

private:
  std::string reason;
};

#endif // CPROVER_MEMORY_ANALYZER_GDB_API_H
#endif

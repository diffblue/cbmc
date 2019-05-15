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

#ifndef CPROVER_MEMORY_ANALYZER_GDB_API_H
#define CPROVER_MEMORY_ANALYZER_GDB_API_H
#include <unistd.h>

#include <exception>
#include <forward_list>

#include <util/exception_utils.h>

class gdb_apit
{
public:
  using commandst = std::forward_list<std::string>;

  explicit gdb_apit(const char *binary, const bool log = false);
  ~gdb_apit();

  struct pointer_valuet
  {
    pointer_valuet(
      const std::string &address = "",
      const std::string &pointee = "",
      const std::string &character = "",
      const optionalt<std::string> &string = nullopt)
      : address(address), pointee(pointee), character(character), string(string)
    {
    }

    const std::string address;
    const std::string pointee;
    const std::string character;
    const optionalt<std::string> string;
  };

  void create_gdb_process();
  void terminate_gdb_process();

  bool run_gdb_to_breakpoint(const std::string &breakpoint);
  void run_gdb_from_core(const std::string &corefile);

  std::string get_value(const std::string &expr);
  pointer_valuet get_memory(const std::string &expr);

  const commandst &get_command_log();

protected:
  const char *binary;

  FILE *response_stream;
  FILE *command_stream;

  const bool log;
  commandst command_log;

  enum class gdb_statet
  {
    NOT_CREATED,
    CREATED,
    STOPPED // valid state, reached e.g. after breakpoint was hit
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

  bool most_recent_line_has_tag(const std::string &tag);
  bool was_command_accepted();
  void check_command_accepted();

  static std::string r_opt(const std::string &regex);

  static std::string
  r_or(const std::string &regex_left, const std::string &regex_right);

  // regex group for hex memory address (part of the output of gdb when printing
  // a pointer), matches e.g. 0x601040 and extracts 0x601040
  const std::string r_hex_addr = R"((0x(?:0|[1-9a-f][0-9a-f]*)))";

  // regex group for identifier (optional part of the output of gdb when
  // printing a pointer), matches e.g. <abc> and extracts abc
  const std::string r_id = R"(<([^<>]+)>)";

  // regex group for octal encoded char (optional part of the output of gdb when
  // printing a pointer), matches e.g. \"\\003\" and extracts \\003
  const std::string r_char = R"(\\"(\\\\[0-7]{3})\\")";

  // regex group for string (optional part of the output of gdb when printing a
  // pointer), matches e.g. \"abc\" and extracts \"abc\"
  const std::string r_string = R"((\\".*\\"))";
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

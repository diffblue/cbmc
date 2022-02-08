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

#include <algorithm>
#include <exception>
#include <forward_list>
#include <map>

#include <util/exception_utils.h>

/// Interface for running and querying GDB
class gdb_apit
{
public:
  using commandst = std::forward_list<std::string>;

  /// Memory address imbued with the explicit boolean data indicating if the
  /// address is null or not.
  struct memory_addresst
  {
    bool null_address;
    std::string address_string;
    memory_addresst() : null_address(true)
    {
    }
    explicit memory_addresst(const std::string &address_string)
      : null_address(address_string == "0x0"), address_string(address_string)
    {
    }

    bool is_null() const
    {
      return null_address;
    }
    bool operator<(const memory_addresst &other) const
    {
      return address_string < other.address_string;
    }
    std::string string() const
    {
      return address_string;
    }
  };

  /// Create a \ref gdb_apit object
  /// \param args: arguments to pass to gdb, the first argument is the command
  ///   to execute
  /// \param log: boolean indicating whether gdb input and output should be
  ///   logged
  explicit gdb_apit(
    const std::vector<std::string> &args, const bool log = false);

  /// Terminate the gdb process and close open streams (for reading from and
  /// writing to gdb)
  ~gdb_apit();

  /// Data associated with the value of a pointer, i.e. not only the address but
  /// also the pointee (if known), string (in the case of char*), etc.
  struct pointer_valuet
  {
    pointer_valuet(
      const std::string &address = "",
      const std::string &pointee = "",
      const std::string &character = "",
      const optionalt<std::string> &string = nullopt,
      const bool valid = false)
      : address(address),
        pointee(pointee),
        character(character),
        string(string),
        valid(valid)
    {
    }

    memory_addresst address;
    std::string pointee;
    std::string character;
    optionalt<std::string> string;

    bool has_known_offset() const
    {
      return std::any_of(
        pointee.begin(), pointee.end(), [](char c) { return c == '+'; });
    }

    bool valid;
  };

  /// Get the exact allocated size for a pointer \p pointer_expr.
  /// \param pointer_expr: expression with a pointer name
  /// \return 1 if the pointer was not allocated with malloc otherwise return
  ///   the number of allocated bytes
  size_t query_malloc_size(const std::string &pointer_expr);

  /// Create a new gdb process for analysing the binary indicated by the first
  /// element in `args`
  void create_gdb_process();

  /// Run gdb to the given breakpoint
  /// \param breakpoint the breakpoint to set (can be e.g. a line number or a
  ///   function name)
  /// \return true if something failed
  bool run_gdb_to_breakpoint(const std::string &breakpoint);

  /// Run gdb with the given core file
  /// \param corefile: core dump
  void run_gdb_from_core(const std::string &corefile);

  /// Get the memory address pointed to by the given pointer expression
  /// \param expr: an expression of pointer type (e.g., `&x` with `x` being of
  ///   type `int` or `p` with `p` being of type `int *`)
  /// \return memory address in hex format
  optionalt<std::string> get_value(const std::string &expr);

  /// Get the value of a pointer associated with \p expr
  /// \param expr: the expression to be analyzed
  /// \return the \p pointer_valuet filled with data gdb produced for \p expr
  pointer_valuet get_memory(const std::string &expr);

  /// Return the vector of commands that have been written to gdb so far
  /// \return the list of commands
  const commandst &get_command_log();

protected:
  // arguments passed to gdb, first argument is the command to execute
  std::vector<std::string> args;

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

  /// track the allocated size for each malloc call
  /// maps hexadecimal address to the number of bytes
  std::map<std::string, size_t> allocated_memory;

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

  /// Intercepts the gdb-analysis at the malloc call-site to add the
  /// corresponding information into \ref allocated_memory.
  void collect_malloc_calls();

  /// Locate and return the value for a given name
  /// \param record: gdb record to search
  /// \param value_name: name of the value to be extracted
  /// \return the value associated with \p value_name
  std::string get_value_from_record(
    const gdb_output_recordt &record,
    const std::string &value_name);

  /// Check if the breakpoint we hit is inside a malloc
  /// \param stopped_record: gdb record pertaining to a breakpoint being hit
  /// \return true if the breakpoint the gdb stopped at was malloc
  bool hit_malloc_breakpoint(const gdb_output_recordt &stopped_record);

  /// Parse the record produced by listing register value
  /// \param record: gdb record for one register value
  /// \return get the value associated with some register value
  std::string get_register_value(const gdb_output_recordt &record);

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

  // name of malloc function
  const std::string malloc_name = "malloc";
};

class gdb_interaction_exceptiont : public cprover_exception_baset
{
public:
  explicit gdb_interaction_exceptiont(std::string reason)
    : cprover_exception_baset(std::move(reason))
  {
  }
};

#endif // CPROVER_MEMORY_ANALYZER_GDB_API_H

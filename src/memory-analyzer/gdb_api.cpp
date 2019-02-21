/*******************************************************************\

Module: GDB Machine Interface API

Author: Malte Mues <mail.mues@gmail.com>
        Daniel Poetzl

\*******************************************************************/

/// \file
/// Low-level interface to gdb

// clang-format off
#if defined(__linux__) || \
    defined(__FreeBSD_kernel__) || \
    defined(__GNU__) || \
    defined(__unix__) || \
    defined(__CYGWIN__) || \
    defined(__MACH__)
// clang-format on

#include <cctype>
#include <cerrno>
#include <cstdio>
#include <cstring>
#include <regex>

#include <iostream>

#include "gdb_api.h"

#include <goto-programs/goto_model.h>

#include <util/prefix.h>
#include <util/string_utils.h>

#include <sys/wait.h>

/// Create a gdb_apit object
///
/// \param binary the binary to run with gdb
/// \param log boolean indicating whether gdb input and output should be logged
gdb_apit::gdb_apit(const char *binary, const bool log)
  : binary(binary), log(log), gdb_state(gdb_statet::NOT_CREATED)
{
}

/// Terminate the gdb process and close open streams (for reading from and
/// writing to gdb)
gdb_apit::~gdb_apit()
{
  PRECONDITION(
    gdb_state == gdb_statet::CREATED || gdb_state == gdb_statet::STOPPED ||
    gdb_state == gdb_statet::NOT_CREATED);

  if(gdb_state == gdb_statet::NOT_CREATED)
    return;

  write_to_gdb("-gdb-exit");
  // we cannot use most_recent_line_has_tag() here as it checks the last line
  // before the next `(gdb) \n` prompt in the output; however when gdb exits no
  // next prompt is printed
  CHECK_RETURN(has_prefix(read_next_line(), "^exit"));

  gdb_state = gdb_statet::NOT_CREATED;

  fclose(command_stream);
  fclose(response_stream);

  wait(NULL);
}

/// Create a new gdb process for analysing the binary indicated by the member
/// variable `binary`
void gdb_apit::create_gdb_process()
{
  PRECONDITION(gdb_state == gdb_statet::NOT_CREATED);

  command_log.clear();

  pid_t gdb_process;

  int pipe_input[2];
  int pipe_output[2];

  if(pipe(pipe_input) == -1)
  {
    throw gdb_interaction_exceptiont("could not create pipe for stdin");
  }

  if(pipe(pipe_output) == -1)
  {
    throw gdb_interaction_exceptiont("could not create pipe for stdout");
  }

  gdb_process = fork();

  if(gdb_process == -1)
  {
    throw gdb_interaction_exceptiont("could not create gdb process");
  }

  if(gdb_process == 0)
  {
    // child process
    close(pipe_input[1]);
    close(pipe_output[0]);

    dup2(pipe_input[0], STDIN_FILENO);
    dup2(pipe_output[1], STDOUT_FILENO);
    dup2(pipe_output[1], STDERR_FILENO);

    dprintf(pipe_output[1], "binary name: %s\n", binary);

    char *const arg[] = {const_cast<char *>("gdb"),
                         const_cast<char *>("--interpreter=mi"),
                         const_cast<char *>(binary),
                         NULL};

    dprintf(pipe_output[1], "Loading gdb...\n");
    execvp("gdb", arg);

    // Only reachable, if execvp failed
    int errno_value = errno;
    dprintf(pipe_output[1], "errno in child: %s\n", strerror(errno_value));
  }
  else
  {
    // parent process
    gdb_state = gdb_statet::CREATED;

    close(pipe_input[0]);
    close(pipe_output[1]);

    // get stream for reading the gdb output
    response_stream = fdopen(pipe_output[0], "r");

    // get stream for writing to gdb
    command_stream = fdopen(pipe_input[1], "w");

    bool has_done_tag = most_recent_line_has_tag(R"(~"done)");
    CHECK_RETURN(has_done_tag);

    if(log)
    {
      // logs output to `gdb.txt` in the current directory, input is not logged
      // hence we log it to `command_log`
      write_to_gdb("-gdb-set logging on");
      check_command_accepted();
    }

    write_to_gdb("-gdb-set max-value-size unlimited");
    check_command_accepted();
  }
}

void gdb_apit::write_to_gdb(const std::string &command)
{
  PRECONDITION(!command.empty());
  PRECONDITION(command.find('\n') == std::string::npos);

  std::string line(command);
  line += '\n';

  if(log)
  {
    command_log.push_front(command);
  }

  if(fputs(line.c_str(), command_stream) == EOF)
  {
    throw gdb_interaction_exceptiont("could not write a command to gdb");
  }

  fflush(command_stream);
}

/// Return the vector of commands that have been written to gdb so far
const gdb_apit::commandst &gdb_apit::get_command_log()
{
  PRECONDITION(log);
  return command_log;
}

std::string gdb_apit::read_next_line()
{
  std::string result;

  do
  {
    const size_t buf_size = 1024;
    char buf[buf_size]; // NOLINT(runtime/arrays)

    const char *c = fgets(buf, buf_size, response_stream);

    if(c == NULL)
    {
      if(ferror(response_stream))
      {
        throw gdb_interaction_exceptiont("error reading from gdb");
      }

      INVARIANT(
        feof(response_stream),
        "EOF must have been reached when the error indicator on the stream "
        "is not set and fgets returned NULL");
      INVARIANT(
        result.empty() || result.back() != '\n',
        "when EOF is reached then either no characters were read or the string"
        " read does not end in a newline");

      return result;
    }

    std::string chunk(buf);
    INVARIANT(!chunk.empty(), "chunk cannot be empty when EOF was not reached");

    result += chunk;
  } while(result.back() != '\n');

  return result;
}

std::string gdb_apit::read_most_recent_line()
{
  std::string line;
  std::string output;

  do
  {
    output = line;
    line = read_next_line();
  } while(line != "(gdb) \n");

  return output;
}

gdb_apit::gdb_output_recordt
gdb_apit::get_most_recent_record(const std::string &tag, const bool must_exist)
{
  std::string line = read_most_recent_line();
  const bool b = has_prefix(line, tag);

  if(must_exist)
  {
    CHECK_RETURN(b);
  }
  else if(!b)
  {
    throw gdb_interaction_exceptiont("record does not exist");
  }

  std::string record = strip_string(line.substr(line.find(',') + 1));

  return parse_gdb_output_record(record);
}

bool gdb_apit::most_recent_line_has_tag(const std::string &tag)
{
  const std::string line = read_most_recent_line();
  return has_prefix(line, tag);
}

/// Run gdb with the given core file
///
/// \param corefile core dump
void gdb_apit::run_gdb_from_core(const std::string &corefile)
{
  PRECONDITION(gdb_state == gdb_statet::CREATED);

  // there does not seem to be a gdb mi command to run from a core file
  const std::string command = "core " + corefile;

  write_to_gdb(command);
  check_command_accepted();

  gdb_state = gdb_statet::STOPPED;
}

/// Run gdb to the given breakpoint
///
/// \param breakpoint the breakpoint to set (can be e.g. a line number or a
///   function name)
bool gdb_apit::run_gdb_to_breakpoint(const std::string &breakpoint)
{
  PRECONDITION(gdb_state == gdb_statet::CREATED);

  std::string command("-break-insert");
  command += " " + breakpoint;

  write_to_gdb(command);
  if(!was_command_accepted())
  {
    throw gdb_interaction_exceptiont("could not set breakpoint");
  }

  write_to_gdb("-exec-run");

  if(!most_recent_line_has_tag("*running"))
  {
    throw gdb_interaction_exceptiont("could not run program");
  }

  gdb_output_recordt record = get_most_recent_record("*stopped");
  const auto it = record.find("reason");
  CHECK_RETURN(it != record.end());

  const std::string &reason = it->second;

  if(reason == "breakpoint-hit")
  {
    gdb_state = gdb_statet::STOPPED;
    return true;
  }
  else if(reason == "exited-normally")
  {
    return false;
  }
  else
  {
    throw gdb_interaction_exceptiont(
      "gdb stopped for unhandled reason `" + reason + "`");
  }

  UNREACHABLE;
}

std::string gdb_apit::eval_expr(const std::string &expr)
{
  write_to_gdb("-var-create tmp * " + expr);

  if(!was_command_accepted())
  {
    throw gdb_interaction_exceptiont(
      "could not create variable for expression `" + expr + "`");
  }

  write_to_gdb("-var-evaluate-expression tmp");
  gdb_output_recordt record = get_most_recent_record("^done", true);

  write_to_gdb("-var-delete tmp");
  check_command_accepted();

  const auto it = record.find("value");
  CHECK_RETURN(it != record.end());

  const std::string value = it->second;

  INVARIANT(
    value.back() != '"' ||
      (value.length() >= 2 && value[value.length() - 2] == '\\'),
    "quotes should have been stripped off from value");
  INVARIANT(value.back() != '\n', "value should not end in a newline");

  return value;
}

/// Get the memory address pointed to by the given pointer expression
///
/// \param expr an expression of pointer type (e.g., `&x` with `x` being of type
///   `int` or `p` with `p` being of type `int *`)
/// \return memory address in hex format
gdb_apit::pointer_valuet gdb_apit::get_memory(const std::string &expr)
{
  PRECONDITION(gdb_state == gdb_statet::STOPPED);

  std::string value = eval_expr(expr);

  std::regex regex(
    r_hex_addr + r_opt(' ' + r_id) + r_opt(' ' + r_or(r_char, r_string)));

  std::smatch result;
  const bool b = regex_match(value, result, regex);
  CHECK_RETURN(b);

  optionalt<std::string> opt_string;
  const std::string string = result[4];

  if(!string.empty())
  {
    const std::size_t len = string.length();

    INVARIANT(len >= 4, "");
    INVARIANT(string[0] == '\\', "");
    INVARIANT(string[1] == '"', "");
    INVARIANT(string[len - 2] == '\\', "");
    INVARIANT(string[len - 1] == '"', "");

    opt_string = string.substr(2, len - 4);
  }

  return pointer_valuet(result[1], result[2], result[3], opt_string);
}

/// Get value of the given value expression
///
/// \param expr an expression of non-pointer type or pointer to char
/// \return value of the expression; if the expression is of type pointer to
///   char and represents a string, the string value is returned; otherwise the
///   value is returned just as it is printed by gdb
std::string gdb_apit::get_value(const std::string &expr)
{
  PRECONDITION(gdb_state == gdb_statet::STOPPED);

  const std::string value = eval_expr(expr);

  // Get char value
  {
    // matches e.g. 99 'c' and extracts c
    std::regex regex(R"([^ ]+ '([^']+)')");

    std::smatch result;
    const bool b = regex_match(value, result, regex);

    if(b)
    {
      return result[1];
    }
  }

  // return raw value
  return value;
}

gdb_apit::gdb_output_recordt
gdb_apit::parse_gdb_output_record(const std::string &s)
{
  PRECONDITION(s.back() != '\n');

  gdb_output_recordt result;

  std::size_t depth = 0;
  std::string::size_type start = 0;

  const std::string::size_type n = s.length();

  for(std::string::size_type i = 0; i < n; i++)
  {
    const char c = s[i];

    if(c == '{' || c == '[')
    {
      depth++;
    }
    else if(c == '}' || c == ']')
    {
      depth--;
    }

    if(depth == 0 && (c == ',' || i == n - 1))
    {
      const std::string item =
        i == n - 1 ? s.substr(start) : s.substr(start, i - start);

      // Split on first `=`
      std::string::size_type j = item.find('=');
      CHECK_RETURN(j != std::string::npos);
      CHECK_RETURN(j > 0);
      CHECK_RETURN(j < s.length());

      const std::string key = strip_string(item.substr(0, j));
      std::string value = strip_string(item.substr(j + 1));

      const char first = value.front();
      const char last = value.back();

      INVARIANT(first == '"' || first == '{' || first == '[', "");
      INVARIANT(first != '"' || last == '"', "");
      INVARIANT(first != '{' || last == '}', "");
      INVARIANT(first != '[' || last == ']', "");

      // Remove enclosing `"` for primitive values
      if(first == '"')
      {
        value = value.substr(1, value.length() - 2);
      }

      auto r = result.insert(std::make_pair(key, value));
      CHECK_RETURN(r.second);

      start = i + 1;
    }
  }

  return result;
}

bool gdb_apit::was_command_accepted()
{
  return most_recent_line_has_tag("^done");
}

void gdb_apit::check_command_accepted()
{
  bool was_accepted = was_command_accepted();
  CHECK_RETURN(was_accepted);
}

std::string gdb_apit::r_opt(const std::string &regex)
{
  return R"((?:)" + regex + R"()?)";
}

std::string
gdb_apit::r_or(const std::string &regex_left, const std::string &regex_right)
{
  return R"((?:)" + regex_left + '|' + regex_right + R"())";
}

#endif

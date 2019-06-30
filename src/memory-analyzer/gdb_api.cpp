/*******************************************************************\

Module: GDB Machine Interface API

Author: Malte Mues <mail.mues@gmail.com>
        Daniel Poetzl

\*******************************************************************/

/// \file
/// Low-level interface to gdb
///
/// Implementation of the GDB/MI API for extracting values of expressions.

#include <cctype>
#include <cerrno>
#include <cstdio>
#include <cstring>
#include <regex>

#include <iostream>

#include "gdb_api.h"

#include <goto-programs/goto_model.h>

#include <util/prefix.h>
#include <util/string2int.h>
#include <util/string_utils.h>

#include <sys/wait.h>

gdb_apit::gdb_apit(const std::vector<std::string> &args, const bool log)
  : args(args), log(log), gdb_state(gdb_statet::NOT_CREATED)
{
}

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

size_t gdb_apit::query_malloc_size(const std::string &pointer_expr)
{
  const auto maybe_address_string = get_value(pointer_expr);
  CHECK_RETURN(maybe_address_string.has_value());

  if(allocated_memory.count(*maybe_address_string) == 0)
    return 1;
  else
    return allocated_memory[*maybe_address_string];
}

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

    dprintf(pipe_output[1], "binary name: %s\n", args.front().c_str());

    std::vector<std::string> exec_cmd;
    exec_cmd.reserve(args.size() + 3);
    exec_cmd.push_back("gdb");
    exec_cmd.push_back("--interpreter=mi");
    exec_cmd.push_back("--args");
    exec_cmd.insert(exec_cmd.end(), args.begin(), args.end());

    char **exec_cmd_ptr = static_cast<char **>(malloc(
      sizeof(char *) * (exec_cmd.size() + 1)));
    exec_cmd_ptr[exec_cmd.size()] = NULL;

    for(std::size_t i = 0; i < exec_cmd.size(); i++)
    {
      exec_cmd_ptr[i] = static_cast<char *>(malloc(
        sizeof(char) * (exec_cmd[i].length() + 1)));
      strcpy(exec_cmd_ptr[i], exec_cmd[i].c_str()); // NOLINT(runtime/printf)
    }

    dprintf(pipe_output[1], "Loading gdb...\n");
    execvp("gdb", exec_cmd_ptr);

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

    std::string line = read_most_recent_line();
    CHECK_RETURN(
      has_prefix(line, R"(~"done)") ||
      has_prefix(line, R"(~"Reading)"));

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

void gdb_apit::run_gdb_from_core(const std::string &corefile)
{
  PRECONDITION(gdb_state == gdb_statet::CREATED);

  // there does not seem to be a gdb mi command to run from a core file
  const std::string command = "core " + corefile;

  write_to_gdb(command);
  check_command_accepted();

  gdb_state = gdb_statet::STOPPED;
}

void gdb_apit::collect_malloc_calls()
{
  // this is what the registers look like at the function call entry:
  //
  // reg. name         hex. value   dec. value
  // 0: rax            0xffffffff   4294967295
  // 1: rbx            0x20000000   536870912
  // 2: rcx            0x591        1425
  // 3: rdx            0x591        1425
  // 4: rsi            0x1          1
  // 5: rdi            0x591        1425
  // ...
  // rax will eventually contain the return value and
  // rdi now stores the first (integer) argument
  // in the machine interface they are referred to by numbers, hence:
  write_to_gdb("-data-list-register-values d 5");
  auto record = get_most_recent_record("^done", true);
  auto allocated_size = safe_string2size_t(get_register_value(record));

  write_to_gdb("-exec-finish");
  if(!most_recent_line_has_tag("*running"))
  {
    throw gdb_interaction_exceptiont("could not run program");
  }
  record = get_most_recent_record("*stopped");
  auto frame_content = get_value_from_record(record, "frame");

  // the malloc breakpoint may be inside another malloc function
  if(frame_content.find("func=\"malloc\"") != std::string::npos)
  {
    // so we need to finish the outer malloc as well
    write_to_gdb("-exec-finish");
    if(!most_recent_line_has_tag("*running"))
    {
      throw gdb_interaction_exceptiont("could not run program");
    }
    record = get_most_recent_record("*stopped");
  }

  // now we can read the rax register to the the allocated memory address
  write_to_gdb("-data-list-register-values x 0");
  record = get_most_recent_record("^done", true);
  allocated_memory[get_register_value(record)] = allocated_size;
}

bool gdb_apit::run_gdb_to_breakpoint(const std::string &breakpoint)
{
  PRECONDITION(gdb_state == gdb_statet::CREATED);

  write_to_gdb("-break-insert " + malloc_name);
  bool malloc_is_known = was_command_accepted();

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

  // malloc function is known, i.e. present among the symbols
  if(malloc_is_known)
  {
    // stop at every entry into malloc call
    while(hit_malloc_breakpoint(record))
    {
      // and store the information about the allocated memory
      collect_malloc_calls();
      write_to_gdb("-exec-continue");
      if(!most_recent_line_has_tag("*running"))
      {
        throw gdb_interaction_exceptiont("could not run program");
      }
      record = get_most_recent_record("*stopped");
    }

    write_to_gdb("-break-delete 1");
    if(!was_command_accepted())
    {
      throw gdb_interaction_exceptiont("could not delete breakpoint at malloc");
    }
  }

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

gdb_apit::pointer_valuet gdb_apit::get_memory(const std::string &expr)
{
  PRECONDITION(gdb_state == gdb_statet::STOPPED);

  std::string value;
  try
  {
    value = eval_expr(expr);
  }
  catch(gdb_interaction_exceptiont &e)
  {
    return pointer_valuet{};
  }

  std::regex regex(
    r_hex_addr + r_opt(' ' + r_id) + r_opt(' ' + r_or(r_char, r_string)));

  std::smatch result;
  const bool b = regex_match(value, result, regex);
  if(!b)
    return pointer_valuet{};

  optionalt<std::string> opt_string;
  const std::string string = result[4];

  if(!string.empty())
  {
    const std::size_t len = string.length();

    INVARIANT(
      len >= 4,
      "pointer-string should be: backslash, quotes, .., backslash, quotes");
    INVARIANT(
      string[0] == '\\',
      "pointer-string should be: backslash, quotes, .., backslash, quotes");
    INVARIANT(
      string[1] == '"',
      "pointer-string should be: backslash, quotes, .., backslash, quotes");
    INVARIANT(
      string[len - 2] == '\\',
      "pointer-string should be: backslash, quotes, .., backslash, quotes");
    INVARIANT(
      string[len - 1] == '"',
      "pointer-string should be: backslash, quotes, .., backslash, quotes");

    opt_string = string.substr(2, len - 4);
  }

  return pointer_valuet(result[1], result[2], result[3], opt_string, true);
}

optionalt<std::string> gdb_apit::get_value(const std::string &expr)
{
  PRECONDITION(gdb_state == gdb_statet::STOPPED);

  std::string value;
  try
  {
    value = eval_expr(expr);
  }
  catch(gdb_interaction_exceptiont &e)
  {
    return {};
  }

  // Get char value
  {
    // matches e.g. 99 'c' and extracts c
    std::regex regex(R"([^ ]+ '([^']+)')");

    std::smatch result;
    const bool b = regex_match(value, result, regex);

    if(b)
    {
      return std::string{result[1]};
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

std::string gdb_apit::get_value_from_record(
  const gdb_output_recordt &record,
  const std::string &value_name)
{
  const auto it = record.find(value_name);
  CHECK_RETURN(it != record.end());
  const auto value = it->second;

  INVARIANT(
    value.back() != '"' ||
      (value.length() >= 2 && value[value.length() - 2] == '\\'),
    "quotes should have been stripped off from value");
  INVARIANT(value.back() != '\n', "value should not end in a newline");

  return value;
}

bool gdb_apit::hit_malloc_breakpoint(const gdb_output_recordt &stopped_record)
{
  const auto it = stopped_record.find("reason");
  CHECK_RETURN(it != stopped_record.end());

  if(it->second != "breakpoint-hit")
    return false;

  return safe_string2size_t(get_value_from_record(stopped_record, "bkptno")) ==
         1;
}

std::string gdb_apit::get_register_value(const gdb_output_recordt &record)
{
  // we expect the record of form:
  // {[register-values]->[name=name_string, value=\"value_string\"],..}
  auto record_value = get_value_from_record(record, "register-values");
  std::string value_eq_quotes = "value=\"";
  auto value_eq_quotes_size = value_eq_quotes.size();

  auto starting_pos = record_value.find(value_eq_quotes) + value_eq_quotes_size;
  auto ending_pos = record_value.find('\"', starting_pos);
  auto value_length = ending_pos - starting_pos;
  return std::string{record_value, starting_pos, value_length};
}

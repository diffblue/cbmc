// Copyright 2018 Author: Malte Mues <mail.mues@gmail.com>
#ifdef __linux__
#include <cctype>
#include <cerrno>
#include <cstdio>
#include <cstring>
#include <regex>

#include "gdb_api.h"
#include <goto-programs/goto_model.h>

#include <util/string_utils.h>

gdb_apit::gdb_apit(const char *arg) : binary_name(arg)
{
  memset(buffer, 0, MAX_READ_SIZE_GDB_BUFFER);
}

int gdb_apit::create_gdb_process()
{
  if(pipe(pipe_input) == -1)
  {
    throw gdb_interaction_exceptiont("could not create pipe for stdin!");
  }
  if(pipe(pipe_output) == -1)
  {
    throw gdb_interaction_exceptiont("could not create pipe for stdout!");
  }

  gdb_process = fork();
  if(gdb_process == -1)
  {
    throw gdb_interaction_exceptiont("could not create gdb process.");
  }
  if(gdb_process == 0)
  {
    // child process
    close(pipe_input[1]);
    close(pipe_output[0]);
    dup2(pipe_input[0], STDIN_FILENO);
    dup2(pipe_output[1], STDOUT_FILENO);
    dup2(pipe_output[1], STDERR_FILENO);
    dprintf(pipe_output[1], "binary name: %s\n", binary_name);
    char *arg[] = {
      const_cast<char *>("gdb"), const_cast<char *>(binary_name), NULL};

    dprintf(pipe_output[1], "Loading gdb...\n");
    execvp("gdb", arg);

    // Only reachable, if execvp failed
    int errno_value = errno;
    dprintf(pipe_output[1], "errno in child: %s\n", strerror(errno_value));
  }
  else
  {
    // parent process
    close(pipe_input[0]);
    close(pipe_output[1]);
    write_to_gdb("set max-value-size unlimited\n");
  }
  return 0;
}

void gdb_apit::terminate_gdb_process()
{
  close(pipe_input[0]);
  close(pipe_input[1]);
}

void gdb_apit::write_to_gdb(const std::string &command)
{
  if(
    write(pipe_input[1], command.c_str(), command.length()) !=
    (ssize_t)command.length())
  {
    throw gdb_interaction_exceptiont("Could not write a command to gdb");
  }
}

std::string gdb_apit::read_next_line()
{
  char token;
  std::string line;
  do
  {
    while(buffer_position >= last_read_size)
    {
      read_next_buffer_chunc();
    }
    token = buffer[buffer_position];
    line += token;
    ++buffer_position;
  } while(token != '\n');
  return line;
}

void gdb_apit::read_next_buffer_chunc()
{
  memset(buffer, 0, last_read_size);
  const auto read_size =
    read(pipe_output[0], &buffer, MAX_READ_SIZE_GDB_BUFFER);
  if(read_size < 0)
  {
    throw gdb_interaction_exceptiont("Error reading from gdb_process");
  }
  last_read_size = read_size;
  buffer_position = 0;
}

void gdb_apit::run_gdb_from_core(const std::string &corefile)
{
  const std::string command = "core " + corefile + "\n";
  write_to_gdb(command);
  std::string line;
  while(!isdigit(line[0]))
  {
    line = read_next_line();
    if(check_for_gdb_core_error(line))
    {
      terminate_gdb_process();
      throw gdb_interaction_exceptiont(
        "This core file doesn't work with the binary.");
    }
  }
}

bool gdb_apit::check_for_gdb_core_error(const std::string &line)
{
  const std::regex core_init_error_r("exec file is newer than core");
  return regex_search(line, core_init_error_r);
}

void gdb_apit::run_gdb_to_breakpoint(const std::string &breakpoint)
{
  std::string command = "break " + breakpoint + "\n";
  write_to_gdb(command);
  command = "run\n";
  write_to_gdb(command);
  std::string line;
  while(!isdigit(line[0]))
  {
    line = read_next_line();
    if(check_for_gdb_breakpoint_error(line))
    {
      terminate_gdb_process();
      throw gdb_interaction_exceptiont("This is not a valid breakpoint\n");
    }
  }
}

bool gdb_apit::check_for_gdb_breakpoint_error(const std::string &line)
{
  const std::regex breakpoint_init_error_r("Make breakpoint pending on future");
  return regex_search(line, breakpoint_init_error_r);
}

std::string gdb_apit::create_command(const std::string &variable)
{
  return "p " + variable + "\n";
}

std::string gdb_apit::get_memory(const std::string &variable)
{
  write_to_gdb(create_command(variable));
  const std::string &response = read_next_line();
  return extract_memory(response);
}

// All lines in the output start with something like
// '$XX = ' where XX is a digit. => shared_prefix.
const char shared_prefix[] = R"(\$[0-9]+\s=\s)";

// Matching a hex encoded address.
const char memory_address[] = R"(0x[[:xdigit:]]+)";

std::string gdb_apit::extract_memory(const std::string &line)
{
  // The next patterns matches the type information,
  // which be "(classifier struct name (*)[XX])"
  // for pointer to struct arrayes. classsifier and struct is optional => {1,3}
  // If it isn't an array, than the ending is " *)"
  // => or expression in pointer_star_or_array_suffix.
  const std::string struct_name = R"((?:\S+\s){1,3})";
  const std::string pointer_star_or_arary_suffix =
    R"((?:\*|(?:\*)?\(\*\)\[[0-9]+\])?)";
  const std::string pointer_type_info =
    R"(\()" + struct_name + pointer_star_or_arary_suffix + R"(\))";

  // The pointer type info is followed by the memory value and eventually
  // extended by the name of the pointer content, if gdb has an explicit symbol.
  // See unit test cases for more examples of expected input.
  const std::regex pointer_pattern(
    std::string(shared_prefix) + pointer_type_info + R"(\s()" + memory_address +
    R"()(\s\S+)?)");
  const std::regex null_pointer_pattern(
    std::string(shared_prefix) + R"((0x0))");
  // Char pointer output the memory adress followed by the string in there.
  const std::regex char_pointer_pattern(
    std::string(shared_prefix) + R"(()" + memory_address +
    R"()\s"[\S[:s:]]*")");

  std::smatch result;
  if(regex_search(line, result, char_pointer_pattern))
  {
    return result[1];
  }
  if(regex_search(line, result, pointer_pattern))
  {
    return result[1];
  }
  if(regex_search(line, result, null_pointer_pattern))
  {
    return result[1];
  }
  throw gdb_interaction_exceptiont("Cannot resolve memory_address: " + line);
}

std::string gdb_apit::get_value(const std::string &variable)
{
  write_to_gdb(create_command(variable));
  const std::string &response = read_next_line();
  return extract_value(response);
}

std::string gdb_apit::extract_value(const std::string &line)
{
  // This pattern matches primitive int values and bools.
  const std::regex value_pattern(
    std::string(shared_prefix) + R"(((?:-)?\d+|true|false))");
  // This pattern matches the char pointer content.
  // It is printed behind the address.
  const std::regex char_value_pattern(
    std::string(shared_prefix) + memory_address + "\\s\"([\\S ]*)\"");
  // An enum entry just prints the name of the value on the commandline.
  const std::regex enum_value_pattern(
    std::string(shared_prefix) + R"(([\S]+)(?:\n|$))");
  // A void pointer outputs it type first, followed by the memory address it
  // is pointing to. This pattern should extract the address.
  const std::regex void_pointer_pattern(
    std::string(shared_prefix) + R"((?:[\S\s]+)\s()" + memory_address + ")");

  std::smatch result;
  if(regex_search(line, result, char_value_pattern))
  {
    return result[1];
  }
  if(regex_search(line, result, value_pattern))
  {
    return result[1];
  }
  if(regex_search(line, result, enum_value_pattern))
  {
    return result[1];
  }
  if(regex_search(line, result, void_pointer_pattern))
  {
    return result[1];
  }
  std::regex memmory_access_error("Cannot access memory");
  if(regex_search(line, memmory_access_error))
  {
    throw gdb_inaccessible_memoryt("ERROR: " + line);
  }
  throw gdb_interaction_exceptiont("Cannot extract value from this: " + line);
}

gdb_apit::gdb_output_recordt
gdb_apit::parse_gdb_output_record(const std::string &s)
{
  PRECONDITION(s.back() != '\n');

  gdb_output_recordt result;

  unsigned depth = 0;
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

#endif

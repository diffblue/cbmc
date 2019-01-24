// Copyright 2018 Author: Malte Mues
#ifdef __linux__
#ifndef CPROVER_MEMORY_ANALYZER_GDB_API_H
#define CPROVER_MEMORY_ANALYZER_GDB_API_H
#include <unistd.h>

#include <exception>

#include <util/exception_utils.h>

class gdb_apit
{
public:
  explicit gdb_apit(const char *binary);

  int create_gdb_process();
  void terminate_gdb_process();

  void run_gdb_to_breakpoint(const std::string &breakpoint);
  void run_gdb_from_core(const std::string &corefile);

  std::string get_value(const std::string &variable);
  std::string get_memory(const std::string &variable);

private:
  const char *binary_name;
  FILE *input_stream;
  FILE *output_stream;

  static std::string create_command(const std::string &variable);
  void write_to_gdb(const std::string &command);

  std::string read_next_line();

  static bool check_for_gdb_breakpoint_error(const std::string &line);
  static bool check_for_gdb_core_error(const std::string &line);

  static std::string extract_value(const std::string &line);
  static std::string extract_memory(const std::string &line);

  typedef std::map<std::string, std::string> gdb_output_recordt;
  static gdb_output_recordt parse_gdb_output_record(const std::string &s);
};

class gdb_interaction_exceptiont : public std::exception
{
public:
  explicit gdb_interaction_exceptiont(std::string reason) : std::exception()
  {
    error = reason;
  }
  const char *what() const throw()
  {
    return error.c_str();
  }

private:
  std::string error;
};

class gdb_inaccessible_memoryt : public gdb_interaction_exceptiont
{
public:
  explicit gdb_inaccessible_memoryt(std::string reason)
    : gdb_interaction_exceptiont(reason)
  {
  }
};
#endif
#endif

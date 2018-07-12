// Copyright 2018 Author: Malte Mues
#ifdef __linux__
#ifndef CPROVER_MEMORY_ANALYZER_ANALYZE_SYMBOL_H
#define CPROVER_MEMORY_ANALYZER_ANALYZE_SYMBOL_H
#include <map>
#include <string>

#include <ansi-c/expr2c_class.h>
#include <util/message.h>
#include <util/namespace.h>
#include <util/std_code.h>

class symbol_tablet;
class gdb_apit;
class exprt;
class source_locationt;

class symbol_analyzert : public messaget
{
public:
  symbol_analyzert(
    const symbol_tablet &st,
    gdb_apit &gdb,
    message_handlert &handler);
  void analyse_symbol(const std::string &symbol);
  std::string get_code();

private:
  gdb_apit &gdb_api;
  const namespacet ns;
  expr2ct c_converter;

  code_blockt generated_code;
  size_t id_counter;
  std::map<symbol_exprt, std::string> outstanding_assigns;
  std::map<std::string, exprt> values;

  void add_assignment(const symbol_exprt &symbol, const exprt &value);
  std::map<std::string, std::string>
  get_value_for_struct(std::string variable, struct_typet structure);
  exprt fill_array_with_values(
    const std::string &symbol_id,
    exprt &array,
    const typet &type,
    const source_locationt &location);
  exprt fill_expr_with_values(
    const std::string &symbol_id,
    exprt expr,
    const typet &type,
    const source_locationt &location);
  exprt fill_char_struct_member_with_values(
    const symbol_exprt &field_acces,
    const exprt &default_expr,
    const source_locationt &location);
  exprt fill_struct_with_values(
    const std::string &symbol_id,
    exprt &expr,
    const typet &type,
    const source_locationt &location);
  exprt fill_void_pointer_with_values(
    const symbol_exprt &symbol,
    const source_locationt &location);

  exprt process_any_pointer_target(
    const symbol_exprt &symbol,
    const std::string memory_location,
    const source_locationt &location);
  code_declt get_pointer_target(
    const std::string deref_pointer,
    const typet &type,
    const source_locationt &location);

  code_declt declare_instance(const std::string &prefix, const typet &type);
  exprt declare_and_initalize_char_ptr(
    const symbol_exprt &symbol,
    const std::string &memory_location,
    const source_locationt &location);
  void process_char_pointer(
    const symbol_exprt &symbol,
    const source_locationt &location);

  void process_outstanding_assignments();
};

class symbol_analysis_exceptiont : public std::exception
{
public:
  explicit symbol_analysis_exceptiont(std::string reason) : std::exception()
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

class place_holder_exprt : public exprt
{
public:
  place_holder_exprt() : exprt(ID_skip_initialize)
  {
  }
  explicit place_holder_exprt(const irep_idt &identifier)
    : exprt(ID_skip_initialize)
  {
    set(ID_identifier, identifier);
  }
};
#endif // CPROVER_MEMORY_ANALYZER_ANALYZE_SYMBOL_H
#endif

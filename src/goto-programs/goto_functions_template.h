/*******************************************************************\

Module: Goto Programs with Functions

Author: Daniel Kroening

Date: June 2003

\*******************************************************************/

/// \file
/// Goto Programs with Functions

#ifndef CPROVER_GOTO_PROGRAMS_GOTO_FUNCTIONS_TEMPLATE_H
#define CPROVER_GOTO_PROGRAMS_GOTO_FUNCTIONS_TEMPLATE_H

#include <ostream>
#include <cassert>

#include <util/std_types.h>
#include <util/symbol.h>
#include <util/cprover_prefix.h>

template <class bodyT>
class goto_function_templatet
{
public:
  bodyT body;
  code_typet type;

  typedef std::vector<irep_idt> parameter_identifierst;
  parameter_identifierst parameter_identifiers;

  bool body_available() const
  {
    return !body.instructions.empty();
  }

  bool is_inlined() const
  {
    return type.get_bool(ID_C_inlined);
  }

  bool is_hidden() const
  {
    return type.get_bool(ID_C_hide);
  }

  void make_hidden()
  {
    type.set(ID_C_hide, true);
  }

  goto_function_templatet()
  {
  }

  void clear()
  {
    body.clear();
    type.clear();
    parameter_identifiers.clear();
  }

  void swap(goto_function_templatet &other)
  {
    body.swap(other.body);
    type.swap(other.type);
    parameter_identifiers.swap(other.parameter_identifiers);
  }

  void copy_from(const goto_function_templatet &other)
  {
    body.copy_from(other.body);
    type=other.type;
    parameter_identifiers=other.parameter_identifiers;
  }

  goto_function_templatet(const goto_function_templatet &)=delete;
  goto_function_templatet &operator=(const goto_function_templatet &)=delete;

  goto_function_templatet(goto_function_templatet &&other):
    body(std::move(other.body)),
    type(std::move(other.type)),
    parameter_identifiers(std::move(other.parameter_identifiers))
  {
  }

  goto_function_templatet &operator=(goto_function_templatet &&other)
  {
    body=std::move(other.body);
    type=std::move(other.type);
    parameter_identifiers=std::move(other.parameter_identifiers);
    return *this;
  }
};

template <class bodyT>
class goto_functions_templatet
{
public:
  typedef goto_function_templatet<bodyT> goto_functiont;
  typedef std::map<irep_idt, goto_functiont> function_mapt;
  function_mapt function_map;

  goto_functions_templatet()
  {
  }

  goto_functions_templatet(const goto_functions_templatet &)=delete;
  goto_functions_templatet &operator=(const goto_functions_templatet &)=delete;

  goto_functions_templatet(goto_functions_templatet &&other):
    function_map(std::move(other.function_map))
  {
  }

  goto_functions_templatet &operator=(goto_functions_templatet &&other)
  {
    function_map=std::move(other.function_map);
    return *this;
  }

  void clear()
  {
    function_map.clear();
  }

  void output(
    const namespacet &ns,
    std::ostream &out) const;

  void compute_location_numbers();
  void compute_loop_numbers();
  void compute_target_numbers();
  void compute_incoming_edges();

  void update()
  {
    compute_incoming_edges();
    compute_target_numbers();
    compute_location_numbers();
    compute_loop_numbers();
  }

  static inline irep_idt entry_point()
  {
    // do not confuse with C's "int main()"
    return CPROVER_PREFIX "_start";
  }

  void swap(goto_functions_templatet &other)
  {
    function_map.swap(other.function_map);
  }

  void copy_from(const goto_functions_templatet &other)
  {
    for(const auto &fun : other.function_map)
      function_map[fun.first].copy_from(fun.second);
  }
};

template <class bodyT>
void goto_functions_templatet<bodyT>::output(
  const namespacet &ns,
  std::ostream &out) const
{
  for(const auto &fun : function_map)
  {
    if(fun.second.body_available())
    {
      out << "^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^\n\n";

      const symbolt &symbol=ns.lookup(fun.first);
      out << symbol.display_name() << " /* " << symbol.name << " */\n";
      fun.second.body.output(ns, symbol.name, out);

      out << std::flush;
    }
  }
}

template <class bodyT>
void goto_functions_templatet<bodyT>::compute_location_numbers()
{
  unsigned nr=0;
  for(auto &named_function : function_map)
    named_function.second.body.compute_location_numbers(nr);
}

template <class bodyT>
void goto_functions_templatet<bodyT>::compute_incoming_edges()
{
  for(auto &named_function : function_map)
    named_function.second.body.compute_incoming_edges();
}

template <class bodyT>
void goto_functions_templatet<bodyT>::compute_target_numbers()
{
  for(auto &named_function : function_map)
    named_function.second.body.compute_target_numbers();
}

template <class bodyT>
void goto_functions_templatet<bodyT>::compute_loop_numbers()
{
  for(auto &named_function : function_map)
    named_function.second.body.compute_loop_numbers();
}

#endif // CPROVER_GOTO_PROGRAMS_GOTO_FUNCTIONS_TEMPLATE_H

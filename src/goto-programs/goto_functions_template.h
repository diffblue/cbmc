/*******************************************************************\

Module: Goto Programs with Functions

Author: Daniel Kroening

Date: June 2003

\*******************************************************************/

/// \file
/// Goto Programs with Functions

#ifndef CPROVER_GOTO_PROGRAMS_GOTO_FUNCTIONS_TEMPLATE_H
#define CPROVER_GOTO_PROGRAMS_GOTO_FUNCTIONS_TEMPLATE_H

#include "goto_function_template.h"
#include <ostream>
#include <cassert>

#include <util/std_types.h>
#include <util/symbol.h>
#include <util/cprover_prefix.h>


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
  for(auto &func : function_map)
  {
    func.second.body.compute_location_numbers(nr);
  }
}

template <class bodyT>
void goto_functions_templatet<bodyT>::compute_incoming_edges()
{
  for(auto &func : function_map)
  {
    func.second.body.compute_incoming_edges();
  }
}

template <class bodyT>
void goto_functions_templatet<bodyT>::compute_target_numbers()
{
  for(auto &func : function_map)
  {
    func.second.body.compute_target_numbers();
  }
}

template <class bodyT>
void goto_functions_templatet<bodyT>::compute_loop_numbers()
{
  for(auto &func : function_map)
  {
    func.second.body.compute_loop_numbers();
  }
}

#endif // CPROVER_GOTO_PROGRAMS_GOTO_FUNCTIONS_TEMPLATE_H

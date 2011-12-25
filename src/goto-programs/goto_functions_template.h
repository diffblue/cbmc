/*******************************************************************\

Module: Goto Programs with Functions

Author: Daniel Kroening

Date: June 2003

\*******************************************************************/

#ifndef CPROVER_GOTO_FUNCTIONS_TEMPLATE_H
#define CPROVER_GOTO_FUNCTIONS_TEMPLATE_H

#include <ostream>

#include <std_types.h>
#include <symbol.h>

template <class bodyT>
class goto_function_templatet
{
public:
  bodyT body;
  code_typet type;
  bool body_available;

  bool is_inlined() const
  {
    return type.get_bool(ID_C_inlined);
  }
  
  goto_function_templatet():body_available(false)
  {
  }
  
  void clear()
  {
    body.clear();
    type.clear();
    body_available=false;
  }

  void swap(goto_function_templatet &other)
  {
    body.swap(other.body);
    type.swap(other.type);
    std::swap(body_available, other.body_available);
  }
  
  void copy_from(const goto_function_templatet<bodyT> &other)
  {
    body.copy_from(other.body);
    type=other.type;
    body_available=other.body_available;
  }

  goto_function_templatet(const goto_function_templatet<bodyT> &src):
    type(src.type),
    body_available(src.body_available)
  {
    body.copy_from(src.body);
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
  }

  irep_idt main_id() const
  {
    return ID_main;
  }
  
  void swap(goto_functions_templatet &other)
  {
    function_map.swap(other.function_map);
  }
  
  void copy_from(const goto_functions_templatet &other)
  {
    for(typename function_mapt::const_iterator
        f_it=other.function_map.begin();
        f_it!=other.function_map.end();
        f_it++)
      function_map[f_it->first].copy_from(f_it->second);
  }

private:
  // copy constructor, deliberatly unavailable
  goto_functions_templatet(const goto_functions_templatet<bodyT> &src);
};

/*******************************************************************\

Function: goto_functions_templatet::output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

template <class bodyT>
void goto_functions_templatet<bodyT>::output(
  const namespacet &ns,
  std::ostream& out) const
{
  for(typename function_mapt::const_iterator
      it=function_map.begin();
      it!=function_map.end();
      it++)
  {
    if(it->second.body_available)
    {
      out << "^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^" << std::endl;
      out << std::endl;
      
      const symbolt &symbol=ns.lookup(it->first);
      out << symbol.display_name() << " (" << symbol.name << "):" << std::endl;
      it->second.body.output(ns, symbol.name, out);
    }
  }
}

/*******************************************************************\

Function: goto_functions_templatet::compute_location_numbers

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

template <class bodyT>
void goto_functions_templatet<bodyT>::compute_location_numbers()
{
  unsigned nr=0;

  for(typename function_mapt::iterator
      it=function_map.begin();
      it!=function_map.end();
      it++)
    it->second.body.compute_location_numbers(nr);
}

/*******************************************************************\

Function: goto_functions_templatet::compute_incoming_edges

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

template <class bodyT>
void goto_functions_templatet<bodyT>::compute_incoming_edges()
{
  for(typename function_mapt::iterator
      it=function_map.begin();
      it!=function_map.end();
      it++)
    it->second.body.compute_incoming_edges();
}

/*******************************************************************\

Function: goto_functions_templatet::compute_target_numbers

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

template <class bodyT>
void goto_functions_templatet<bodyT>::compute_target_numbers()
{
  for(typename function_mapt::iterator
      it=function_map.begin();
      it!=function_map.end();
      it++)
    it->second.body.compute_target_numbers();
}

/*******************************************************************\

Function: goto_functions_templatet::compute_loop_numbers

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

template <class bodyT>
void goto_functions_templatet<bodyT>::compute_loop_numbers()
{
  for(typename function_mapt::iterator
      it=function_map.begin();
      it!=function_map.end();
      it++)
    it->second.body.compute_loop_numbers();
}
  
#endif

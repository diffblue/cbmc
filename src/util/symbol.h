/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_SYMBOL_H
#define CPROVER_SYMBOL_H

/*! \file util/symbol.h
 * \brief Symbol table entry
 *
 * \author Daniel Kroening <kroening@kroening.com>
 * \date   Sun Jul 31 21:54:44 BST 2011
*/

/*! \defgroup gr_symbol_table Symbol Table
*/

#include <iosfwd>

#include "expr.h"

/*! \brief Symbol table entry.
    \ingroup gr_symbol_table

    This is a symbol in the symbol table, stored in an
    object of type symbol_tablet.
*/
class symbolt
{
public:
  /// Type of symbol
  typet type;
  
  /// Initial value of symbol
  exprt value;
  
  /// Source code location of definition of symbol
  source_locationt location;
  
  /// The unique identifier
  irep_idt name;
  
  /// Name of module the symbol belongs to
  irep_idt module;
  
  /// Base (non-scoped) name
  irep_idt base_name;
  
  /// Language mode
  irep_idt mode;
  
  /// Language-specific display name
  irep_idt pretty_name;
  
  const irep_idt &display_name() const
  {
    return pretty_name==""?name:pretty_name;
  }
  
  // global use
  bool is_type, is_macro, is_exported,
       is_input, is_output, is_state_var, is_property;
       
  // ANSI-C
  bool is_static_lifetime, is_thread_local;
  bool is_lvalue, is_file_local, is_extern, is_volatile,
       is_parameter, is_auxiliary;

  symbolt()
  {
    clear();
  }
  
  void clear()
  {
    type.make_nil();
    value.make_nil();
    location.make_nil();

    name=module=base_name=mode=pretty_name=irep_idt();

    is_type=is_macro=is_exported=
    is_input=is_output=is_state_var=is_property=
    is_static_lifetime=is_thread_local=
    is_lvalue=is_file_local=is_extern=is_volatile=
    is_parameter=is_auxiliary=false;
  }
     
  void swap(symbolt &b);
  void show(std::ostream &out) const;

  // serialization
  void to_irep(irept &dest) const;
  void from_irep(const irept &src);
  
  class symbol_exprt symbol_expr() const;
  
  inline bool is_shared() const
  {
    return !is_thread_local;
  }
  
  inline bool is_procedure_local() const
  {
    return !is_static_lifetime;
  }
};

std::ostream &operator<<(std::ostream &out,
                         const symbolt &symbol);

#include <list>
 
typedef std::list<symbolt> symbol_listt;

#define forall_symbol_list(it, expr) \
  for(symbol_listt::const_iterator it=(expr).begin(); \
      it!=(expr).end(); ++it)

typedef std::list<const symbolt *> symbolptr_listt;

#define forall_symbolptr_list(it, list) \
  for(symbolptr_listt::const_iterator it=(list).begin(); \
      it!=(list).end(); ++it)

#define Forall_symbolptr_list(it, list) \
  for(symbolptr_listt::iterator it=(list).begin(); \
      it!=(list).end(); ++it)

/*! \brief Symbol table entry describing a data type
    \ingroup gr_symbol_table

    This is a symbol generated as part of type checking.
*/
class type_symbolt:public symbolt
{
public:
  type_symbolt(const typet &_type)
  {
    type=_type;
    is_type=true;
  }
};

/*! \brief Internally generated symbol table entry
    \ingroup gr_symbol_table

    This is a symbol generated as part of translation to or
    modification of the intermediate representation.
*/
class auxiliary_symbolt:public symbolt
{
public:
  auxiliary_symbolt()
  {
    is_lvalue=true;
    is_state_var=true;
    is_thread_local=true;
    is_file_local=true;
    is_auxiliary=true;
  }
};

/*! \brief Symbol table entry of function parameter
    \ingroup gr_symbol_table

    This is a symbol generated as part of type checking.
*/
class parameter_symbolt:public symbolt
{
public:
  parameter_symbolt()
  {
    is_lvalue=true;
    is_state_var=true;
    is_thread_local=true;
    is_file_local=true;
    is_parameter=true;
  }
};

#endif

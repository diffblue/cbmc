/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_SYMBOL_H
#define CPROVER_SYMBOL_H

#include <iostream>
#include <algorithm>

#include "expr.h"
#include "location.h"

class symbolt
{
public:
  typet type;
  exprt value;
  locationt location;
  irep_idt name;
  irep_idt module;
  irep_idt base_name;
  irep_idt mode;
  irep_idt pretty_name;
  
  const irep_idt &display_name() const
  {
    return pretty_name==""?name:pretty_name;
  }
  
  typedef std::list<irep_idt> hierarchyt;
  hierarchyt hierarchy;
  
  unsigned ordering;
  
  // global use
  bool theorem, is_type, is_macro, is_exported,
       is_input, is_output, is_statevar;
       
  // PVS
  bool is_actual, free_var, binding;
  
  // ANSI-C
  bool static_lifetime, thread_local;
  bool lvalue, file_local, is_extern, is_volatile;

  symbolt()
  {
    clear();
  }
  
  void clear()
  {
    value.make_nil();
    location.make_nil();
    lvalue=thread_local=static_lifetime=file_local=is_extern=
    free_var=theorem=
    is_type=is_actual=is_macro=is_exported=binding=
    is_volatile=is_input=is_output=is_statevar=false;
    ordering=0;
    name=module=base_name=mode=pretty_name="";
  }
     
  void swap(symbolt &b)
  {
    #define SYM_SWAP1(x) x.swap(b.x)
    
    SYM_SWAP1(type);
    SYM_SWAP1(value);
    SYM_SWAP1(name);
    SYM_SWAP1(pretty_name);
    SYM_SWAP1(module);
    SYM_SWAP1(base_name);
    SYM_SWAP1(mode);
    SYM_SWAP1(location);

    #define SYM_SWAP2(x) std::swap(x, b.x)
    
    SYM_SWAP2(ordering);
    SYM_SWAP2(theorem);
    SYM_SWAP2(is_type);
    SYM_SWAP2(is_macro);
    SYM_SWAP2(is_exported);
    SYM_SWAP2(is_input);
    SYM_SWAP2(is_output);
    SYM_SWAP2(is_statevar);
    SYM_SWAP2(is_actual);
    SYM_SWAP2(free_var);
    SYM_SWAP2(lvalue);
    SYM_SWAP2(static_lifetime);
    SYM_SWAP2(thread_local);
    SYM_SWAP2(file_local);
    SYM_SWAP2(is_extern);
    SYM_SWAP2(is_volatile);
  }
  
  void show(std::ostream &out) const;

  void to_irep(irept &dest) const;
  void from_irep(const irept &src);
};

std::ostream &operator<<(std::ostream &out,
                         const symbolt &symbol);

#include <list>
 
typedef std::list<symbolt> symbol_listt;

#define forall_symbol_list(it, expr) \
  for(symbol_listt::const_iterator it=(expr).begin(); \
      it!=(expr).end(); it++)

typedef std::list<const symbolt *> symbolptr_listt;

#define forall_symbolptr_list(it, list) \
  for(symbolptr_listt::const_iterator it=(list).begin(); \
      it!=(list).end(); it++)

#define Forall_symbolptr_list(it, list) \
  for(symbolptr_listt::iterator it=(list).begin(); \
      it!=(list).end(); it++)


bool is_global(const symbolt& symbol);

bool is_thread_local(const symbolt& symbol);

bool is_procedure_local(const symbolt& symbol);


#endif

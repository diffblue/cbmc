/*******************************************************************\

Module: Variable Numbering

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_PATH_SYMEX_VAR_MAP_H
#define CPROVER_PATH_SYMEX_VAR_MAP_H

#include <iosfwd>
#include <map>

#include <util/namespace.h>
#include <util/type.h>

class var_mapt
{
public:
  explicit var_mapt(const namespacet &_ns):
    ns(_ns), shared_count(0), local_count(0), nondet_count(0), dynamic_count(0)
  {
  }

  struct var_infot
  {
    enum { SHARED, THREAD_LOCAL, PROCEDURE_LOCAL } kind;
    
    inline bool is_shared() const
    {
      return kind==SHARED;
    }

    // the variables are numbered
    unsigned number;

    // full_identifier=symbol+suffix
    irep_idt full_identifier, symbol, suffix;

    // the type of the identifier (struct member or array)
    typet type;
    
    unsigned ssa_counter;
    
    var_infot():kind(SHARED), number(0), ssa_counter(0)
    {
    }
    
    irep_idt ssa_identifier() const;

    symbol_exprt ssa_symbol() const
    {
      symbol_exprt s=symbol_exprt(ssa_identifier(), type);
      s.set(ID_C_SSA_symbol, true);
      s.set(ID_C_full_identifier, full_identifier);
      return s;
    }

    inline void increment_ssa_counter() 
    {
      ++ssa_counter;
    }
    
    void output(std::ostream &out) const;
  };
  
  typedef std::map<irep_idt, var_infot> id_mapt;
  id_mapt id_map;

  var_infot &operator()(
    const irep_idt &symbol,
    const irep_idt &suffix,
    const typet &type);
  
  inline var_infot &operator[](const irep_idt &full_identifier)
  {
    return id_map[full_identifier];
  }
  
  void init(var_infot &var_info);

  const namespacet &ns;
  
  void output(std::ostream &) const;

protected:
  unsigned shared_count, local_count;

public:
  unsigned nondet_count;  // free inputs
  unsigned dynamic_count; // memory allocation  
};

#endif

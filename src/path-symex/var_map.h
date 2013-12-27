/*******************************************************************\

Module: Variable Numbering

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_VAR_MAP_H
#define CPROVER_VAR_MAP_H

#include <map>

#include <util/namespace.h>
#include <util/expr.h>

#include <path-symex/loc_ref.h>

class var_mapt
{
public:
  explicit var_mapt(const namespacet &_ns):
    ns(_ns), shared_count(0), local_count(0), nondet_count(0), dynamic_count(0)
  {
  }

  struct var_infot
  {
    enum { SHARED, THREAD_LOCAL, PROCEDURE_LOCAL , DYNAMIC} kind;
    
    inline bool is_shared() const
    {
      return kind==SHARED;
    }

    // the variables are numbered
    unsigned number;

    // identifier=symbol+suffix
    irep_idt identifier, symbol, suffix;

    // the type of the field/array
    typet type;
    
    unsigned ssa_counter;
    
    var_infot():kind(SHARED), number(0), ssa_counter(0)
    {
    }
    
    irep_idt ssa_identifier(unsigned thread) const;

	  inline void increment_ssa_counter() 
	  {
		  ++ssa_counter;
	  }
  };
  
  typedef std::map<irep_idt, var_infot> id_mapt;
  id_mapt id_map;

  void strip(std::string& s, char c)
  {
    std::size_t pos=s.rfind(c);
    if(pos!=std::string::npos) {
       s.erase(pos,s.size());  
    } 
  }

  inline var_infot &operator()(
    const irep_idt &identifier,
    const irep_idt &suffix,
    const typet &type)
  {

    std::pair<id_mapt::iterator, bool> result;

    std::string id(id2string(identifier)+id2string(suffix));

     // drop the #
    strip(id,'#');

    result=
    id_map.insert(std::pair<irep_idt, var_infot>(
      id, var_infot()));      
  
    if(result.second) // inserted?
      init(identifier, suffix, type, result.first->second);
    
    return result.first->second;
  }
  
  void init(
    const irep_idt &identifier,
    const irep_idt &suffix,
    const typet &type,
    var_infot &var_info);

  // maps function identifiers to first PC and function type
  typedef std::pair<loc_reft,code_typet> function_entryt;
  typedef std::map<irep_idt, function_entryt> function_mapt;
  function_mapt function_map;

  // if expr is a symbol.member, return var_info
  // otherwise return NULL
  inline var_infot *operator()(const exprt &expr)
  {
    return expr_rec(expr, "", expr.type());
  }

  bool is_symex(const exprt &src);

  bool is_nondet(const exprt &src);

  const namespacet &ns;

protected:
  unsigned shared_count, local_count;

  var_infot *expr_rec(
    const exprt &expr,
    const std::string &suffix,
    const typet &type);

public:
  unsigned nondet_count;  // free inputs
  unsigned dynamic_count; // memory allocation
  
};

#endif

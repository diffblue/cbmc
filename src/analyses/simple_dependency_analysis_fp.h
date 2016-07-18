/*******************************************************************\

Module: Global dependency analysis

Author: Daniel Poetzl

\*******************************************************************/

#ifndef CPROVER_ANALYSES_SIMPLE_DEPENDENCY_ANALYSIS_H
#define CPROVER_ANALYSES_SIMPLE_DEPENDENCY_ANALYSIS_H

#include <memory>

#include <goto-programs/goto_functions.h>
#include <util/expr.h>
#include <util/type.h>
#include <util/misc_utils.h>

// base class
class gather_symbolst:public std::set<irep_idt>,public const_cond_expr_visitort
{};

// get all symbols used in an expression
class gather_symbols_indicest:public gather_symbolst
{
  virtual bool operator()(const exprt &expr)
  {
    if(expr.id()==ID_symbol)
    {
      const symbol_exprt &symbol_expr=to_symbol_expr(expr);
      irep_idt id=symbol_expr.get_identifier();
      insert(id);
    }

    return true;
  }
};

// get all symbols, ignore subexpressions used as array indices
class gather_symbols_no_indicest:public gather_symbolst
{
  virtual bool operator()(const exprt &expr)
  {
    if(expr.id()==ID_index)
    {
      const index_exprt &index_expr=to_index_expr(expr);
      index_expr.array().visit(*this);
      return false; // do not visit index expression
    }

    if(expr.id()==ID_symbol)
    {
      const symbol_exprt &symbol_expr=to_symbol_expr(expr);
      irep_idt id=symbol_expr.get_identifier();
      insert(id);
    }

    return true;
  }
};

#if 0
class gather_symbols_allt:
  public std::set<irep_idt>,public const_cond_expr_visitort
{
public:
  gather_symbols_allt(bool address_subexprs=false, bool ignore_indices=true) :
    address_subexprs(address_subexprs), ignore_indices(ignore_indices) {}

  bool address_subexprs;
  bool ignore_indices;

  virtual bool operator()(const exprt &expr)
  {
    if(address_subexprs)
    {
      if(expr.id()==ID_address_of)
      {
        const address_of_exprt &address_of_expr=to_address_of_expr(expr);
        gather_symbols_allt gs(false, ignore_indices);
        address_of_expr.object().visit(gs);
        insert(gs.begin(), gs.end());

        return false; // address of subexpression already visited
      }

      return true;
    }

    assert(!address_subexprs);

    if(ignore_indices)
    {
      if(expr.id()==ID_index)
      {
        const index_exprt &index_expr=to_index_expr(expr);
        index_expr.array().visit(*this);
        return false; // do not visit index expression
      }
    }

    assert(expr.id()!=ID_index);

    if(expr.id()==ID_symbol)
    {
      const symbol_exprt &symbol_expr=to_symbol_expr(expr);
      irep_idt id=symbol_expr.get_identifier();
      insert(id);
    }

    return true;
  }
};
#endif

class simple_dependency_analysist
{
public:
  simple_dependency_analysist(
    const goto_functionst &goto_functions, bool ignore_indices=true) :
    goto_functions(goto_functions),
    ignore_indices(ignore_indices),
    num_assignments(0),
    num_significant_assignments(0),
    num_functions(0),
    num_functions_body(0),
    num_significant_functions_body(0)
  {}

  typedef std::vector<exprt> expr_vect;

  typedef goto_programt::const_targett locationt;
  typedef std::set<locationt> location_sett;

  typedef std::set<irep_idt> id_sett;
  typedef std::vector<exprt> argumentst;

  typedef goto_functionst::goto_functiont goto_functiont;

  void operator()(
    const expr_vect &expr_vec, // input
    location_sett &location_set, // output
    id_sett &id_set); // output

  void output_stats(std::ostream &out) const;

  void clear()
  {
    num_assignments=0;
    num_significant_assignments=0;
    num_functions=0;
    num_functions_body=0;
    num_significant_functions_body=0;
  }

protected:
  const goto_functionst &goto_functions;
  bool ignore_indices;

  unsigned num_assignments;
  unsigned num_significant_assignments;

  unsigned num_functions;
  unsigned num_functions_body;
  unsigned num_significant_functions_body;

  unsigned num_iterations;

  bool is_handled(irep_idt id);

  bool handle_thread_create(
    locationt l,
    const argumentst &args,
    location_sett &other_locations,
    id_sett &id_set);

  bool handle_function_call(
    irep_idt id,
    locationt l,
    const exprt &lhs,
    const argumentst &args,
    location_sett &other_locations,
    id_sett &id_set);

  // check if sets have common elements
  bool have_common_elements(const id_sett &set1, const id_sett &set2)
  {
    for(id_sett::const_iterator it=set1.begin();
        it!=set1.end(); it++)
    {
      if(set2.find(*it)!=set2.end())
        return true;
    }
    return false;
  }

  // get ids of functions that could be used as threads
  void get_thread_functions(std::set<irep_idt> &funcs);

  // get the expressions used in returns
  void get_returns(
    const goto_programt &goto_program,
    expr_vect &expr_vec,
    location_sett &location_set);

  void postprocess(
    location_sett &location_set,
    const id_sett &id_set);

  // factory method
  gather_symbolst *create_gather_symbols()
  {
    if(ignore_indices)
      return new gather_symbols_no_indicest();
    else
      return new gather_symbols_indicest();
  }
};

#endif

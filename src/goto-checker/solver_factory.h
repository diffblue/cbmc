/*******************************************************************\

Module: Solver Factory

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Solver Factory

#ifndef CPROVER_GOTO_CHECKER_SOLVER_FACTORY_H
#define CPROVER_GOTO_CHECKER_SOLVER_FACTORY_H

#include <list>
#include <map>
#include <memory>

#include <util/options.h>

#include <goto-symex/symex_target_equation.h>
#include <solvers/prop/prop.h>
#include <solvers/prop/prop_conv.h>
#include <solvers/sat/cnf.h>
#include <solvers/sat/satcheck.h>
#include <solvers/smt2/smt2_dec.h>

class solver_factoryt
{
public:
  solver_factoryt(
    const optionst &_options,
    const symbol_tablet &_symbol_table,
    message_handlert &_message_handler,
    bool _output_xml_in_refinement)
    : options(_options),
      symbol_table(_symbol_table),
      ns(_symbol_table),
      message_handler(_message_handler),
      output_xml_in_refinement(_output_xml_in_refinement)
  {
  }

  // The solver class,
  // which owns a variety of allocated objects.
  class solvert
  {
  public:
    solvert()
    {
    }

    explicit solvert(std::unique_ptr<prop_convt> p)
      : prop_conv_ptr(std::move(p))
    {
    }

    solvert(std::unique_ptr<prop_convt> p1, std::unique_ptr<propt> p2)
      : prop_ptr(std::move(p2)), prop_conv_ptr(std::move(p1))
    {
    }

    solvert(std::unique_ptr<prop_convt> p1, std::unique_ptr<std::ofstream> p2)
      : ofstream_ptr(std::move(p2)), prop_conv_ptr(std::move(p1))
    {
    }

    prop_convt &prop_conv() const
    {
      PRECONDITION(prop_conv_ptr != nullptr);
      return *prop_conv_ptr;
    }

    propt &prop() const
    {
      PRECONDITION(prop_ptr != nullptr);
      return *prop_ptr;
    }

    void set_prop_conv(std::unique_ptr<prop_convt> p)
    {
      prop_conv_ptr = std::move(p);
    }

    void set_prop(std::unique_ptr<propt> p)
    {
      prop_ptr = std::move(p);
    }

    void set_ofstream(std::unique_ptr<std::ofstream> p)
    {
      ofstream_ptr = std::move(p);
    }

    // the objects are deleted in the opposite order they appear below
    std::unique_ptr<std::ofstream> ofstream_ptr;
    std::unique_ptr<propt> prop_ptr;
    std::unique_ptr<prop_convt> prop_conv_ptr;
  };

  // returns a solvert object
  virtual std::unique_ptr<solvert> get_solver()
  {
    if(options.get_bool_option("dimacs"))
      return get_dimacs();
    if(options.get_bool_option("refine"))
      return get_bv_refinement();
    else if(options.get_bool_option("refine-strings"))
      return get_string_refinement();
    if(options.get_bool_option("smt2"))
      return get_smt2(get_smt2_solver_type());
    return get_default();
  }

  virtual ~solver_factoryt()
  {
  }

protected:
  const optionst &options;
  const symbol_tablet &symbol_table;
  namespacet ns;
  message_handlert &message_handler;
  const bool output_xml_in_refinement;

  std::unique_ptr<solvert> get_default();
  std::unique_ptr<solvert> get_dimacs();
  std::unique_ptr<solvert> get_bv_refinement();
  std::unique_ptr<solvert> get_string_refinement();
  std::unique_ptr<solvert> get_smt2(smt2_dect::solvert solver);

  smt2_dect::solvert get_smt2_solver_type() const;

  // consistency checks during solver creation
  void no_beautification();
  void no_incremental_check();
};

#endif // CPROVER_GOTO_CHECKER_SOLVER_FACTORY_H

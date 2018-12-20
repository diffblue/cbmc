/*******************************************************************\

Module: Solver Factory

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Solver Factory

#ifndef CPROVER_GOTO_CHECKER_SOLVER_FACTORY_H
#define CPROVER_GOTO_CHECKER_SOLVER_FACTORY_H

#include <memory>

#include <solvers/smt2/smt2_dec.h>

class message_handlert;
class namespacet;
class optionst;
class propt;
class prop_convt;
class symbol_tablet;

class solver_factoryt
{
public:
  solver_factoryt(
    const optionst &_options,
    const symbol_tablet &_symbol_table,
    message_handlert &_message_handler,
    bool _output_xml_in_refinement);

  // The solver class,
  // which owns a variety of allocated objects.
  class solvert
  {
  public:
    solvert() = default;
    explicit solvert(std::unique_ptr<prop_convt> p);
    solvert(std::unique_ptr<prop_convt> p1, std::unique_ptr<propt> p2);
    solvert(std::unique_ptr<prop_convt> p1, std::unique_ptr<std::ofstream> p2);

    prop_convt &prop_conv() const;
    propt &prop() const;

    void set_prop_conv(std::unique_ptr<prop_convt> p);
    void set_prop(std::unique_ptr<propt> p);
    void set_ofstream(std::unique_ptr<std::ofstream> p);

    // the objects are deleted in the opposite order they appear below
    std::unique_ptr<std::ofstream> ofstream_ptr;
    std::unique_ptr<propt> prop_ptr;
    std::unique_ptr<prop_convt> prop_conv_ptr;
  };

  /// Returns a solvert object
  virtual std::unique_ptr<solvert> get_solver();

  virtual ~solver_factoryt() = default;

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

/*******************************************************************\

Module: Bounded Model Checking for Test Suite Generation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Bounded Model Checking for Test Suite Generation

#ifndef CPROVER_CCOVER_CCOVER_BMC_H
#define CPROVER_CCOVER_CCOVER_BMC_H

#include <memory>

#include <util/ui_message.h>

#include <goto-programs/goto_trace.h>

#include <goto-symex/symex_target_equation.h>
#include <goto-programs/goto_model.h>
#include <goto-symex/memory_model.h>

#include <cbmc/symex_bmc.h>

class optionst;

class ccover_bmct:public messaget
{
public:
  ccover_bmct(
    const optionst &_options,
    const symbol_tablet &outer_symbol_table,
    message_handlert &_message_handler,
    prop_convt &_prop_conv,
    path_storaget &_path_storage)
    : messaget(_message_handler),
      options(_options),
      outer_symbol_table(outer_symbol_table),
      ns(outer_symbol_table, symex_symbol_table),
      equation(),
      path_storage(_path_storage),
      symex(_message_handler, outer_symbol_table, equation, _options, path_storage),
      prop_conv(_prop_conv),
      ui(ui_message_handlert::uit::PLAIN)
  {
    symex.constant_propagation=options.get_bool_option("propagation");
    symex.record_coverage=
      !options.get_option("symex-coverage-report").empty();
  }

  void run(abstract_goto_modelt &);

  virtual ~ccover_bmct() { }

  void set_ui(ui_message_handlert::uit _ui) { ui=_ui; }

  static int do_bmc(
    const optionst &opts,
    abstract_goto_modelt &goto_model,
    const ui_message_handlert::uit &ui,
    message_handlert &);

protected:
  const optionst &options;
  /// \brief symbol table for the goto-program that we will execute

  const symbol_tablet &outer_symbol_table;
  /// \brief symbol table generated during symbolic execution

  symbol_tablet symex_symbol_table;
  namespacet ns;
  symex_target_equationt equation;
  path_storaget &path_storage;
  symex_bmct symex;
  prop_convt &prop_conv;
  std::unique_ptr<memory_model_baset> memory_model;
  // use gui format
  ui_message_handlert::uit ui;

  // unwinding
  void setup_unwind();
  void do_conversion();

  trace_optionst trace_options()
  {
    return trace_optionst(options);
  }

  void setup();
  void get_memory_model();
  void slice();

  bool cover(const goto_functionst &);

  friend class bmc_covert;
};

#endif // CPROVER_CCOVER_CCOVER_BMC_H

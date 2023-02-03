/*******************************************************************\

Module: Coverage Instrumentation

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// Coverage Instrumentation

#ifndef CPROVER_GOTO_INSTRUMENT_COVER_INSTRUMENT_H
#define CPROVER_GOTO_INSTRUMENT_COVER_INSTRUMENT_H

#include <util/namespace.h>

#include <goto-programs/goto_program.h>

#include <memory>

enum class coverage_criteriont;
class cover_blocks_baset;
class goal_filterst;

/// Base class for goto program coverage instrumenters
class cover_instrumenter_baset
{
public:
  virtual ~cover_instrumenter_baset() = default;
  cover_instrumenter_baset(
    const symbol_table_baset &_symbol_table,
    const goal_filterst &_goal_filters,
    const irep_idt &_coverage_criterion)
    : coverage_criterion(_coverage_criterion),
      ns(_symbol_table),
      goal_filters(_goal_filters)
  {
  }

  /// The type of function used to make goto_program assertions.
  using assertion_factoryt = std::function<
    goto_programt::instructiont(const exprt &, const source_locationt &)>;
  static_assert(
    std::is_same<
      assertion_factoryt,
      std::function<decltype(goto_programt::make_assertion)>>::value,
    "`assertion_factoryt` is expected to have the same type as "
    "`goto_programt::make_assertion`.");

  /// Instruments a goto program
  /// \param function_id: name of \p goto_program
  /// \param goto_program: a goto program
  /// \param basic_blocks: detected basic blocks
  /// \param make_assertion: A function which makes goto program assertions.
  ///    This parameter may be used to customise the expressions asserted.
  void operator()(
    const irep_idt &function_id,
    goto_programt &goto_program,
    const cover_blocks_baset &basic_blocks,
    const assertion_factoryt &make_assertion) const
  {
    Forall_goto_program_instructions(i_it, goto_program)
    {
      instrument(function_id, goto_program, i_it, basic_blocks, make_assertion);
    }
  }

  const irep_idt property_class = "coverage";
  const irep_idt coverage_criterion;

protected:
  const namespacet ns;
  const goal_filterst &goal_filters;

  /// Override this method to implement an instrumenter
  virtual void instrument(
    const irep_idt &function_id,
    goto_programt &,
    goto_programt::targett &,
    const cover_blocks_baset &,
    const assertion_factoryt &) const = 0;

  void initialize_source_location(
    source_locationt &source_location,
    const std::string &comment,
    const irep_idt &function_id) const
  {
    source_location.set_comment(comment);
    source_location.set(ID_coverage_criterion, coverage_criterion);
    source_location.set_property_class(property_class);
    source_location.set_function(function_id);
  }

  bool is_non_cover_assertion(goto_programt::const_targett t) const
  {
    return t->is_assert() &&
           t->source_location().get_property_class() != property_class;
  }
};

/// A collection of instrumenters to be run
class cover_instrumenterst
{
public:
  void add_from_criterion(
    coverage_criteriont,
    const symbol_table_baset &,
    const goal_filterst &);

  /// Applies all instrumenters to the given goto program
  /// \param function_id: name of \p goto_program
  /// \param goto_program: a goto program
  /// \param basic_blocks: detected basic blocks of the goto program
  /// \param make_assertion: A function which makes goto program assertions.
  ///    This parameter may be used to customise the expressions asserted.
  void operator()(
    const irep_idt &function_id,
    goto_programt &goto_program,
    const cover_blocks_baset &basic_blocks,
    const cover_instrumenter_baset::assertion_factoryt &make_assertion) const
  {
    for(const auto &instrumenter : instrumenters)
      (*instrumenter)(function_id, goto_program, basic_blocks, make_assertion);
  }

private:
  std::vector<std::unique_ptr<cover_instrumenter_baset>> instrumenters;
};

/// Basic block coverage instrumenter
class cover_location_instrumentert : public cover_instrumenter_baset
{
public:
  cover_location_instrumentert(
    const symbol_table_baset &_symbol_table,
    const goal_filterst &_goal_filters)
    : cover_instrumenter_baset(_symbol_table, _goal_filters, "location")
  {
  }

protected:
  void instrument(
    const irep_idt &function_id,
    goto_programt &,
    goto_programt::targett &,
    const cover_blocks_baset &,
    const assertion_factoryt &) const override;
};

/// Branch coverage instrumenter
class cover_branch_instrumentert : public cover_instrumenter_baset
{
public:
  cover_branch_instrumentert(
    const symbol_table_baset &_symbol_table,
    const goal_filterst &_goal_filters)
    : cover_instrumenter_baset(_symbol_table, _goal_filters, "branch")
  {
  }

protected:
  void instrument(
    const irep_idt &function_id,
    goto_programt &,
    goto_programt::targett &,
    const cover_blocks_baset &,
    const assertion_factoryt &) const override;
};

/// Condition coverage instrumenter
class cover_condition_instrumentert : public cover_instrumenter_baset
{
public:
  cover_condition_instrumentert(
    const symbol_table_baset &_symbol_table,
    const goal_filterst &_goal_filters)
    : cover_instrumenter_baset(_symbol_table, _goal_filters, "condition")
  {
  }

protected:
  void instrument(
    const irep_idt &function_id,
    goto_programt &,
    goto_programt::targett &,
    const cover_blocks_baset &,
    const assertion_factoryt &) const override;
};

/// Decision coverage instrumenter
class cover_decision_instrumentert : public cover_instrumenter_baset
{
public:
  cover_decision_instrumentert(
    const symbol_table_baset &_symbol_table,
    const goal_filterst &_goal_filters)
    : cover_instrumenter_baset(_symbol_table, _goal_filters, "decision")
  {
  }

protected:
  void instrument(
    const irep_idt &function_id,
    goto_programt &,
    goto_programt::targett &,
    const cover_blocks_baset &,
    const assertion_factoryt &) const override;
};

/// MC/DC coverage instrumenter
class cover_mcdc_instrumentert : public cover_instrumenter_baset
{
public:
  cover_mcdc_instrumentert(
    const symbol_table_baset &_symbol_table,
    const goal_filterst &_goal_filters)
    : cover_instrumenter_baset(_symbol_table, _goal_filters, "MC/DC")
  {
  }

protected:
  void instrument(
    const irep_idt &function_id,
    goto_programt &,
    goto_programt::targett &,
    const cover_blocks_baset &,
    const assertion_factoryt &) const override;
};

/// Path coverage instrumenter
class cover_path_instrumentert : public cover_instrumenter_baset
{
public:
  cover_path_instrumentert(
    const symbol_table_baset &_symbol_table,
    const goal_filterst &_goal_filters)
    : cover_instrumenter_baset(_symbol_table, _goal_filters, "path")
  {
  }

protected:
  void instrument(
    const irep_idt &function_id,
    goto_programt &,
    goto_programt::targett &,
    const cover_blocks_baset &,
    const assertion_factoryt &) const override;
};

/// Assertion coverage instrumenter
class cover_assertion_instrumentert : public cover_instrumenter_baset
{
public:
  cover_assertion_instrumentert(
    const symbol_table_baset &_symbol_table,
    const goal_filterst &_goal_filters)
    : cover_instrumenter_baset(_symbol_table, _goal_filters, "assertion")
  {
  }

protected:
  void instrument(
    const irep_idt &function_id,
    goto_programt &,
    goto_programt::targett &,
    const cover_blocks_baset &,
    const assertion_factoryt &) const override;
};

/// __CPROVER_cover coverage instrumenter
class cover_cover_instrumentert : public cover_instrumenter_baset
{
public:
  cover_cover_instrumentert(
    const symbol_table_baset &_symbol_table,
    const goal_filterst &_goal_filters)
    : cover_instrumenter_baset(_symbol_table, _goal_filters, "cover")
  {
  }

protected:
  void instrument(
    const irep_idt &function_id,
    goto_programt &,
    goto_programt::targett &,
    const cover_blocks_baset &,
    const assertion_factoryt &) const override;
};

void cover_instrument_end_of_function(
  const irep_idt &function_id,
  goto_programt &goto_program,
  const cover_instrumenter_baset::assertion_factoryt &);

// assume-instructions instrumenter.
class cover_assume_instrumentert : public cover_instrumenter_baset
{
public:
  cover_assume_instrumentert(
    const symbol_table_baset &_symbol_table,
    const goal_filterst &_goal_filters)
    : cover_instrumenter_baset(_symbol_table, _goal_filters, "location")
  {
  }

protected:
  void instrument(
    const irep_idt &,
    goto_programt &,
    goto_programt::targett &,
    const cover_blocks_baset &,
    const assertion_factoryt &) const override;
};

#endif // CPROVER_GOTO_INSTRUMENT_COVER_INSTRUMENT_H

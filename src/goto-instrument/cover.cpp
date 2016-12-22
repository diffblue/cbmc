/*******************************************************************\

Module: Coverage Instrumentation

Author: Daniel Kroening

Date: May 2016

\*******************************************************************/

#include <algorithm>
#include <iterator>

#include <util/prefix.h>
#include <util/i2string.h>
#include <util/expr_util.h>

#include "cover.h"
#include "cover_mcdc.h"

/*******************************************************************\

Function: as_string

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

const char *as_string(coverage_criteriont c)
{
  switch(c)
  {
  case coverage_criteriont::LOCATION: return "location";
  case coverage_criteriont::BRANCH: return "branch";
  case coverage_criteriont::DECISION: return "decision";
  case coverage_criteriont::CONDITION: return "condition";
  case coverage_criteriont::PATH: return "path";
  case coverage_criteriont::MCDC: return "MC/DC";
  case coverage_criteriont::ASSERTION: return "assertion";
  case coverage_criteriont::COVER: return "cover instructions";
  default: return "";
  }
}

/*******************************************************************\

Function: instrument_assertion

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void instrument_cover_goalst::instrument_assertion(
  goto_programt::instructionst::iterator &insn)
{
  if(insn->is_assert())
  {
    insn->guard=false_exprt();
    insn->source_location.set(ID_coverage_criterion, coverage_criterion);
    insn->source_location.set_property_class(property_class);
  }
}

/*******************************************************************\

Function: instrument_cover

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void instrument_cover_goalst::instrument_cover(
  goto_programt::instructionst::iterator &insn)
{
  if(insn->is_function_call())
  {
    const code_function_callt &code_function_call=
      to_code_function_call(insn->code);
    if(code_function_call.function().id()==ID_symbol &&
       to_symbol_expr(code_function_call.function()).get_identifier()==
       "__CPROVER_cover" &&
       code_function_call.arguments().size()==1)
    {
      const exprt c=code_function_call.arguments()[0];
      std::string comment="condition `"+from_expr(ns, "", c)+"'";
      insn->guard=not_exprt(c);
      insn->type=ASSERT;
      insn->code.clear();
      insn->source_location.set_comment(comment);
      insn->source_location.set(ID_coverage_criterion, coverage_criterion);
      insn->source_location.set_property_class(property_class);
    }
  }
  else if(insn->is_assert())
    insn->make_skip();
}

/*******************************************************************\

Function: instrument_location

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void instrument_cover_goalst::instrument_location(
  goto_programt::instructionst::iterator &insn,
  goto_programt &goto_program,
  basic_blockst &basic_blocks,
  std::set<unsigned> &blocks_done)
{
  if(insn->is_assert())
    insn->make_skip();

  unsigned block_nr=basic_blocks[insn];
  if(blocks_done.insert(block_nr).second)
  {
    std::string b=i2string(block_nr);
    std::string id=id2string(insn->function)+"#"+b;
    source_locationt source_location=
      basic_blocks.source_location_map[block_nr];

    if(!source_location.get_file().empty() &&
       source_location.get_file()[0]!='<')
    {
      std::string comment="block "+b;
      goto_program.insert_before_swap(insn);
      insn->make_assertion(false_exprt());
      insn->source_location=source_location;
      insn->source_location.set_comment(comment);
      insn->source_location.set(ID_coverage_criterion, coverage_criterion);
      insn->source_location.set_property_class(property_class);

      insn++;
    }
  }
}

/*******************************************************************\

Function: instrument_branch

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void instrument_cover_goalst::instrument_branch(
  goto_programt::instructionst::iterator &insn,
  goto_programt &goto_program,
  basic_blockst &basic_blocks)
{
  if(insn->is_assert())
    insn->make_skip();

  if(insn==goto_program.instructions.begin())
  {
    // we want branch coverage to imply 'entry point of function'
    // coverage
    std::string comment=
      "function "+id2string(insn->function)+" entry point";

    source_locationt source_location=insn->source_location;

    goto_programt::targett t=goto_program.insert_before(insn);
    t->make_assertion(false_exprt());
    t->source_location=source_location;
    t->source_location.set_comment(comment);
    t->source_location.set(ID_coverage_criterion, coverage_criterion);
    t->source_location.set_property_class(property_class);
  }

  if(insn->is_goto() && !insn->guard.is_true())
  {
    std::string b=i2string(basic_blocks[insn]);
    std::string true_comment=
      "function "+id2string(insn->function)+" block "+b+" branch true";
    std::string false_comment=
      "function "+id2string(insn->function)+" block "+b+" branch false";

    exprt guard=insn->guard;
    source_locationt source_location=insn->source_location;

    goto_program.insert_before_swap(insn);
    insn->make_assertion(not_exprt(guard));
    insn->source_location=source_location;
    insn->source_location.set_comment(true_comment);
    insn->source_location.set(ID_coverage_criterion, coverage_criterion);
    insn->source_location.set_property_class(property_class);

    goto_program.insert_before_swap(insn);
    insn->make_assertion(guard);
    insn->source_location=source_location;
    insn->source_location.set_comment(false_comment);
    insn->source_location.set(ID_coverage_criterion, coverage_criterion);
    insn->source_location.set_property_class(property_class);

    insn++;
    insn++;
  }
}

/*******************************************************************\

Function: instrument_condition

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void instrument_cover_goalst::instrument_condition(
  goto_programt::instructionst::iterator &insn,
  goto_programt &goto_program)
{
  if(insn->is_assert())
    insn->make_skip();

  // Conditions are all atomic predicates in the programs.
  {
    const std::set<exprt> conditions=collect_conditions(insn);

    const source_locationt source_location=insn->source_location;

    for(const auto & c : conditions)
    {
      const std::string c_string=from_expr(ns, "", c);

      const std::string comment_t="condition `"+c_string+"' true";
      goto_program.insert_before_swap(insn);
      insn->make_assertion(c);
      insn->source_location=source_location;
      insn->source_location.set_comment(comment_t);
      insn->source_location.set(ID_coverage_criterion, coverage_criterion);
      insn->source_location.set_property_class(property_class);

      const std::string comment_f="condition `"+c_string+"' false";
      goto_program.insert_before_swap(insn);
      insn->make_assertion(not_exprt(c));
      insn->source_location=source_location;
      insn->source_location.set_comment(comment_f);
      insn->source_location.set(ID_coverage_criterion, coverage_criterion);
      insn->source_location.set_property_class(property_class);
    }

    for(std::size_t i=0; i<conditions.size()*2; i++)
      insn++;
  }
}

/*******************************************************************\

Function: instrument_decision

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void instrument_cover_goalst::instrument_decision(
  goto_programt::instructionst::iterator &insn,
  goto_programt &goto_program)
{
  if(insn->is_assert())
    insn->make_skip();

  // Decisions are maximal Boolean combinations of conditions.
  {
    const std::set<exprt> decisions=collect_decisions(insn);

    const source_locationt source_location=insn->source_location;

    for(const auto & d : decisions)
    {
      const std::string d_string=from_expr(ns, "", d);

      const std::string comment_t="decision `"+d_string+"' true";
      goto_program.insert_before_swap(insn);
      insn->make_assertion(d);
      insn->source_location=source_location;
      insn->source_location.set_comment(comment_t);
      insn->source_location.set(ID_coverage_criterion, coverage_criterion);
      insn->source_location.set_property_class(property_class);

      const std::string comment_f="decision `"+d_string+"' false";
      goto_program.insert_before_swap(insn);
      insn->make_assertion(not_exprt(d));
      insn->source_location=source_location;
      insn->source_location.set_comment(comment_f);
      insn->source_location.set(ID_coverage_criterion, coverage_criterion);
      insn->source_location.set_property_class(property_class);
    }

    for(std::size_t i=0; i<decisions.size()*2; i++)
      insn++;
  }
}

/*******************************************************************\

Function: instrument_cover_goals

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void instrument_cover_goalst::instrument_cover_goals(
  goto_programt &goto_program)
{
  basic_blockst basic_blocks(goto_program);
  std::set<unsigned> blocks_done;

  // ignore if built-in library
  if(!goto_program.instructions.empty() &&
     has_prefix(
       id2string(
         goto_program.instructions.front().source_location.get_file()),
         "<builtin-library-"))
    return;

  for(const auto &criterion : criteria)
  {
    coverage_criterion=as_string(criterion);
    property_class="coverage";

    instrument_mcdc_goalst mcdc(ns, criteria, coverage_criterion, property_class);

    Forall_goto_program_instructions(i_it, goto_program)
    {
      switch(criterion)
      {
      case coverage_criteriont::ASSERTION:
        // turn into 'assert(false)' to avoid simplification
        instrument_assertion(i_it);
        break;

      case coverage_criteriont::COVER:
        // turn __CPROVER_cover(x) into 'assert(!x)'
        instrument_cover(i_it);
        break;

      case coverage_criteriont::LOCATION:
        instrument_location(i_it, goto_program, basic_blocks, blocks_done);
        break;

      case coverage_criteriont::BRANCH:
        instrument_branch(i_it, goto_program, basic_blocks);
        break;

      case coverage_criteriont::CONDITION:
        instrument_condition(i_it, goto_program);
        break;

      case coverage_criteriont::DECISION:
        instrument_decision(i_it, goto_program);
        break;

      case coverage_criteriont::PATH:
        if(i_it->is_assert())
          i_it->make_skip();
        break;

      case coverage_criteriont::MCDC:
    	mcdc.instrument_mcdc(i_it, goto_program, basic_blocks, blocks_done);
        break;

      default: {}
      }
    }
  }
}

/*******************************************************************\

Function: instrument_cover_goals

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void instrument_cover_goalst::instrument_cover_goals(
  goto_functionst &goto_functions)
{
  Forall_goto_functions(f_it, goto_functions)
  {
    if(f_it->first==ID__start ||
       f_it->first=="__CPROVER_initialize")
      continue;

    instrument_cover_goals(f_it->second.body);
  }
}

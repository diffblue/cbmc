/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "smt2_dec.h"

#include <util/invariant.h>
#include <util/message.h>
#include <util/run.h>
#include <util/tempfile.h>

#include <solvers/prop/literal_expr.h>

#include "smt2irep.h"

#include <fstream>

static std::string drop_quotes(std::string src)
{
  if(src.size() >= 2 && src.front() == '|' && src.back() == '|')
    return std::string(src, 1, src.size() - 2);
  else
    return src;
}

std::string smt2_dect::decision_procedure_text() const
{
  // clang-format off
  return "SMT2 " + logic + (use_FPA_theory ? " (with FPA)" : "") + " using " +
    (solver==solvert::GENERIC?"Generic":
     solver==solvert::BITWUZLA?"Bitwuzla":
     solver==solvert::BOOLECTOR?"Boolector":
     solver==solvert::CPROVER_SMT2?"CPROVER SMT2":
     solver==solvert::CVC5?"CVC5":
     solver==solvert::MATHSAT?"MathSAT":
     solver==solvert::YICES?"Yices":
     solver==solvert::Z3?"Z3":
     "(unknown)");
  // clang-format on
}

bool smt2_dect::is_in_conflict(const exprt &expr) const
{
  if(expr.id() != ID_literal)
    return false;

  const literalt lit = to_literal_expr(expr).get_literal();

  if(lit.is_constant())
    return false;

  // Build the SMT2 identifier for this literal, matching
  // what convert_literal() emits.
  std::string smt2_id = convert_identifier("B" + std::to_string(lit.var_no()));

  // The failed_assumptions set may contain quoted or unquoted
  // forms; check both.
  if(failed_assumptions.count(smt2_id))
    return !lit.sign();

  if(failed_assumptions.count(drop_quotes(smt2_id)))
    return !lit.sign();

  // Check the negated form for negated literals
  const std::string negated = "(not " + smt2_id + ")";
  if(failed_assumptions.count(negated))
    return lit.sign();

  const std::string negated_unquoted = "(not " + drop_quotes(smt2_id) + ")";
  if(failed_assumptions.count(negated_unquoted))
    return lit.sign();

  return false;
}

decision_proceduret::resultt smt2_dect::dec_solve(const exprt &assumption)
{
  ++number_of_solver_calls;

  temporary_filet temp_file_problem("smt2_dec_problem_", ""),
    temp_file_stdout("smt2_dec_stdout_", ""),
    temp_file_stderr("smt2_dec_stderr_", "");

  const auto write_problem_to_file = [&](std::ofstream problem_out) {
    if(assumption.is_not_nil())
      assumptions.push_back(convert(assumption));

    cached_output << stringstream.str();
    stringstream.str(std::string{});

    write_footer();

    if(assumption.is_not_nil())
      assumptions.pop_back();

    problem_out << cached_output.str() << stringstream.str();
    stringstream.str(std::string{});
  };

  write_problem_to_file(std::ofstream(
    temp_file_problem(), std::ios_base::out | std::ios_base::trunc));

  std::vector<std::string> argv;
  std::string stdin_filename;

  auto solver_binary_name = [this](const std::string &solver_name)
  {
    if(solver_binary_or_empty.empty())
      return solver_name;
    else
      return solver_binary_or_empty;
  };

  switch(solver)
  {
  case solvert::BITWUZLA:
    argv = {solver_binary_name("bitwuzla"), temp_file_problem()};
    break;

  case solvert::BOOLECTOR:
    argv = {
      solver_binary_name("boolector"), "--smt2", temp_file_problem(), "-m"};
    break;

  case solvert::CPROVER_SMT2:
    argv = {solver_binary_name("smt2_solver")};
    stdin_filename = temp_file_problem();
    break;

  case solvert::CVC5:
    argv = {
      solver_binary_name("cvc5"), "--lang", "smtlib", temp_file_problem()};
    break;

  case solvert::MATHSAT:
    // The options below were recommended by Alberto Griggio
    // on 10 July 2013

    argv = {
      solver_binary_name("mathsat"),
      "-input=smt2",
      "-preprocessor.toplevel_propagation=true",
      "-preprocessor.simplification=7",
      "-dpll.branching_random_frequency=0.01",
      "-dpll.branching_random_invalidate_phase_cache=true",
      "-dpll.restart_strategy=3",
      "-dpll.glucose_var_activity=true",
      "-dpll.glucose_learnt_minimization=true",
      "-theory.bv.eager=true",
      "-theory.bv.bit_blast_mode=1",
      "-theory.bv.delay_propagated_eqs=true",
      "-theory.fp.mode=1",
      "-theory.fp.bit_blast_mode=2",
      "-theory.arr.mode=1"};

    stdin_filename = temp_file_problem();
    break;

  case solvert::YICES:
    //    command = "yices -smt -e "   // Calling convention for older versions
    // Convention for 2.2.1
    argv = {solver_binary_name("yices-smt2"), temp_file_problem()};
    break;

  case solvert::Z3:
    argv = {solver_binary_name("z3"), "-smt2", temp_file_problem()};
    break;

  case solvert::GENERIC:
    PRECONDITION(!solver_binary_or_empty.empty());
    argv = {solver_binary_or_empty, temp_file_problem()};
    break;
  }

  int res =
    run(argv[0], argv, stdin_filename, temp_file_stdout(), temp_file_stderr());

  if(res<0)
  {
    messaget log{message_handler};
    log.error() << "error running SMT2 solver" << messaget::eom;
    return decision_proceduret::resultt::D_ERROR;
  }

  std::ifstream in(temp_file_stdout());
  return read_result(in);
}

decision_proceduret::resultt smt2_dect::read_result(std::istream &in)
{
  std::string line;
  decision_proceduret::resultt res=resultt::D_ERROR;

  boolean_assignment.clear();
  boolean_assignment.resize(no_boolean_variables, false);

  typedef std::unordered_map<irep_idt, irept> valuest;
  valuest parsed_values;

  while(in)
  {
    auto parsed_opt = smt2irep(in, message_handler);

    if(!parsed_opt.has_value())
      break;

    const auto &parsed = parsed_opt.value();

    if(parsed.id()=="sat")
      res=resultt::D_SATISFIABLE;
    else if(parsed.id()=="unsat")
      res=resultt::D_UNSATISFIABLE;
    else if(parsed.id() == "unknown")
    {
      messaget log{message_handler};
      log.error() << "SMT2 solver returned \"unknown\"" << messaget::eom;
      return decision_proceduret::resultt::D_ERROR;
    }
    else if(
      parsed.id().empty() && parsed.get_sub().size() == 1 &&
      parsed.get_sub().front().get_sub().size() == 2)
    {
      const irept &s0=parsed.get_sub().front().get_sub()[0];
      const irept &s1=parsed.get_sub().front().get_sub()[1];

      // Examples:
      // ( (B0 true) )
      // ( (|__CPROVER_pipe_count#1| (_ bv0 32)) )
      // ( (|some_integer| 0) )
      // ( (|some_integer| (- 10)) )

      parsed_values[s0.id()] = s1;
    }
    else if(
      parsed.id().empty() && parsed.get_sub().size() == 2 &&
      parsed.get_sub().front().id() == "error")
    {
      // We ignore errors after UNSAT because get-value after check-sat
      // returns unsat will give an error.
      if(res != resultt::D_UNSATISFIABLE)
      {
        const auto &message = id2string(parsed.get_sub()[1].id());
        messaget log{message_handler};
        log.error() << "SMT2 solver returned error message:\n"
                    << "\t" << messaget::quote_begin << message
                    << messaget::quote_end << messaget::eom;
        return decision_proceduret::resultt::D_ERROR;
      }
    }
    else if(parsed.id().empty() && !parsed.get_sub().empty())
    {
      // Check if this looks like an unsat-assumptions response:
      // a list of identifiers or (not identifier) forms.
      bool looks_like_assumptions = true;
      for(const auto &sub : parsed.get_sub())
      {
        if(sub.id().empty() && sub.get_sub().empty())
        {
          looks_like_assumptions = false;
          break;
        }
      }

      if(looks_like_assumptions)
      {
        for(const auto &sub : parsed.get_sub())
        {
          if(!sub.id().empty())
          {
            failed_assumptions.insert(id2string(sub.id()));
          }
          else if(sub.get_sub().size() == 2 && sub.get_sub()[0].id() == "not")
          {
            // Store as "(not name)" for negated literals
            failed_assumptions.insert(
              "(not " + id2string(sub.get_sub()[1].id()) + ")");
          }
        }
      }
    }
  }

  // If the result is not satisfiable don't bother updating the assignments and
  // values (since we didn't get any), just return.
  if(res != resultt::D_SATISFIABLE)
    return res;

  for(auto &assignment : identifier_map)
  {
    std::string conv_id = drop_quotes(convert_identifier(assignment.first));
    const irept &value = parsed_values[conv_id];
    assignment.second.value = parse_rec(value, assignment.second.type);
  }

  // Booleans
  for(unsigned v=0; v<no_boolean_variables; v++)
  {
    const std::string boolean_identifier =
      convert_identifier("B" + std::to_string(v));
      const auto found_parsed_value =
        parsed_values.find(drop_quotes(boolean_identifier));
      if(found_parsed_value != parsed_values.end())
      {
        const irept &value = found_parsed_value->second;

        if(value.id() != ID_true && value.id() != ID_false)
        {
          messaget log{message_handler};
          log.error() << "SMT2 solver returned non-constant value for variable "
                      << boolean_identifier << messaget::eom;
          return decision_proceduret::resultt::D_ERROR;
        }
        boolean_assignment[v] = value.id() == ID_true;
      }
      else
      {
        // Work out the value based on what set_to was called with.
        const auto found_set_value = set_values.find(boolean_identifier);
        if(found_set_value != set_values.end())
          boolean_assignment[v] = found_set_value->second;
        else
        {
          // Old code used the computation
          // const irept &value=values["B"+std::to_string(v)];
          // boolean_assignment[v]=(value.id()==ID_true);
          const irept &value = parsed_values[boolean_identifier];

          if(value.id() != ID_true && value.id() != ID_false)
          {
            messaget log{message_handler};
            log.error()
              << "SMT2 solver returned non-Boolean value for variable "
              << boolean_identifier << messaget::eom;
            return decision_proceduret::resultt::D_ERROR;
          }
          boolean_assignment[v] = value.id() == ID_true;
        }
      }
  }

  return res;
}

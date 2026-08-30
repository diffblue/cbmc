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

static std::string drop_quotes(std::string src)
{
  if(src.size() >= 2 && src.front() == '|' && src.back() == '|')
    return std::string(src, 1, src.size() - 2);
  else
    return src;
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
  }

  // If the result is not satisfiable don't bother updating the assignments and
  // values (since we didn't get any), just return.
  if(res != resultt::D_SATISFIABLE)
    return res;

  for(auto &identifier : identifier_map)
  {
    std::string conv_id = drop_quotes(convert_identifier(identifier.first));
    const irept &value = parsed_values[conv_id];
    value_map[identifier.first] = parse_rec(value, identifier.second.type);
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

void smt2_dect::print_assignment(std::ostream &os) const
{
  // Boolean stuff

  for(std::size_t v = 0; v < boolean_assignment.size(); v++)
      os << "b" << v << "=" << boolean_assignment[v] << "\n";

  // others
}

tvt smt2_dect::l_get(literalt l) const
{
  if(l.is_true())
      return tvt(true);
  if(l.is_false())
      return tvt(false);

  INVARIANT(
    l.var_no() < boolean_assignment.size(),
    "variable number shall be within bounds");
  return tvt(boolean_assignment[l.var_no()] ^ l.sign());
}

exprt smt2_dect::get(const exprt &expr) const
{
  if(expr.id() == ID_symbol)
  {
      const irep_idt &id = to_symbol_expr(expr).identifier();

      auto it = value_map.find(id);

      if(it != value_map.end())
        return it->second;
      else
        return expr;
  }
  else if(expr.id() == ID_nondet_symbol)
  {
      const irep_idt &id = to_nondet_symbol_expr(expr).get_identifier();

      auto it = value_map.find(id);

      if(it != value_map.end())
        return it->second;
  }
  else if(expr.id() == ID_literal)
  {
      auto l = to_literal_expr(expr).get_literal();
      if(l_get(l).is_true())
        return true_exprt();
      else
        return false_exprt();
  }
  else if(expr.id() == ID_not)
  {
      auto op = get(to_not_expr(expr).op());
      if(op == true)
        return false_exprt();
      else if(op == false)
        return true_exprt();
  }
  else if(
    expr.is_constant() || expr.id() == ID_empty_union ||
    (!expr.has_operands() && (expr.id() == ID_struct || expr.id() == ID_array)))
  {
      return expr;
  }
  else if(expr.has_operands())
  {
      exprt copy = expr;
      for(auto &op : copy.operands())
      {
        exprt eval_op = get(op);
        if(eval_op.is_nil())
          return nil_exprt{};
        op = std::move(eval_op);
      }
      return copy;
  }

  return nil_exprt();
}

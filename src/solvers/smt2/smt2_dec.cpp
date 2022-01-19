/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "smt2_dec.h"

#include <util/invariant.h>
#include <util/message.h>
#include <util/run.h>
#include <util/tempfile.h>

#include "smt2irep.h"

std::string smt2_dect::decision_procedure_text() const
{
  // clang-format off
  return "SMT2 " + logic + (use_FPA_theory ? " (with FPA)" : "") + " using " +
    (solver==solvert::GENERIC?"Generic":
     solver==solvert::BOOLECTOR?"Boolector":
     solver==solvert::CPROVER_SMT2?"CPROVER SMT2":
     solver==solvert::CVC3?"CVC3":
     solver==solvert::CVC4?"CVC4":
     solver==solvert::MATHSAT?"MathSAT":
     solver==solvert::YICES?"Yices":
     solver==solvert::Z3?"Z3":
     "(unknown)");
  // clang-format on
}

decision_proceduret::resultt smt2_dect::dec_solve()
{
  post_process();

  ++number_of_solver_calls;

  temporary_filet temp_file_problem("smt2_dec_problem_", ""),
    temp_file_stdout("smt2_dec_stdout_", ""),
    temp_file_stderr("smt2_dec_stderr_", "");

  const auto write_problem_to_file = [&](std::ofstream problem_out) {
    cached_output << stringstream.str();
    stringstream.str(std::string{});
    write_footer();
    problem_out << cached_output.str() << stringstream.str();
    stringstream.str(std::string{});
  };
  write_problem_to_file(std::ofstream(
    temp_file_problem(), std::ios_base::out | std::ios_base::trunc));

  std::vector<std::string> argv;
  std::string stdin_filename;

  switch(solver)
  {
  case solvert::BOOLECTOR:
    argv = {"boolector", "--smt2", temp_file_problem(), "-m"};
    break;

  case solvert::CPROVER_SMT2:
    argv = {"smt2_solver"};
    stdin_filename = temp_file_problem();
    break;

  case solvert::CVC3:
    argv = {"cvc3",
            "+model",
            "-lang",
            "smtlib",
            "-output-lang",
            "smtlib",
            temp_file_problem()};
    break;

  case solvert::CVC4:
    // The flags --bitblast=eager --bv-div-zero-const help but only
    // work for pure bit-vector formulas.
    argv = {"cvc4", "-L", "smt2", temp_file_problem()};
    break;

  case solvert::MATHSAT:
    // The options below were recommended by Alberto Griggio
    // on 10 July 2013

    argv = {"mathsat",
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
    argv = {"yices-smt2", temp_file_problem()};
    break;

  case solvert::Z3:
    argv = {"z3", "-smt2", temp_file_problem()};
    break;

  case solvert::GENERIC:
    UNREACHABLE;
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
        // Special case error handling
        if(
          solver == solvert::Z3 &&
          message.find("must not contain quantifiers") != std::string::npos)
        {
          // We tried to "(get-value |XXXX|)" where |XXXX| is determined to
          // include a quantified expression
          // Nothing to do, this should be caught and value assigned by the
          // set_to defaults later.
        }
        // Unhandled error, log the error and report it back up to caller
        else
        {
          messaget log{message_handler};
          log.error() << "SMT2 solver returned error message:\n"
                      << "\t\"" << message << "\"" << messaget::eom;
          return decision_proceduret::resultt::D_ERROR;
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
    std::string conv_id = convert_identifier(assignment.first);
    const irept &value = parsed_values[conv_id];
    assignment.second.value = parse_rec(value, assignment.second.type);
  }

  // Booleans
  for(unsigned v=0; v<no_boolean_variables; v++)
  {
    const std::string boolean_identifier = "B" + std::to_string(v);
    boolean_assignment[v] = [&]() {
      const auto found_parsed_value = parsed_values.find(boolean_identifier);
      if(found_parsed_value != parsed_values.end())
        return found_parsed_value->second.id() == ID_true;
      // Work out the value based on what set_to was called with.
      const auto found_set_value =
        set_values.find('|' + boolean_identifier + '|');
      if(found_set_value != set_values.end())
        return found_set_value->second;
      // Old code used the computation
      // const irept &value=values["B"+std::to_string(v)];
      // boolean_assignment[v]=(value.id()==ID_true);
      return parsed_values[boolean_identifier].id() == ID_true;
    }();
  }

  return res;
}

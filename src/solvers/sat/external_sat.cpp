/*******************************************************************\

Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.

\*******************************************************************/

#include "external_sat.h"

#include "dimacs_cnf.h"

#include <util/exception_utils.h>
#include <util/run.h>
#include <util/string_utils.h>
#include <util/tempfile.h>

#include <json/json_parser.h>

#include <chrono>
#include <cstdlib>
#include <fstream>
#include <random>
#include <sstream>
#include <string>
#include <thread>

class missing_configurationt : public cprover_exception_baset
{
public:
  missing_configurationt(std::string message) : _message(std::move(message))
  {
  }

  std::string what() const override
  {
    return _message;
  }

protected:
  std::string _message;
};

external_satt::external_satt(message_handlert &message_handler, std::string cmd)
  : cnf_clause_list_assignmentt(message_handler), _cmd(std::move(cmd))
{
}

const std::string external_satt::solver_text()
{
  return "External SAT solver";
}

bool external_satt::is_in_conflict(literalt) const
{
  UNIMPLEMENTED;
}

void external_satt::set_assignment(literalt, bool)
{
  UNIMPLEMENTED;
}

inline void external_satt::write_cnf_file(std::string cnf_file)
{
  log.status() << "Writing temporary CNF" << messaget::eom;
  std::ofstream out(cnf_file);

  // We start counting at 1, thus there is one variable fewer.
  out << "p cnf " << (no_variables() - 1) << ' ' << no_clauses() << '\n';

  for(auto &c : clauses)
    dimacs_cnft::write_dimacs_clause(c, out, false);

  out.close();
}

inline std::string external_satt::execute_solver(std::string cnf_file)
{
  log.status() << "Invoking SAT solver" << messaget::eom;
  std::ostringstream response_ostream;
  auto cmd_result = run(_cmd, {"", cnf_file}, "", response_ostream, "");

  log.status() << "Solver returned code: " << cmd_result << messaget::eom;
  return response_ostream.str();
}

inline external_satt::resultt
external_satt::parse_result(std::string solver_output)
{
  std::istringstream response_istream(solver_output);
  std::string line;
  external_satt::resultt result = resultt::P_ERROR;
  std::vector<bool> assigned_variables(no_variables(), false);
  while(getline(response_istream, line))
  {
    if(line[0] == 's')
    {
      auto parts = split_string(line, ' ');
      if(parts.size() < 2)
      {
        log.error() << "external SAT solver has provided an unexpected "
                       "response in results.\nUnexpected reponse: "
                    << line << messaget::eom;
        return resultt::P_ERROR;
      }

      auto status = parts[1];
      log.status() << "result:" << status << messaget::eom;
      if(status == "UNSATISFIABLE")
      {
        return resultt::P_UNSATISFIABLE;
      }
      if(status == "SATISFIABLE")
      {
        result = resultt::P_SATISFIABLE;
        assignment.insert(assignment.begin(), no_variables() - 1, tvt(false));
      }
      if(status == "TIMEOUT")
      {
        log.error() << "external SAT solver reports a timeout" << messaget::eom;
        return resultt::P_ERROR;
      }
    }

    if(line[0] == 'v' && result == resultt::P_SATISFIABLE)
    {
      auto assignments = split_string(line, ' ');

      // remove the first element which should be 'v' identifying
      // the line as the satisfying assignments
      assignments.erase(assignments.begin());
      auto number_of_variables = no_variables();
      for(auto &assignment_string : assignments)
      {
        try
        {
          signed long long as_long = std::stol(assignment_string);
          auto index = std::labs(as_long);

          if(index >= number_of_variables)
          {
            log.error() << "SAT assignment " << as_long
                        << " out of range of CBMC largest variable of "
                        << (number_of_variables - 1) << messaget::eom;
            return resultt::P_ERROR;
          }
          assignment[index] = tvt(as_long >= 0);
          assigned_variables[index] = true;
        }
        catch(...)
        {
          log.error() << "SAT assignment " << assignment_string
                      << " caused an exception while processing"
                      << messaget::eom;
          return resultt::P_ERROR;
        }
      }
      // Assignments can span multiple lines so returning early isn't an option
    }
  }

  if(result == resultt::P_SATISFIABLE)
  {
    // We don't need to check zero
    for(auto index = 1; index < no_variables(); index++)
    {
      if(!assigned_variables[index])
      {
        log.error() << "No assignment was found for literal: " << index
                    << messaget::eom;
        return resultt::P_ERROR;
      }
    }
    return resultt::P_SATISFIABLE;
  }

  log.error() << "external SAT solver has provided an unexpected response"
              << messaget::eom;
  return resultt::P_ERROR;
}

external_satt::resultt external_satt::do_prop_solve()
{
  // create a temporary file
  temporary_filet cnf_file("external-sat", ".cnf");
  write_cnf_file(cnf_file());
  auto output = execute_solver(cnf_file());
  return parse_result(output);
}

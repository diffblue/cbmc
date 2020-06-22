/*******************************************************************\

Module: Remote SAT

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "remote_sat.h"

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

remote_satt::remote_satt(message_handlert &message_handler)
  : cnf_clause_list_assignmentt(message_handler)
{
}

const std::string remote_satt::solver_text()
{
  return "SAT as a service";
}

bool remote_satt::is_in_conflict(literalt) const
{
  UNIMPLEMENTED;
}

void remote_satt::set_assignment(literalt, bool)
{
  UNIMPLEMENTED;
}

std::string random_file_name()
{
  static char alnum[] =
    "0123456789abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ";

  static std::mt19937 rg{std::random_device{}()};
  static std::uniform_int_distribution<std::string::size_type> pick(
    0, sizeof(alnum) - 2);

  std::string::size_type length = 10;
  std::string s;
  s.reserve(length);

  while(length--)
    s += alnum[pick(rg)];

  return s;
}

remote_satt::resultt remote_satt::do_prop_solve()
{
  // create a temporary file
  temporary_filet cnf_file("remote-sat", "cnf");

  std::ofstream out(cnf_file());

  // We start counting at 1, thus there is one variable fewer.
  out << "p cnf " << (no_variables() - 1) << ' ' << clauses.size() << '\n';

  for(auto &c : clauses)
    dimacs_cnft::write_dimacs_clause(c, out, false);

  out.close();

  // send that file into the configured bucket using the AWS CLI
  log.status() << "Uploading the CNF" << messaget::eom;

  const std::string bucket_env = "AWS_REMOTE_SAT_BUCKET";
  const std::string endpoint_env = "AWS_REMOTE_SAT_ENDPOINT";
  auto bucket = getenv(bucket_env.c_str());
  auto endpoint = getenv(endpoint_env.c_str());

  if(bucket == nullptr)
    throw missing_configurationt(
      "environment variable " + bucket_env + " is not set");

  if(endpoint == nullptr)
    throw missing_configurationt(
      "environment variable " + endpoint_env + " is not set");

  auto S3URI =
    "s3://" + std::string(bucket) + "/" + random_file_name() + ".cnf";

  auto cli_s3_result = run(
    "aws",
    {"aws", "s3", "cp", cnf_file(), S3URI, "--content-type", "text/plain"});

  // ok?
  if(cli_s3_result != 0)
    throw system_exceptiont("aws s3 command has failed");

  // now trigger the API
  log.status() << "Invoking the solver API" << messaget::eom;

  json_objectt query;
  query["s3_loc"] = json_stringt(S3URI);

  std::ostringstream query_stream;
  query_stream << query;

  std::ostringstream response_ostream;
  auto curl_result = run(
    "curl",
    {
      "curl",
      "--header",
      "Content-Type: application/json",
      "--request",
      "POST",
      "--data",
      query_stream.str(),
      endpoint,
    },
    "",
    response_ostream,
    "");

  // ok?
  if(curl_result != 0)
    throw system_exceptiont("curl has failed");

  // parse the JSON response
  std::istringstream response_istream(response_ostream.str());

  jsont response_json;
  if(parse_json(response_istream, "", log.get_message_handler(), response_json))
  {
    log.error() << "remote SAT checker has provided an ill-formed response: "
                   "json does not parse"
                << messaget::eom;
    return resultt::P_ERROR;
  }

  if(!response_json.is_object())
  {
    log.error() << "remote SAT checker has provided an ill-formed response: "
                   "expecting a json object"
                << messaget::eom;
    return resultt::P_ERROR;
  }

  // Is there a "message"?
  if(response_json["message"].value!="")
    log.status() << "Remote SAT message: " << response_json["message"].value << messaget::eom;

  // We get a "job_id" and a "status".
  // We may have to wait if the status is "PENDING"
  while(response_json["status"].value == "PENDING")
  {
    // unsatisfactory, should increase
    std::this_thread::sleep_for(std::chrono::seconds(1));

    const auto &job_id = response_json["job_id"].value;
    log.status() << "remote SAT is PENDING, job " << job_id << messaget::eom;

    auto curl_polling_result = run(
      "curl",
      {
        "curl",
        std::string(endpoint) + "/" + job_id,
      },
      "",
      response_ostream,
      "");

    // ok?
    if(curl_polling_result != 0)
      throw system_exceptiont("curl has failed");

    if(parse_json(
         response_istream, "", log.get_message_handler(), response_json))
    {
      log.error() << "remote SAT checker has provided an ill-formed response: "
                     "json does not parse"
                  << messaget::eom;
      return resultt::P_ERROR;
    }

    if(!response_json.is_object())
    {
      log.error() << "remote SAT checker has provided an ill-formed response: "
                     "expecting a json object"
                  << messaget::eom;
      return resultt::P_ERROR;
    }
  }

  const auto &status = response_json["status"].value;

  if(status == "UNSAT")
    return resultt::P_UNSATISFIABLE;
  else if(status == "SAT")
  {
    // collect satisfying assignment
    const auto &assignment_json = response_json["assignment"];

#if 0
    if(!assignment_json.is_array())
    {
      log.error() << "remote SAT checker has provided an ill-formed response"
                  << messaget::eom;
      return resultt::P_ERROR;
    }

    const auto &assignment_array = to_json_array(assignment_json);

    assignment.resize(no_variables() + 1, tvt::unknown());

    for(auto &element : assignment_array)
    {
      if(element.is_number())
      {
        try
        {
          signed long long as_long = std::stol(element.value);
          auto index = std::labs(as_long);

          if(index >= assignment.size())
            continue; // ignore for now

          assignment[index] = tvt(as_long >= 0);
        }
        catch(...)
        {
          // number does not parse
          CHECK_RETURN(false);
        }
      }
    }
#else
    auto assignments = split_string(assignment_json.value, ' ');
    for(auto &assignment_string : assignments)
    {
      try
      {
        signed long long as_long = std::stol(assignment_string);
        auto index = std::labs(as_long);

        if(index >= assignment.size())
          continue; // ignore for now

        assignment[index] = tvt(as_long >= 0);
      }
      catch(...)
      {
        // number does not parse
        CHECK_RETURN(false);
      }
    }
#endif

    return resultt::P_SATISFIABLE;
  }
  else if(status == "TIMEOUT")
  {
    log.error() << "remote SAT checker reports a timeout" << messaget::eom;
    return resultt::P_ERROR;
  }
  else
  {
    log.error() << "remote SAT checker has provided an unexpected response"
                << messaget::eom;
    return resultt::P_ERROR;
  }
}

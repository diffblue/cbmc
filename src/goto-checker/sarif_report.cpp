/*******************************************************************\

Module: SARIF Report

Author: Michael Tautschnig

\*******************************************************************/

/// \file
/// SARIF Report

#include "sarif_report.h"

#include <util/json.h>

void sarif_report(
  const propertiest &properties,
  const std::string &program,
  const std::string &version,
  std::ostream &out)
{
  json_objectt sarif;
  sarif["$schema"] =
    json_stringt("https://json.schemastore.org/sarif-2.1.0.json");
  sarif["version"] = json_stringt("2.1.0");

  json_arrayt runs;
  json_objectt run;

  // tool
  json_objectt driver;
  driver["name"] = json_stringt(program);
  driver["version"] = json_stringt(version);
  driver["informationUri"] =
    json_stringt("https://www.cprover.org/" + program + "/");
  json_objectt tool;
  tool["driver"] = std::move(driver);
  run["tool"] = std::move(tool);

  // results
  json_arrayt results;
  for(const auto &property_pair : properties)
  {
    results.push_back(sarif_result(property_pair.first, property_pair.second));
  }
  run["results"] = std::move(results);

  runs.push_back(std::move(run));
  sarif["runs"] = std::move(runs);

  out << sarif << '\n';
}

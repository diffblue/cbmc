/*******************************************************************\

Module: SARIF Report

Author: Michael Tautschnig

\*******************************************************************/

/// \file
/// SARIF Report

#include "sarif_report.h"

#include <util/cmdline.h>
#include <util/json.h>
#include <util/message.h>
#include <util/version.h>

#include <algorithm>
#include <cctype>
#include <iostream>
#include <map>

std::string sarif_uri(const std::string &file)
{
  if(file.empty() || file[0] == '<')
    return {};

  std::string path = file;
#ifdef _WIN32
  for(auto &c : path)
  {
    if(c == '\\')
      c = '/';
  }
  const bool absolute =
    path.size() >= 2 && path[1] == ':' && std::isalpha(path[0]);
#else
  const bool absolute = path[0] == '/';
#endif

  // RFC 3986: keep unreserved characters and the path separator, and
  // percent-encode all other bytes (including those of UTF-8 sequences)
  static const char hex[] = "0123456789ABCDEF";
  std::string encoded;
  for(const unsigned char c : path)
  {
    if(
      std::isalnum(c) || c == '-' || c == '.' || c == '_' || c == '~' ||
      c == '/' || (absolute && c == ':'))
    {
      encoded += static_cast<char>(c);
    }
    else
    {
      encoded += '%';
      encoded += hex[c >> 4];
      encoded += hex[c & 0xf];
    }
  }

  if(!absolute)
    return encoded;
#ifdef _WIN32
  return "file:///" + encoded;
#else
  return "file://" + encoded;
#endif
}

/// The property class of a property, such as "assertion" or "array bounds".
static std::string property_class(const property_infot &property_info)
{
  const irep_idt &property_class =
    property_info.pc->source_location().get_property_class();
  return property_class.empty() ? "property" : id2string(property_class);
}

/// The SARIF rule of a property: its property class, with spaces replaced
/// by underscores as in property ids (e.g. "array_bounds"), which is stable
/// across runs, unlike the property id.
static std::string sarif_rule_id(const property_infot &property_info)
{
  std::string rule_id = property_class(property_info);
  std::replace(rule_id.begin(), rule_id.end(), ' ', '_');
  return rule_id;
}

/// Convert a property and its status into a SARIF result.
static json_objectt sarif_result(
  const irep_idt &property_id,
  const property_infot &property_info,
  std::size_t rule_index)
{
  json_objectt result;

  // SARIF 2.1.0 3.27.9 and 3.27.10: only a result of kind "fail" has a
  // level other than "none" (the default); an inconclusive result is "open".
  std::string kind;
  switch(property_info.status)
  {
  case property_statust::FAIL:
    kind = "fail";
    result["level"] = json_stringt("error");
    break;
  case property_statust::ERROR:
  case property_statust::UNKNOWN:
    kind = "open";
    break;
  case property_statust::PASS:
    kind = "pass";
    break;
  case property_statust::NOT_REACHABLE:
  case property_statust::NOT_CHECKED:
    kind = "notApplicable";
    break;
  }

  result["ruleId"] = json_stringt(sarif_rule_id(property_info));
  result["ruleIndex"] = json_numbert(std::to_string(rule_index));
  result["kind"] = json_stringt(kind);

  json_objectt message;
  message["text"] = json_stringt(
    property_info.description + " (" + as_string(property_info.status) + ")");
  result["message"] = std::move(message);

  const auto &source_location = property_info.pc->source_location();
  json_objectt location;
  bool has_location = false;

  const std::string uri = sarif_uri(id2string(source_location.get_file()));
  if(!uri.empty())
  {
    json_objectt artifact_location;
    artifact_location["uri"] = json_stringt(uri);
    json_objectt physical_location;
    physical_location["artifactLocation"] = std::move(artifact_location);

    if(!source_location.get_line().empty())
    {
      json_objectt region;
      region["startLine"] = json_numbert(id2string(source_location.get_line()));
      if(!source_location.get_column().empty())
      {
        region["startColumn"] =
          json_numbert(id2string(source_location.get_column()));
      }
      physical_location["region"] = std::move(region);
    }

    location["physicalLocation"] = std::move(physical_location);
    has_location = true;
  }

  if(!source_location.get_function().empty())
  {
    json_objectt logical_location;
    logical_location["fullyQualifiedName"] =
      json_stringt(source_location.get_function());
    logical_location["kind"] = json_stringt("function");
    json_arrayt logical_locations;
    logical_locations.push_back(std::move(logical_location));
    location["logicalLocations"] = std::move(logical_locations);
    has_location = true;
  }

  if(has_location)
  {
    json_arrayt locations;
    locations.push_back(std::move(location));
    result["locations"] = std::move(locations);
  }

  json_objectt properties;
  properties["propertyId"] = json_stringt(property_id);
  result["properties"] = std::move(properties);

  return result;
}

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

  // one rule per property class, in order of first use
  std::map<std::string, std::size_t> rule_indices;
  json_arrayt rules;
  json_arrayt results;
  for(const auto &property_pair : properties)
  {
    const std::string rule_id = sarif_rule_id(property_pair.second);
    auto entry = rule_indices.emplace(rule_id, rule_indices.size());
    if(entry.second)
    {
      json_objectt rule;
      rule["id"] = json_stringt(rule_id);
      json_objectt short_description;
      short_description["text"] =
        json_stringt(property_class(property_pair.second));
      rule["shortDescription"] = std::move(short_description);
      rules.push_back(std::move(rule));
    }
    results.push_back(sarif_result(
      property_pair.first, property_pair.second, entry.first->second));
  }

  json_objectt driver;
  driver["name"] = json_stringt(program);
  driver["version"] = json_stringt(version);
  driver["informationUri"] =
    json_stringt("https://www.cprover.org/" + program + "/");
  driver["rules"] = std::move(rules);
  json_objectt tool;
  tool["driver"] = std::move(driver);

  json_objectt run;
  run["tool"] = std::move(tool);
  run["results"] = std::move(results);

  json_arrayt runs;
  runs.push_back(std::move(run));
  sarif["runs"] = std::move(runs);

  out << sarif << '\n';
}

sarif_outputt::sarif_outputt(
  const cmdlinet &cmdline,
  const std::string &program,
  message_handlert &message_handler)
  : program(program), message_handler(message_handler)
{
  if(cmdline.isset("sarif-result"))
    filename = cmdline.get_value("sarif-result");
}

sarif_outputt::~sarif_outputt()
{
  if(enabled() && !written)
  {
    messaget log{message_handler};
    log.warning() << "no verification results were computed, so none were "
                     "written in SARIF format"
                  << messaget::eom;
  }
}

bool sarif_outputt::open()
{
  if(!enabled() || to_stdout())
    return true;

  file.open(filename);
  if(!file)
  {
    messaget log{message_handler};
    log.error() << "failed to open SARIF output file: " << filename
                << messaget::eom;
    return false;
  }
  return true;
}

bool sarif_outputt::write(const propertiest &properties)
{
  if(!enabled())
    return true;

  written = true;
  std::ostream &out = to_stdout() ? std::cout : file;
  sarif_report(properties, program, CBMC_VERSION, out);
  out.flush();
  if(!out)
  {
    messaget log{message_handler};
    log.error() << "failed to write SARIF output file: " << filename
                << messaget::eom;
    return false;
  }
  return true;
}

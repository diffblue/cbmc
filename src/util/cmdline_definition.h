/*******************************************************************\

Module: Command line parsing

Author: Peter Schrammel

\*******************************************************************/

// \file Command line options definition

#ifndef CPROVER_UTIL_CMDLINE_DEFINITION_H
#define CPROVER_UTIL_CMDLINE_DEFINITION_H

#include <list>
#include <string>
#include <vector>

#include "optional.h"

class json_arrayt;
class xmlt;

struct cmdline_optiont
{
  struct argumentt
  {
    argumentt(std::string name, std::string type);

    std::string name;
    std::string type;
  };

  typedef std::string deprecatedt;

  cmdline_optiont(
    std::string name,
    optionalt<argumentt> argument,
    std::string help_text,
    std::string option_group,
    optionalt<deprecatedt> deprecated);

  std::string name;
  optionalt<argumentt> argument;
  std::string help_text;
  std::string option_group;
  optionalt<deprecatedt> deprecated;
};

class cmdline_definitiont
{
public:
  explicit cmdline_definitiont(
    std::initializer_list<cmdline_optiont> &&initializer_list);

  void concat(const cmdline_definitiont &other);

  std::string
  to_help_text(std::size_t option_width, std::size_t total_width) const;
  std::string to_option_string() const;
  json_arrayt to_json() const;
  xmlt to_xml() const;

private:
  std::vector<cmdline_optiont> cmdline_options;
};

cmdline_definitiont
operator+(cmdline_definitiont first, const cmdline_definitiont &second);

#endif // CPROVER_UTIL_CMDLINE_DEFINITION_H

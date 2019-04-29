/*******************************************************************\

Module: Name mangling

Author: Kareem Khazem <karkhaz@karkhaz.com>, 2019

\*******************************************************************/

#include "name_mangler.h"

#include <util/get_base_name.h>

#include <iomanip>
#include <sstream>

irep_idt file_name_manglert::
operator()(const symbolt &src, const std::string &extra_info)
{
  std::string basename = get_base_name(src.location.get_file().c_str(), false);

  std::stringstream ss;
  ss << CPROVER_PREFIX << "file_local_";
  ss << std::regex_replace(
          std::regex_replace(basename, forbidden, "_"), multi_under, "_")
     << "_";

  if(extra_info != "")
    ss << extra_info << "_";
  ss << src.name;
  return irep_idt(ss.str());
}

irep_idt djb_manglert::
operator()(const symbolt &src, const std::string &extra_info)
{
  char const *str = src.location.get_working_directory().c_str();
  unsigned long hash = 5381;
  int c;
  while((c = *str++))
    hash = ((hash << 5) + hash) + c;

  uint32_t eight_nibble_hash = (uint32_t)hash;

  std::stringstream ss;
  ss << CPROVER_PREFIX << "file_local_" << std::setfill('0') << std::setw(8)
     << std::hex << eight_nibble_hash << "_" << extra_info << "_" << src.name;
  return irep_idt(ss.str());
}

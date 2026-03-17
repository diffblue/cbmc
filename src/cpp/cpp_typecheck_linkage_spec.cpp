/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/// \file
/// C++ Language Type Checking

#include <util/message.h>

#include "cpp_typecheck.h"

void cpp_typecheckt::convert(cpp_linkage_spect &linkage_spec)
{
  irep_idt old_linkage_spec=current_linkage_spec;

  current_linkage_spec=linkage_spec.linkage().get(ID_value);

  // there is a linkage spec "C++", which we know as "cpp"
  if(current_linkage_spec=="C++")
    current_linkage_spec=ID_cpp;

  // do the declarations
  for(cpp_linkage_spect::itemst::iterator
      it=linkage_spec.items().begin();
      it!=linkage_spec.items().end();
      it++)
  {
    const auto &loc = it->source_location();
    std::string file = id2string(loc.get_file());
    if(file.empty())
      file = id2string(linkage_spec.source_location().get_file());
    bool is_system =
      file.find("/usr/include/") == 0 || file.find("/usr/lib/") == 0;

    if(is_system)
    {
      null_message_handlert null_mh;
      message_handlert &old_mh = get_message_handler();
      set_message_handler(null_mh);
      try
      {
        convert(*it);
      }
      catch(int)
      {
      }
      set_message_handler(old_mh);
    }
    else
    {
      convert(*it);
    }
  }

  // back to previous linkage spec
  current_linkage_spec=old_linkage_spec;
}

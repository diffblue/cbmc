/*******************************************************************\

Module: Alignment Checks

Author:

\*******************************************************************/

/// \file
/// Alignment Checks

#include "alignment_checks.h"

#include <util/pointer_offset_size.h>
#include <util/config.h>
#include <util/symbol_table.h>

void print_struct_alignment_problems(
  const symbol_tablet &symbol_table,
  std::ostream &out)
{
  forall_symbols(it, symbol_table.symbols)
    if(it->second.is_type && it->second.type.id()==ID_struct)
    {
      const struct_typet &str=to_struct_type(it->second.type);
      const struct_typet::componentst &components=str.components();

      bool first_time_seen_in_struct=true;

      for(struct_typet::componentst::const_iterator
          it_mem=components.begin();
          it_mem!=components.end();
          it_mem++)
      {
        mp_integer cumulated_length=0;
        bool first_time_seen_from=true;

        // if the instruction cannot be aligned to the address,
        // try the next one

        if(it_mem->get_is_padding())
          // || alignment(it_mem->type())%config.ansi_c.alignment!=0)
          continue;

        for(struct_typet::componentst::const_iterator
            it_next=it_mem;
            it_next!=components.end();
            it_next++)
        {
          const typet &it_type=it_next->type();
          const namespacet ns(symbol_table);
          mp_integer size=pointer_offset_size(it_type, ns);

          if(size<0)
            throw "type of unknown size:\n"+it_type.pretty();

          cumulated_length+=size;
          // [it_mem;it_next] cannot be covered by an instruction
          if(cumulated_length>config.ansi_c.memory_operand_size)
          {
            // if interferences have been found, no need to check with
            // starting from an already covered member
            if(!first_time_seen_from)
              it_mem=it_next-1;
            break;
          }

          if(it_mem!=it_next && !it_next->get_is_padding())
          {
            if(first_time_seen_in_struct)
            {
              first_time_seen_in_struct=false;
              first_time_seen_from=false;

              out << "\nWARNING: "
                  << "declaration of structure "
                  << str.find_type(ID_tag).pretty()
                  << " at " << it->second.location << '\n';
            }

            out << "members " << it_mem->get_pretty_name() << " and "
                << it_next->get_pretty_name() << " might interfere\n";
          }
        }
      }
    }
    else if(it->second.type.id()==ID_array)
    {
      // is this structure likely to introduce data races?
      #if 0
      const namespacet ns(symbol_table);
      const array_typet array=to_array_type(it->second.type);
      const mp_integer size=
        pointer_offset_size(array.subtype(), ns);

      if(size<0)
        throw "type of unknown size:\n"+it_type.pretty();

      if(2*integer2long(size)<=config.ansi_c.memory_operand_size)
      {
        out << "\nWARNING: "
            << "declaration of an array at "
            << it->second.location <<
            << "\nmight be concurrently accessed\n";
      }
      #endif
    }
}

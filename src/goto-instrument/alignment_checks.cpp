/*******************************************************************\

Module: Alignment Checks

Author:

\*******************************************************************/

#include <pointer_offset_size.h>
#include <config.h>
#include <context.h>

#include "alignment_checks.h"

/*******************************************************************\

Function: print_struct_alignment_problems

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void print_struct_alignment_problems(
  const contextt &context,
  std::ostream &out)
{
  forall_symbols(it, context.symbols)
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
          const namespacet ns(context);
          mp_integer size=pointer_offset_size(ns, it_type);

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

              out << std::endl
                  << "WARNING: "
                  << "declaration of structure "
                  << str.find_type(ID_tag).pretty()
                  << " at " << it->second.location << std::endl;
            }

            out << "members " << it_mem->get_pretty_name() << " and "
                << it_next->get_pretty_name() << " might interfere"
                << std::endl;
          }
        }
      }
    }
    else if(it->second.type.id()==ID_array)
    {
      // is this structure likely to introduce dataraces?
      #if 0
      const namespacet ns(context);
      const array_typet array=to_array_type(it->second.type);
      const mp_integer size=
        pointer_offset_size(ns, array.subtype());       

      if(2*integer2long(size)<=config.ansi_c.memory_operand_size)
      {
        out << std::endl << "WARNING: " 
            << "declaration of an array at "
            << it->second.location << std::endl
            << "might be concurrently accessed" << std::endl;
      }
      #endif
    }
}

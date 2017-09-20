#include "store_goto_location.h"

#include <goto-programs/goto_program.h>
#include <util/source_location.h>

void store_goto_locations(goto_programt &goto_program)
{
    for(auto it=goto_program.instructions.begin();
        it!=goto_program.instructions.end();
        it++)
    {
      auto &source_location=it->source_location;
      auto location_number=it->location_number;

      source_location.set_goto_location(location_number);
    }
}

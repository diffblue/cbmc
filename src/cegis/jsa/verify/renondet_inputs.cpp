/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <cegis/cegis-util/program_helper.h>

#include <cegis/jsa/options/jsa_program.h>
#include <cegis/jsa/instrument/jsa_meta_data.h>
#include <cegis/jsa/preprocessing/clone_heap.h>
#include <cegis/jsa/verify/renondet_inputs.h>

void assume_renondet_inputs_valid(jsa_programt &prog)
{
  if (prog.counterexample_locations.empty()) return;
  const symbol_tablet &st=prog.st;
  goto_programt &body=get_entry_body(prog.gf);

  for (const goto_programt::targett &pos : prog.inductive_step_renondets)
  {
    const irep_idt &id=get_affected_variable(*pos);
    const symbol_exprt lhs(st.lookup(id).symbol_expr());
    const typet &type=lhs.type();
    if (is_jsa_heap(type))
      assume_valid_heap(st, body, pos, address_of_exprt(lhs));
  }
}

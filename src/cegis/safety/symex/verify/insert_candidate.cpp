/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <cegis/cegis-util/program_helper.h>
#include <cegis/instrument/meta_variables.h>
#include <cegis/invariant/util/invariant_program_helper.h>
#include <cegis/invariant/symex/verify/insert_program.h>
#include <cegis/safety/meta/meta_variable_names.h>
#include <cegis/safety/options/safety_program.h>
#include <cegis/safety/symex/verify/insert_candidate.h>

void safety_insert_candidate(safety_programt &program,
    const safety_goto_solutiont &candidate)
{
  if(candidate.empty()) return;
  const safety_programt::safety_loopst &loops=program.safety_loops;
  const size_t size=loops.size();
  assert(size == candidate.size());
  goto_programt &body=get_entry_body(program.gf);
  const std::string Ix_0(get_cegis_meta_name(get_Ix(0)));
  const std::string Ix0(get_cegis_meta_name(get_Ix0()));
  insert_program(body, program.Ix0, candidate.front(), Ix_0, Ix0);
  for(size_t i=0; i < size; ++i)
  {
    const invariant_programt::invariant_loopt &loop=loops[i];
    const goto_programt::instructionst &prog=candidate[i];
    const invariant_programt::meta_vars_positionst &meta=loop.meta_variables;
    insert_program(body, meta.Ix, prog);
    const std::string Ix(get_cegis_meta_name(get_Ix(i)));
    const std::string Ix_prime(get_cegis_meta_name(get_Ix_prime(i)));
    insert_program(body, meta.Ix_prime, prog, Ix, Ix_prime);
  }
}

/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <util/arith_tools.h>

#include <cegis/cegis-util/program_helper.h>

#include <cegis/jsa/value/jsa_types.h>
#include <cegis/jsa/options/jsa_program.h>
#include <cegis/jsa/instrument/jsa_meta_data.h>
#include <cegis/jsa/preprocessing/add_constraint_meta_variables.h>
#include <cegis/jsa/preprocessing/create_temp_variables.h>

void create_jsa_temp_variables(jsa_programt &prog, const size_t max_size)
{
  goto_programt::targett pos=prog.synthetic_variables;
  symbol_tablet &st=prog.st;
  goto_functionst &gf=prog.gf;
  goto_programt &body=get_entry_body(gf);
  const std::string tmp_prefix(JSA_TMP_PREFIX);
  const typet type(jsa_word_type());
  for(size_t i=0; i < max_size; ++i)
  {
    pos=body.insert_after(pos);
    const std::string base_name(tmp_prefix + std::to_string(i));
    declare_jsa_meta_variable(st, pos, base_name, type);
    pos=assign_jsa_meta_variable(st, gf, pos, base_name, from_integer(0, type));
  }
  prog.synthetic_variables=pos;
}

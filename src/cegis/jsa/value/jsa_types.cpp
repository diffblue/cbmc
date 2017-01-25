/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <ansi-c/c_types.h>

#include <cegis/jsa/instrument/jsa_meta_data.h>
#include <cegis/jsa/value/jsa_types.h>

typet jsa_word_type()
{
  return unsigned_char_type();
}

typet jsa_internal_index_type()
{
  return jsa_word_type();
}

typet jsa_iterator_id_type()
{
  return jsa_word_type();
}

#define PRED_INSTR_TYPE "tag-__CPROVER_jsa_pred_instruction"
symbol_typet jsa_predicate_instruction_type()
{
  return symbol_typet(PRED_INSTR_TYPE);
}

array_typet jsa_predicate_type(const exprt &size)
{
  return array_typet(jsa_predicate_instruction_type(), size);
}

#define INV_INSTR_TYPE "tag-__CPROVER_jsa_invariant_instruction"
symbol_typet jsa_invariant_instruction_type()
{
  return symbol_typet(INV_INSTR_TYPE);
}

array_typet jsa_invariant_type(const exprt & size)
{
  return array_typet(jsa_invariant_instruction_type(), size);
}

#define QUERY_INSTR_TYPE "tag-__CPROVER_jsa_query_instruction"
symbol_typet jsa_query_instruction_type()
{
  return symbol_typet(QUERY_INSTR_TYPE);
}

array_typet jsa_query_type(const exprt &size)
{
  return array_typet(jsa_query_instruction_type(), size);
}

symbol_typet jsa_heap_type()
{
  return symbol_typet(JSA_HEAP_TAG);
}

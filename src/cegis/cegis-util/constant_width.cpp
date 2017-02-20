/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <util/std_expr.h>

#include "constant_width.h"

// TODO: Consider min word width to be size of character.
#define MIN_WORD_WIDTH 2u

size_t get_min_word_width(const exprt &expr)
{
  assert(ID_constant == expr.id());
  const std::string &value=id2string(to_constant_expr(expr).get_value());
  if(value.empty()) return MIN_WORD_WIDTH;
  const bool is_neg_if_signed=value[0] == '1';
  std::string::size_type first_sb=value.find(is_neg_if_signed ? '0' : '1');
  if(std::string::npos == first_sb) return MIN_WORD_WIDTH;
  const size_t value_width=value.size() - first_sb + 1;
  // TODO: Make more flexible for other word widths
  if(value_width > 16u) return value.size();
  if(value_width > 8u) return 16u;
  if(value_width > 4u) return 8u;
  if(value_width > 2u) return 4u;
  return MIN_WORD_WIDTH;
}

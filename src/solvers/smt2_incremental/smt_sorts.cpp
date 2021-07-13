// Author: Diffblue Ltd.

#include "smt_sorts.h"

#include <util/invariant.h>

// Define the irep_idts for sorts.
#define SORT_ID(the_id)                                                        \
  const irep_idt ID_smt_##the_id##_sort{"smt_" #the_id "_sort"};
#include <solvers/smt2_incremental/smt_sorts.def>
#undef SORT_ID

smt_bool_sortt::smt_bool_sortt() : smt_sortt{ID_smt_bool_sort}
{
}

smt_bit_vector_sortt::smt_bit_vector_sortt(const std::size_t bit_width)
  : smt_sortt{ID_smt_bit_vector_sort}
{
  set_size_t(ID_width, bit_width);
}

std::size_t smt_bit_vector_sortt::bit_width() const
{
  return get_size_t(ID_width);
}

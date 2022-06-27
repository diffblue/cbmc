// Author: Diffblue Ltd.

#include "smt_sorts.h"

#include <util/invariant.h>

// Define the irep_idts for sorts.
#define SORT_ID(the_id)                                                        \
  const irep_idt ID_smt_##the_id##_sort{"smt_" #the_id "_sort"};
#include <solvers/smt2_incremental/smt_sorts.def>
#undef SORT_ID

#define SORT_ID(the_id)                                                        \
  template <>                                                                  \
  const smt_##the_id##_sortt *smt_sortt::cast<smt_##the_id##_sortt>() const &  \
  {                                                                            \
    return id() == ID_smt_##the_id##_sort                                      \
             ? static_cast<const smt_##the_id##_sortt *>(this)                 \
             : nullptr;                                                        \
  }
#include <solvers/smt2_incremental/smt_sorts.def> // NOLINT(build/include)
#undef SORT_ID

#define SORT_ID(the_id)                                                        \
  template <>                                                                  \
  optionalt<smt_##the_id##_sortt> smt_sortt::cast<smt_##the_id##_sortt>() &&   \
  {                                                                            \
    if(id() == ID_smt_##the_id##_sort)                                         \
      return {std::move(*static_cast<const smt_##the_id##_sortt *>(this))};    \
    else                                                                       \
      return {};                                                               \
  }
#include <solvers/smt2_incremental/smt_sorts.def> // NOLINT(build/include)
#undef SORT_ID

bool smt_sortt::operator==(const smt_sortt &other) const
{
  return irept::operator==(other);
}

bool smt_sortt::operator!=(const smt_sortt &other) const
{
  return !(*this == other);
}

smt_bool_sortt::smt_bool_sortt() : smt_sortt{ID_smt_bool_sort}
{
}

smt_bit_vector_sortt::smt_bit_vector_sortt(const std::size_t bit_width)
  : smt_sortt{ID_smt_bit_vector_sort}
{
  INVARIANT(
    bit_width > 0,
    "The definition of SMT2 bit vector theory requires the number of "
    "bits to be greater than 0.");
  set_size_t(ID_width, bit_width);
}

std::size_t smt_bit_vector_sortt::bit_width() const
{
  return get_size_t(ID_width);
}

smt_array_sortt::smt_array_sortt(
  const smt_sortt &index_sort,
  const smt_sortt &element_sort)
  : smt_sortt{ID_smt_array_sort}
{
  add(ID_index, index_sort);
  add(ID_value, element_sort);
}

const smt_sortt &smt_array_sortt::index_sort() const
{
  return static_cast<const smt_sortt &>(find(ID_index));
}

const smt_sortt &smt_array_sortt::element_sort() const
{
  return static_cast<const smt_sortt &>(find(ID_value));
}

template <typename visitort>
void accept(const smt_sortt &sort, const irep_idt &id, visitort &&visitor)
{
#define SORT_ID(the_id)                                                        \
  if(id == ID_smt_##the_id##_sort)                                             \
    return visitor.visit(static_cast<const smt_##the_id##_sortt &>(sort));
#include "smt_sorts.def"
#undef SORT_ID
  UNREACHABLE;
}

void smt_sortt::accept(smt_sort_const_downcast_visitort &visitor) const
{
  ::accept(*this, id(), visitor);
}

void smt_sortt::accept(smt_sort_const_downcast_visitort &&visitor) const
{
  ::accept(*this, id(), std::move(visitor));
}

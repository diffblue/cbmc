// Author: Diffblue Ltd.

/// \file
/// Data structure for smt sorts.
/// \note All classes derived from `smt_sortt`, must be listed in smt_sorts.def.

#ifndef CPROVER_SOLVERS_SMT2_INCREMENTAL_SMT_SORTS_H
#define CPROVER_SOLVERS_SMT2_INCREMENTAL_SMT_SORTS_H

#include <util/irep.h>

class smt_sort_const_downcast_visitort;

class smt_sortt : protected irept
{
public:
  // smt_sortt does not support the notion of an empty / null state. Use
  // optionalt<smt_sortt> instead if an empty sort is required.
  smt_sortt() = delete;

  using irept::pretty;

  bool operator==(const smt_sortt &) const;
  bool operator!=(const smt_sortt &) const;

  void accept(smt_sort_const_downcast_visitort &) const;
  void accept(smt_sort_const_downcast_visitort &&) const;

protected:
  using irept::irept;
};

class smt_bool_sortt final : public smt_sortt
{
public:
  smt_bool_sortt();
};

class smt_bit_vector_sortt final : public smt_sortt
{
public:
  explicit smt_bit_vector_sortt(std::size_t bit_width);
  std::size_t bit_width() const;
};

class smt_sort_const_downcast_visitort
{
public:
#define SORT_ID(the_id) virtual void visit(const smt_##the_id##_sortt &) = 0;
#include "smt_sorts.def"
#undef SORT_ID
};

#endif // CPROVER_SOLVERS_SMT2_INCREMENTAL_SMT_SORTS_H

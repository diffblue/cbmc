// Author: Diffblue Ltd.

/// \file
/// Data structure for smt sorts.
/// \note All classes derived from `smt_sortt`, must be listed in smt_sorts.def.

#ifndef CPROVER_SOLVERS_SMT2_INCREMENTAL_SMT_SORTS_H
#define CPROVER_SOLVERS_SMT2_INCREMENTAL_SMT_SORTS_H

#include <util/irep.h>
#include <util/optional.h>

#include <type_traits>

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

  /// \brief Class for adding the ability to up and down cast smt_sortt to and
  ///   from irept. These casts are required by other irept derived classes in
  ///   order to store instances of smt_sortt inside them.
  /// \tparam derivedt The type of class which derives from this class and from
  ///   irept.
  template <typename derivedt>
  class storert
  {
  protected:
    storert();
    static irept upcast(smt_sortt sort);
    static const smt_sortt &downcast(const irept &);
  };

  template <typename sub_classt>
  const sub_classt *cast() const &;

  template <typename sub_classt>
  optionalt<sub_classt> cast() &&;

protected:
  using irept::irept;
};

template <typename derivedt>
smt_sortt::storert<derivedt>::storert()
{
  static_assert(
    std::is_base_of<irept, derivedt>::value &&
      std::is_base_of<storert<derivedt>, derivedt>::value,
    "Only irept based classes need to upcast smt_sortt to store it.");
}

template <typename derivedt>
irept smt_sortt::storert<derivedt>::upcast(smt_sortt sort)
{
  return static_cast<irept &&>(std::move(sort));
}

template <typename derivedt>
const smt_sortt &smt_sortt::storert<derivedt>::downcast(const irept &irep)
{
  return static_cast<const smt_sortt &>(irep);
}

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

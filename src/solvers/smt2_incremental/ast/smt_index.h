// Author: Diffblue Ltd.

#ifndef CPROVER_SOLVERS_SMT2_INCREMENTAL_SMT_INDEX_H
#define CPROVER_SOLVERS_SMT2_INCREMENTAL_SMT_INDEX_H

#include <util/irep.h>

class smt_index_const_downcast_visitort;

/// \brief
/// For implementation of indexed identifiers. See SMT-LIB Standard Version 2.6
/// section 3.3.
class smt_indext : protected irept
{
public:
  // smt_indext does not support the notion of an empty / null state. Use
  // optionalt<smt_indext> instead if an empty index is required.
  smt_indext() = delete;

  using irept::pretty;

  bool operator==(const smt_indext &) const;
  bool operator!=(const smt_indext &) const;

  template <typename sub_classt>
  const sub_classt *cast() const &;

  void accept(smt_index_const_downcast_visitort &) const;

  /// \brief Class for adding the ability to up and down cast smt_indext to and
  ///   from irept. These casts are required by other irept derived classes in
  ///   order to store instances of smt_termt inside them.
  /// \tparam derivedt The type of class which derives from this class and from
  ///   irept.
  template <typename derivedt>
  class storert
  {
  protected:
    storert();
    static irept upcast(smt_indext index);
    static const smt_indext &downcast(const irept &);
  };

protected:
  using irept::irept;
};

template <typename derivedt>
smt_indext::storert<derivedt>::storert()
{
  static_assert(
    std::is_base_of<irept, derivedt>::value &&
      std::is_base_of<storert<derivedt>, derivedt>::value,
    "Only irept based classes need to upcast smt_sortt to store it.");
}

template <typename derivedt>
irept smt_indext::storert<derivedt>::upcast(smt_indext index)
{
  return static_cast<irept &&>(std::move(index));
}

template <typename derivedt>
const smt_indext &smt_indext::storert<derivedt>::downcast(const irept &irep)
{
  return static_cast<const smt_indext &>(irep);
}

class smt_numeral_indext : public smt_indext
{
public:
  explicit smt_numeral_indext(std::size_t value);
  std::size_t value() const;
};

class smt_symbol_indext : public smt_indext
{
public:
  explicit smt_symbol_indext(irep_idt identifier);
  irep_idt identifier() const;
};

class smt_index_const_downcast_visitort
{
public:
  virtual void visit(const smt_numeral_indext &) = 0;
  virtual void visit(const smt_symbol_indext &) = 0;
};

#endif // CPROVER_SOLVERS_SMT2_INCREMENTAL_SMT_INDEX_H

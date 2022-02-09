// Author: Diffblue Ltd.

#ifndef CPROVER_SOLVERS_SMT2_INCREMENTAL_SMT_TERMS_H
#define CPROVER_SOLVERS_SMT2_INCREMENTAL_SMT_TERMS_H

#include <util/irep.h>

#include <solvers/smt2_incremental/smt_index.h>
#include <solvers/smt2_incremental/smt_sorts.h>

#include <functional>

class BigInt;
using mp_integer = BigInt;

class smt_term_const_downcast_visitort;
class smt_termt : protected irept, private smt_sortt::storert<smt_termt>
{
public:
  // smt_termt does not support the notion of an empty / null state. Use
  // optionalt<smt_termt> instead if an empty term is required.
  smt_termt() = delete;

  using irept::pretty;

  bool operator==(const smt_termt &) const;
  bool operator!=(const smt_termt &) const;

  const smt_sortt &get_sort() const;

  void accept(smt_term_const_downcast_visitort &) const;
  void accept(smt_term_const_downcast_visitort &&) const;

  /// \brief Class for adding the ability to up and down cast smt_termt to and
  ///   from irept. These casts are required by other irept derived classes in
  ///   order to store instances of smt_termt inside them.
  /// \tparam derivedt The type of class which derives from this class and from
  ///   irept.
  template <typename derivedt>
  class storert
  {
  protected:
    storert();
    static irept upcast(smt_termt term);
    static const smt_termt &downcast(const irept &);
  };

protected:
  smt_termt(irep_idt id, smt_sortt sort);
};

template <typename derivedt>
smt_termt::storert<derivedt>::storert()
{
  static_assert(
    std::is_base_of<irept, derivedt>::value &&
      std::is_base_of<storert<derivedt>, derivedt>::value,
    "Only irept based classes need to upcast smt_termt to store it.");
}

template <typename derivedt>
irept smt_termt::storert<derivedt>::upcast(smt_termt term)
{
  return static_cast<irept &&>(std::move(term));
}

template <typename derivedt>
const smt_termt &smt_termt::storert<derivedt>::downcast(const irept &irep)
{
  return static_cast<const smt_termt &>(irep);
}

class smt_bool_literal_termt : public smt_termt
{
public:
  explicit smt_bool_literal_termt(bool value);
  bool value() const;
};

/// Stores identifiers in unescaped and unquoted form. Any escaping or quoting
/// required should be performed during printing.
/// \details
/// The SMT-LIB standard Version 2.6 refers to "indexed" identifiers which have
/// 1 or more indices and "simple" identifiers which have no indicies. The
/// internal `smt_identifier_termt` class is used for both kinds of identifier
/// which are distinguished based on whether the collection of `indices` is
/// empty or not.
class smt_identifier_termt : public smt_termt,
                             private smt_indext::storert<smt_identifier_termt>
{
public:
  /// \brief Constructs an identifier term with the given \p identifier and
  ///   \p sort.
  /// \param identifier: This should be the unescaped form of the identifier.
  ///   Escaping of the identifier if required is to be performed as part of the
  ///   printing operation. The given identifier is checked to ensure that it
  ///   has not already been escaped, in order to avoid escaping it twice.
  ///   Performing escaping during the printing will ensure that the identifiers
  ///   output conform to the specification of the concrete form.
  /// \param sort: The sort which this term will have. All terms in our abstract
  ///   form must be sorted, even if those sorts are not printed in all
  ///   contexts.
  /// \param indices: This should be collection of indices for an indexed
  ///   identifier, or an empty collection for simple (non-indexed) identifiers.
  smt_identifier_termt(
    irep_idt identifier,
    smt_sortt sort,
    std::vector<smt_indext> indices = {});
  irep_idt identifier() const;
  std::vector<std::reference_wrapper<const smt_indext>> indices() const;
};

class smt_bit_vector_constant_termt : public smt_termt
{
public:
  smt_bit_vector_constant_termt(const mp_integer &value, smt_bit_vector_sortt);
  smt_bit_vector_constant_termt(const mp_integer &value, std::size_t bit_width);
  mp_integer value() const;

  // This deliberately hides smt_termt::get_sort, because bit_vector terms
  // always have bit_vector sorts. The same sort data is returned for both
  // functions either way. Therefore this hiding is benign if the kind of sort
  // is not important and useful for avoiding casts if the term is a known
  // smt_bit_vector_constant_termt at compile time and the `bit_width()` is
  // needed.
  const smt_bit_vector_sortt &get_sort() const;
};

class smt_function_application_termt : public smt_termt
{
private:
  /// Unchecked construction of function application terms. The public factoryt
  /// sub class should be used to construct instances of this term with the
  /// appropriate checks for the function being applied.
  smt_function_application_termt(
    smt_identifier_termt function_identifier,
    std::vector<smt_termt> arguments);

public:
  const smt_identifier_termt &function_identifier() const;
  std::vector<std::reference_wrapper<const smt_termt>> arguments() const;

  template <typename functiont>
  class factoryt
  {
  private:
    functiont function;

  public:
    template <typename... function_type_argument_typest>
    explicit factoryt(function_type_argument_typest &&... arguments) noexcept
      : function{std::forward<function_type_argument_typest>(arguments)...}
    {
    }

    template <typename... argument_typest>
    smt_function_application_termt
    operator()(argument_typest &&... arguments) const
    {
      function.validate(arguments...);
      auto return_sort = function.return_sort(arguments...);
      return smt_function_application_termt{
        smt_identifier_termt{function.identifier(), std::move(return_sort)},
        {std::forward<argument_typest>(arguments)...}};
    }
  };
};

class smt_term_const_downcast_visitort
{
public:
#define TERM_ID(the_id) virtual void visit(const smt_##the_id##_termt &) = 0;
#include "smt_terms.def"
#undef TERM_ID
};

#endif // CPROVER_SOLVERS_SMT2_INCREMENTAL_SMT_TERMS_H

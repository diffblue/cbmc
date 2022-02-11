// Author: Diffblue Ltd.

#include <solvers/smt2_incremental/smt_terms.h>

#include <solvers/smt2_incremental/smt_sorts.h>

#include <util/arith_tools.h>
#include <util/mp_arith.h>
#include <util/range.h>

#include <algorithm>
#include <regex>

// Define the irep_idts for terms.
#define TERM_ID(the_id)                                                        \
  const irep_idt ID_smt_##the_id##_term{"smt_" #the_id "_term"};
#include <solvers/smt2_incremental/smt_terms.def>
#undef TERM_ID

smt_termt::smt_termt(irep_idt id, smt_sortt sort)
  : irept{id, {{ID_type, upcast(std::move(sort))}}, {}}
{
}

bool smt_termt::operator==(const smt_termt &other) const
{
  return irept::operator==(other);
}

bool smt_termt::operator!=(const smt_termt &other) const
{
  return !(*this == other);
}

const smt_sortt &smt_termt::get_sort() const
{
  return downcast(find(ID_type));
}

smt_bool_literal_termt::smt_bool_literal_termt(bool value)
  : smt_termt{ID_smt_bool_literal_term, smt_bool_sortt{}}
{
  set(ID_value, value);
}

bool smt_bool_literal_termt::value() const
{
  return get_bool(ID_value);
}

static bool is_valid_smt_identifier(irep_idt identifier)
{
  // The below regex matches a complete string which does not contain the `|`
  // character. So it would match the string `foo bar`, but not `|foo bar|`.
  static const std::regex valid{"[^\\|]*"};
  return std::regex_match(id2string(identifier), valid);
}

smt_identifier_termt::smt_identifier_termt(
  irep_idt identifier,
  smt_sortt sort,
  std::vector<smt_indext> indices)
  : smt_termt(ID_smt_identifier_term, std::move(sort))
{
  // The below invariant exists as a sanity check that the string being used for
  // the identifier is in unescaped form. This is because the escaping and
  // unescaping are implementation details of the printing to string and
  // response parsing respectively, not part of the underlying data.
  INVARIANT(
    is_valid_smt_identifier(identifier),
    R"(Identifiers may not contain | characters.)");
  set(ID_identifier, identifier);
  for(auto &index : indices)
  {
    get_sub().push_back(
      smt_indext::storert<smt_identifier_termt>::upcast(std::move(index)));
  }
}

irep_idt smt_identifier_termt::identifier() const
{
  return get(ID_identifier);
}

std::vector<std::reference_wrapper<const smt_indext>>
smt_identifier_termt::indices() const
{
  return make_range(get_sub()).map([](const irept &index) {
    return std::cref(
      smt_indext::storert<smt_identifier_termt>::downcast(index));
  });
}

smt_bit_vector_constant_termt::smt_bit_vector_constant_termt(
  const mp_integer &value,
  smt_bit_vector_sortt sort)
  : smt_termt{ID_smt_bit_vector_constant_term, std::move(sort)}
{
  INVARIANT(
    value < power(mp_integer{2}, get_sort().bit_width()),
    "value must fit in number of bits available.");
  INVARIANT(
    !value.is_negative(),
    "Negative numbers are not supported by bit vector constants.");
  set(ID_value, integer2bvrep(value, get_sort().bit_width()));
}

smt_bit_vector_constant_termt::smt_bit_vector_constant_termt(
  const mp_integer &value,
  std::size_t bit_width)
  : smt_bit_vector_constant_termt{value, smt_bit_vector_sortt{bit_width}}
{
}

mp_integer smt_bit_vector_constant_termt::value() const
{
  return bvrep2integer(get(ID_value), get_sort().bit_width(), false);
}

const smt_bit_vector_sortt &smt_bit_vector_constant_termt::get_sort() const
{
  // The below cast is sound because the constructor only allows bit_vector
  // sorts to be set.
  return static_cast<const smt_bit_vector_sortt &>(smt_termt::get_sort());
}

smt_function_application_termt::smt_function_application_termt(
  smt_identifier_termt function_identifier,
  std::vector<smt_termt> arguments)
  : smt_termt(ID_smt_function_application_term, function_identifier.get_sort())
{
  set(ID_identifier, std::move(function_identifier));
  std::transform(
    std::make_move_iterator(arguments.begin()),
    std::make_move_iterator(arguments.end()),
    std::back_inserter(get_sub()),
    [](smt_termt &&argument) { return static_cast<irept &&>(argument); });
}

const smt_identifier_termt &
smt_function_application_termt::function_identifier() const
{
  return static_cast<const smt_identifier_termt &>(find(ID_identifier));
}

std::vector<std::reference_wrapper<const smt_termt>>
smt_function_application_termt::arguments() const
{
  return make_range(get_sub()).map([](const irept &argument) {
    return std::cref(static_cast<const smt_termt &>(argument));
  });
}

template <typename visitort>
void accept(const smt_termt &term, const irep_idt &id, visitort &&visitor)
{
#define TERM_ID(the_id)                                                        \
  if(id == ID_smt_##the_id##_term)                                             \
    return visitor.visit(static_cast<const smt_##the_id##_termt &>(term));
// The include below is marked as nolint because including the same file
// multiple times is required as part of the x macro pattern.
#include <solvers/smt2_incremental/smt_terms.def> // NOLINT(build/include)
#undef TERM_ID
  UNREACHABLE;
}

void smt_termt::accept(smt_term_const_downcast_visitort &visitor) const
{
  ::accept(*this, id(), visitor);
}

void smt_termt::accept(smt_term_const_downcast_visitort &&visitor) const
{
  ::accept(*this, id(), std::move(visitor));
}

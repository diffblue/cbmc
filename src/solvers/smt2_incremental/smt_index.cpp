// Author: Diffblue Ltd.

#include "smt_index.h"

// Define the irep_idts for kinds of index.
const irep_idt ID_smt_numeral_index{"smt_numeral_index"};
const irep_idt ID_smt_symbol_index{"smt_symbol_index"};

bool smt_indext::operator==(const smt_indext &other) const
{
  return irept::operator==(other);
}

bool smt_indext::operator!=(const smt_indext &other) const
{
  return !(*this == other);
}

template <>
const smt_numeral_indext *smt_indext::cast<smt_numeral_indext>() const &
{
  return id() == ID_smt_numeral_index
           ? static_cast<const smt_numeral_indext *>(this)
           : nullptr;
}

template <>
const smt_symbol_indext *smt_indext::cast<smt_symbol_indext>() const &
{
  return id() == ID_smt_symbol_index
           ? static_cast<const smt_symbol_indext *>(this)
           : nullptr;
}

void smt_indext::accept(smt_index_const_downcast_visitort &visitor) const
{
  if(const auto numeral = this->cast<smt_numeral_indext>())
    return visitor.visit(*numeral);
  if(const auto symbol = this->cast<smt_symbol_indext>())
    return visitor.visit(*symbol);
  UNREACHABLE;
}

smt_numeral_indext::smt_numeral_indext(std::size_t value)
  : smt_indext{ID_smt_numeral_index}
{
  set_size_t(ID_value, value);
}

std::size_t smt_numeral_indext::value() const
{
  return get_size_t(ID_value);
}

smt_symbol_indext::smt_symbol_indext(irep_idt identifier)
  : smt_indext{ID_smt_symbol_index}
{
  set(ID_identifier, identifier);
}

irep_idt smt_symbol_indext::identifier() const
{
  return get(ID_identifier);
}

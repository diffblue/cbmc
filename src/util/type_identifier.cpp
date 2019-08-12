#include "type_identifier.h"

int type_identifiert::identifier_counter = 0;

bool type_identifiert::operator==(const type_identifiert &other) const
{
  return id == other.id;
}

bool type_identifiert::operator!=(const type_identifiert &other) const
{
  return id != other.id;
}

/*******************************************************************\

Module: Language Features

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Language Features

#include "language_features.h"

#include <util/cprover_prefix.h>
#include <util/namespace.h>

#include "goto_model.h"

static const irep_idt language_features_identifier =
  CPROVER_PREFIX "language_features";

static const symbolt *
language_features_symbol(const symbol_tablet &symbol_table)
{
  const namespacet ns(symbol_table);
  const symbolt *result;
  if(!ns.lookup(language_features_identifier, result))
    return result;
  else
    return nullptr;
}

static symbolt &language_features_symbol(symbol_tablet &symbol_table)
{
  symbolt *result = symbol_table.get_writeable(language_features_identifier);

  if(result == nullptr)
  {
    // need to add
    symbolt new_symbol;
    new_symbol.base_name = language_features_identifier;
    new_symbol.name = language_features_identifier;
    new_symbol.mode =
      ID_C; // arbitrary, to make symbolt::is_well_formed() happy
    new_symbol.value = exprt(irep_idt());
    symbol_table.move(new_symbol, result);
    return *result;
  }
  else
    return *result;
}

bool has_language_feature(
  const symbol_tablet &symbol_table,
  const irep_idt &feature)
{
  auto symbol = language_features_symbol(symbol_table);
  if(symbol == nullptr)
  {
    // Legacy model without annotations, we conservatively
    // assume that the model might use the feature.
    return true;
  }
  else
  {
    auto &feature_irep = symbol->value.find(feature);
    if(feature_irep.is_nil())
    {
      // No annotation. We assume that the feature is not used.
      return false;
    }
    else
      return symbol->value.get_bool(feature);
  }
}

bool has_language_feature(
  const abstract_goto_modelt &model,
  const irep_idt &feature)
{
  return has_language_feature(model.get_symbol_table(), feature);
}

void add_language_feature(symbol_tablet &symbol_table, const irep_idt &feature)
{
  auto &symbol = language_features_symbol(symbol_table);
  symbol.value.set(feature, true);
}

void add_language_feature(goto_modelt &model, const irep_idt &feature)
{
  add_language_feature(model.symbol_table, feature);
}

void clear_language_feature(
  symbol_tablet &symbol_table,
  const irep_idt &feature)
{
  auto &symbol = language_features_symbol(symbol_table);
  symbol.value.set(feature, false);
}

void clear_language_feature(goto_modelt &model, const irep_idt &feature)
{
  clear_language_feature(model.symbol_table, feature);
}

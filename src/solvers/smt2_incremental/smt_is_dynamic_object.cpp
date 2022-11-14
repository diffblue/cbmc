// Author: Diffblue Ltd.

#include "smt_is_dynamic_object.h"

#include <util/c_types.h>
#include <util/config.h>

#include <solvers/smt2_incremental/theories/smt_core_theory.h>

static smt_declare_function_commandt
make_is_dynamic_object_function_declaration()
{
  return smt_declare_function_commandt{
    smt_identifier_termt{"is_dynamic_object", smt_bool_sortt{}},
    {smt_bit_vector_sortt{config.bv_encoding.object_bits}}};
}

smt_is_dynamic_objectt::smt_is_dynamic_objectt()
  : declaration{make_is_dynamic_object_function_declaration()},
    make_application{smt_command_functiont{declaration}}
{
}

smt_commandt smt_is_dynamic_objectt::make_definition(
  std::size_t unique_id,
  bool is_dynamic_object) const
{
  const auto id_sort =
    declaration.parameter_sorts().at(0).get().cast<smt_bit_vector_sortt>();
  INVARIANT(id_sort, "Object identifiers are expected to have bit vector sort");
  const auto bit_vector_of_id =
    smt_bit_vector_constant_termt{unique_id, *id_sort};
  return smt_assert_commandt{smt_core_theoryt::equal(
    make_application(std::vector<smt_termt>{bit_vector_of_id}),
    smt_bool_literal_termt{is_dynamic_object})};
}

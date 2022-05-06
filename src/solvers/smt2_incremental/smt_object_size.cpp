// Author: Diffblue Ltd.

#include "smt_object_size.h"

#include <util/c_types.h>
#include <util/config.h>

#include <solvers/smt2_incremental/convert_expr_to_smt.h>
#include <solvers/smt2_incremental/smt_core_theory.h>
#include <solvers/smt2_incremental/smt_sorts.h>

static smt_declare_function_commandt make_object_size_function_declaration()
{
  return smt_declare_function_commandt{
    smt_identifier_termt{
      "size_of_object", convert_type_to_smt_sort(size_type())},
    {smt_bit_vector_sortt{config.bv_encoding.object_bits}}};
}

smt_object_sizet::smt_object_sizet()
  : declaration{make_object_size_function_declaration()},
    make_application{smt_command_functiont{declaration}}
{
}

smt_commandt smt_object_sizet::make_definition(
  const std::size_t unique_id,
  smt_termt size) const
{
  const auto id_sort =
    declaration.parameter_sorts().at(0).get().cast<smt_bit_vector_sortt>();
  INVARIANT(id_sort, "Object identifiers are expected to have bit vector sort");
  const auto bit_vector_of_id =
    smt_bit_vector_constant_termt{unique_id, *id_sort};
  return smt_assert_commandt{smt_core_theoryt::equal(
    make_application(std::vector<smt_termt>{bit_vector_of_id}),
    std::move(size))};
}

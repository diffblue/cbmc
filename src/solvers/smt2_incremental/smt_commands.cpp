// Author: Diffblue Ltd.

#include <solvers/smt2_incremental/smt_commands.h>

#include <util/range.h>

// Define the irep_idts for commands.
#define COMMAND_ID(the_id)                                                     \
  const irep_idt ID_smt_##the_id##_command{"smt_" #the_id "_command"};
#include <solvers/smt2_incremental/smt_commands.def>
#undef COMMAND_ID

bool smt_commandt::operator==(const smt_commandt &other) const
{
  return irept::operator==(other);
}

bool smt_commandt::operator!=(const smt_commandt &other) const
{
  return !(*this == other);
}

smt_assert_commandt::smt_assert_commandt(smt_termt condition)
  : smt_commandt{ID_smt_assert_command}
{
  INVARIANT(
    condition.get_sort() == smt_bool_sortt{},
    "Only terms with boolean sorts can be asserted.");
  set(ID_cond, upcast(std::move(condition)));
}

const smt_termt &smt_assert_commandt::condition() const
{
  return downcast(find(ID_cond));
}

smt_check_sat_commandt::smt_check_sat_commandt()
  : smt_commandt{ID_smt_check_sat_command}
{
}

smt_declare_function_commandt::smt_declare_function_commandt(
  smt_identifier_termt identifier,
  std::vector<smt_sortt> parameter_sorts)
  : smt_commandt{ID_smt_declare_function_command}
{
  set(ID_identifier, term_storert::upcast(std::move(identifier)));
  std::transform(
    std::make_move_iterator(parameter_sorts.begin()),
    std::make_move_iterator(parameter_sorts.end()),
    std::back_inserter(get_sub()),
    [](smt_sortt &&parameter_sort) {
      return sort_storert::upcast(std::move(parameter_sort));
    });
}

const smt_identifier_termt &smt_declare_function_commandt::identifier() const
{
  return static_cast<const smt_identifier_termt &>(
    term_storert::downcast(find(ID_identifier)));
}

const smt_sortt &smt_declare_function_commandt::return_sort() const
{
  return identifier().get_sort();
}

std::vector<std::reference_wrapper<const smt_sortt>>
smt_declare_function_commandt::parameter_sorts() const
{
  return make_range(get_sub()).map([](const irept &parameter_sort) {
    return std::cref(sort_storert::downcast(parameter_sort));
  });
}

smt_exit_commandt::smt_exit_commandt() : smt_commandt{ID_smt_exit_command}
{
}

smt_define_function_commandt::smt_define_function_commandt(
  irep_idt identifier,
  std::vector<smt_identifier_termt> parameters,
  smt_termt definition)
  : smt_commandt{ID_smt_define_function_command}
{
  set(ID_identifier, identifier);
  std::transform(
    std::make_move_iterator(parameters.begin()),
    std::make_move_iterator(parameters.end()),
    std::back_inserter(get_sub()),
    [](smt_identifier_termt &&parameter) {
      return upcast(std::move(parameter));
    });
  set(ID_code, upcast(std::move(definition)));
}

const irep_idt &smt_define_function_commandt::identifier() const
{
  return get(ID_identifier);
}

std::vector<std::reference_wrapper<const smt_identifier_termt>>
smt_define_function_commandt::parameters() const
{
  return make_range(get_sub()).map([](const irept &parameter) {
    return std::cref(
      static_cast<const smt_identifier_termt &>(downcast((parameter))));
  });
}

const smt_sortt &smt_define_function_commandt::return_sort() const
{
  return definition().get_sort();
}

const smt_termt &smt_define_function_commandt::definition() const
{
  return downcast(find(ID_code));
}

smt_get_value_commandt::smt_get_value_commandt(smt_termt descriptor)
  : smt_commandt{ID_smt_get_value_command}
{
  set(ID_value, upcast(std::move(descriptor)));
}

const smt_termt &smt_get_value_commandt::descriptor() const
{
  return downcast(find(ID_value));
}

smt_push_commandt::smt_push_commandt(std::size_t levels)
  : smt_commandt(ID_smt_push_command)
{
  set_size_t(ID_value, levels);
}

size_t smt_push_commandt::levels() const
{
  return get_size_t(ID_value);
}

smt_pop_commandt::smt_pop_commandt(std::size_t levels)
  : smt_commandt(ID_smt_pop_command)
{
  set_size_t(ID_value, levels);
}

size_t smt_pop_commandt::levels() const
{
  return get_size_t(ID_value);
}

smt_set_logic_commandt::smt_set_logic_commandt(smt_logict logic)
  : smt_commandt(ID_smt_set_logic_command)
{
  set(ID_value, upcast(std::move(logic)));
}

const smt_logict &smt_set_logic_commandt::logic() const
{
  return downcast(find(ID_value));
}

smt_set_option_commandt::smt_set_option_commandt(smt_optiont option)
  : smt_commandt(ID_smt_set_option_command)
{
  set(ID_value, upcast(std::move(option)));
}

const smt_optiont &smt_set_option_commandt::option() const
{
  return downcast(find(ID_value));
}

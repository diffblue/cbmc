/*******************************************************************\

Module:

Author: Daniel Poetzl

\*******************************************************************/

#include "c_object_factory_parameters.h"

#include <util/cmdline.h>
#include <util/exception_utils.h>
#include <util/optional_utils.h>
#include <util/string_utils.h>

#include <algorithm>
#include <string>

void parse_c_object_factory_options(const cmdlinet &cmdline, optionst &options)
{
  parse_object_factory_options(cmdline, options);
  if(cmdline.isset("pointers-to-treat-as-array"))
  {
    options.set_option(
      "pointers-to-treat-as-array",
      cmdline.get_comma_separated_values("pointers-to-treat-as-array"));
  }
  if(cmdline.isset("associated-array-sizes"))
  {
    options.set_option(
      "associated-array-sizes",
      cmdline.get_comma_separated_values("associated-array-sizes"));
  }
  if(cmdline.isset("max-dynamic-array-size"))
  {
    options.set_option(
      "max-dynamic-array-size", cmdline.get_value("max-dynamic-array-size"));
  }
}

bool c_object_factory_parameterst::should_be_treated_as_array(irep_idt id) const
{
  return pointers_to_treat_as_array.find(id) !=
         pointers_to_treat_as_array.end();
}

void c_object_factory_parameterst::set(const optionst &options)
{
  object_factory_parameterst::set(options);
  auto const &pointers_to_treat_as_array =
    options.get_list_option("pointers-to-treat-as-array");
  std::transform(
    begin(pointers_to_treat_as_array),
    end(pointers_to_treat_as_array),
    inserter(
      this->pointers_to_treat_as_array, this->pointers_to_treat_as_array.end()),
    id2string);
  if(options.is_set("max-dynamic-array-size"))
  {
    max_dynamic_array_size =
      options.get_unsigned_int_option("max-dynamic-array-size");
    if(max_dynamic_array_size == 0)
    {
      throw invalid_command_line_argument_exceptiont(
        "Max dynamic array size must be >= 1", "--max-dynamic-array-size");
    }
  }
  if(options.is_set("associated-array-sizes"))
  {
    array_name_to_associated_array_size_variable.clear();
    variables_that_hold_array_sizes.clear();
    auto const &array_size_pairs =
      options.get_list_option("associated-array-sizes");
    for(auto const &array_size_pair : array_size_pairs)
    {
      std::string array_name;
      std::string size_name;
      try
      {
        split_string(array_size_pair, ':', array_name, size_name);
      }
      catch(const deserialization_exceptiont &e)
      {
        throw invalid_command_line_argument_exceptiont{
          "can't parse parameter value",
          "--associated-array-sizes",
          "pairs of array/size parameter names, separated by a ':' colon"};
      }
      auto const mapping_insert_result =
        array_name_to_associated_array_size_variable.insert(
          {irep_idt{array_name}, irep_idt{size_name}});
      if(!mapping_insert_result.second)
      {
        throw invalid_command_line_argument_exceptiont{
          "duplicate associated size entries for array `" + array_name +
            "', existing: `" + id2string(mapping_insert_result.first->second) +
            "', tried to insert: `" + size_name + "'",
          "--associated-array-sizes"};
      }
      auto const size_name_insert_result =
        variables_that_hold_array_sizes.insert(irep_idt{size_name});
      if(!size_name_insert_result.second)
      {
        throw invalid_command_line_argument_exceptiont{
          "using size parameter `" + size_name + "' more than once",
          "--associated-array-sizes"};
      }
    }
  }
}

bool c_object_factory_parameterst::is_array_size_parameter(irep_idt id) const
{
  return variables_that_hold_array_sizes.find(id) !=
         end(variables_that_hold_array_sizes);
}

optionalt<irep_idt> c_object_factory_parameterst::get_associated_size_variable(
  irep_idt array_id) const
{
  return optional_lookup(
    array_name_to_associated_array_size_variable, array_id);
}

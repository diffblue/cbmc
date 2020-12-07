/*******************************************************************\

Module: RRA Specification

Author: Adrian Palacios accorell@amazon.com
        Murali Talupur  talupur@amazon.com
        Lefan Zhang     lefanz@amazon.com

\*******************************************************************/

#include <fstream>
#include <iostream>

#include <ansi-c/ansi_c_language.h>
#include <ansi-c/ansi_c_parser.h>
#include <ansi-c/ansi_c_typecheck.h>
#include <json/json_parser.h>
#include <langapi/language.h>
#include <langapi/mode.h>
#include <util/file_util.h>
#include <util/message.h>
#include <util/std_expr.h>

#include "rra_spec.h"
#include "rra_spec_gen.h"

rra_spect::rra_spect(std::string filename, message_handlert &message_handler)
{
  jsont json;

  std::string no_path_filename =
    filename.substr(filename.find_last_of('/'), filename.length());
  std::string clean_filename =
    no_path_filename.substr(0, no_path_filename.find_last_of('.'));
  std::string abst_funcs_filename =
    get_current_working_directory() + clean_filename + "_abst_funcs.c";
  abst_function_file = abst_funcs_filename;

  std::ifstream json_ifstream(filename);

  INVARIANT(json_ifstream, "the json file could not be opened");

  INVARIANT(
    !parse_json(json_ifstream, filename, message_handler, json),
    "the json file could not be parsed");

  const auto &json_object = to_json_object(json);
  INVARIANT(
    json_object.find("entries") != json_object.end(),
    "'entries' is missing from the json file");
  const auto &json_entries = json_object.find("entries")->second;
  const auto &json_entries_array = to_json_array(json_entries);
  for(auto it = json_entries_array.begin(); it != json_entries_array.end();
      ++it)
  {
    const auto &entry_obj = to_json_object(*it);
    spect spec;
    size_t spec_index = specs.size();
    spec.set_spect_index(spec_index);

    INVARIANT(
      entry_obj.find("function") != entry_obj.end(),
      "'function' is missing from an entry in json file.");
    // we assume that all entries in the json
    // file are located in the same function
    function = entry_obj.find("function")->second.value;
    // insert the entity

    INVARIANT(
      entry_obj.find("name") != entry_obj.end(),
      "'name' is missing from an entry in json file.");
    INVARIANT(
      entry_obj.find("entity") != entry_obj.end(),
      "'entity' is missing from an entry in json file.");
    spec.insert_entity(
      entry_obj.find("name")->second.value,
      entry_obj.find("entity")->second.value);
    INVARIANT(
      entry_obj.find("related-entities") != entry_obj.end(),
      "'related-entities' is missing from an entry in json file.");
    const auto &json_re_array =
      to_json_array(entry_obj.find("related-entities")->second);
    for(auto it_r = json_re_array.begin(); it_r != json_re_array.end(); ++it_r)
    {
      const auto &related_entity = to_json_object(*it_r);
      INVARIANT(
        related_entity.find("name") != related_entity.end(),
        "'name' is missing from related entity.");
      spec.insert_entity(
        related_entity.find("name")->second.value,
        related_entity.find("entity")->second.value);
    }

    spec.set_addition_func("add_" + std::to_string(spec_index));
    spec.set_minus_func("sub_" + std::to_string(spec_index));
    spec.set_multiply_func("mult_" + std::to_string(spec_index));
    spec.set_precise_func("is_precise_" + std::to_string(spec_index));
    spec.set_abstract_func("abs_" + std::to_string(spec_index));
    spec.set_concretize_func("conc_" + std::to_string(spec_index));

    INVARIANT(
      entry_obj.find("shape") != entry_obj.end(),
      "'shape' is missing from an entry in json file.");
    std::string shape_type =
      to_json_string(entry_obj.find("shape")->second).value;

    std::vector<irep_idt> indices = rra_spec_gent::generate_indices(shape_type);
    std::vector<std::string> assumptions =
      rra_spec_gent::generate_assumptions(shape_type, indices);

    spec.set_shape(indices, assumptions, shape_type);

    specs.push_back(spec);
  }
}

void rra_spect::generate_abstract_function_files()
{
  std::ofstream gen_abst_funcs_file;
  std::ostringstream abst_funcs_output;

  gen_abst_funcs_file.open(abst_function_file, std::ofstream::out);

  rra_spec_gent::generate_abst_funcs_hdr(abst_funcs_output);

  for(size_t spec_index = 0; spec_index < specs.size(); spec_index++)
  {
    std::string spec_shape = specs[spec_index].get_shape_type();

    rra_spec_gent::generate_functions(
      spec_index, spec_shape, abst_funcs_output);
  }

  gen_abst_funcs_file << abst_funcs_output.str();
  gen_abst_funcs_file.close();
}

void rra_spect::remove_abstract_function_files()
{
  const char *file_to_remove = abst_function_file.c_str();
  std::remove(file_to_remove);
}

std::vector<std::string> rra_spect::get_abstraction_function_files() const
{
  std::vector<std::string> files;

  files.push_back(abst_function_file);

  return files;
}

rra_spect::spect rra_spect::spect::update_abst_spec(
  irep_idt old_function,
  irep_idt new_function,
  std::unordered_map<irep_idt, func_call_arg_namet> _name_pairs) const
{
  // This function update the entity forest across function calls
  // For example, if we have two functions
  // struct list{
  //   struct buf{
  //       len
  //   }
  // };
  // bar(list::buf *buffer)
  // {
  // }
  // foo(){
  //   list l;
  //   bar(&(l.buf));
  // }
  // Foo forest:
  // l
  // |
  // |
  // buf (STRUCT)
  // |
  // |
  // len
  // (LENGTH) (ARRAY)
  // Bar forest will be updated into:
  // buffer (STRUCT_POINTER)
  // |
  // |
  // len
  // (LENGTH) (ARRAY)

  // copy the spec into a new one, clear the entities
  spect new_spec(*this);
  new_spec.abst_entities =
    std::unordered_map<irep_idt, std::unique_ptr<entityt>>();

  auto all_abst_entities = get_all_abst_entities();
  const auto &top_layer_entities = abst_entities;

  // step 1: insert all global entities
  for(const auto &ent : top_layer_entities)
    if(std::string(ent.first.c_str()).rfind(old_function.c_str(), 0))
      new_spec.insert_entity(ent.first, *(ent.second));

  // step 2: insert all entities shown up in function call argument pairs
  for(const auto &pair : _name_pairs)
  {
    // only insert entity into the new one if the old name belongs to the spect
    // we shouldn't insert entities that don't belong to this entity
    if(all_abst_entities.find(pair.first) != all_abst_entities.end())
    {
      auto orig_entity = all_abst_entities[pair.first];
      // flag: REGULAR / POINTER_TO_ENTITY / ENTITY_TO_POINTER
      func_call_arg_namet::arg_translate_typet flag = pair.second.type;
      orig_entity.name = pair.second.name;
      if(flag == func_call_arg_namet::ENTITY_TO_POINTER)
      {
        if(orig_entity.type == entityt::STRUCT)
          orig_entity.type = entityt::STRUCT_POINTER;
        else
          throw "the entity " + std::string(orig_entity.name.c_str()) +
            " needs to be a struct to be translated into a pointer." +
            " Currently we are not supporting other types of pointer "
            "calculation as function args.";
      }
      else if(flag == func_call_arg_namet::POINTER_TO_ENTITY)
      {
        if(orig_entity.type == entityt::STRUCT_POINTER)
          orig_entity.type = entityt::STRUCT;
        else
          throw "the entity " + std::string(orig_entity.name.c_str()) +
            " needs to be a struct pointer to be translated into a struct." +
            " Currently we are not supporting other types of pointer "
            "calculation as function args.";
      }
      else
      {
      }
      new_spec.insert_entity(pair.second.name, orig_entity);
    }
  }

  return new_spec;
}

rra_spect rra_spect::update_abst_spec(
  irep_idt old_function,
  irep_idt new_function,
  std::unordered_map<irep_idt, spect::func_call_arg_namet> _name_pairs) const
{
  if(function != old_function)
  {
    throw "the old rra_spect should match the callee";
  }

  rra_spect new_abst_spec;
  new_abst_spec.function = new_function;
  for(const auto &spec : specs)
  {
    spect new_spec =
      spec.update_abst_spec(old_function, new_function, _name_pairs);
    if(!spec.compare_shape_only(new_spec))
      throw "the updated spect's shape should be the same as the original one";
    new_abst_spec.specs.push_back(new_spec);
  }
  if(specs.size() != new_abst_spec.specs.size())
    throw "the updated specs' size should remain the same";
  return new_abst_spec;
}

void rra_spect::get_entities_string(std::ostream &output) const
{
  for(const auto &spec : specs)
  {
    for(const auto &ent : spec.get_abst_arrays())
      output << "array: " + std::string(ent.first.c_str()) + "\n";
    for(const auto &ent : spec.get_abst_const_c_strs())
      output << "const c_str: " + std::string(ent.first.c_str()) + "\n";
    for(const auto &ent : spec.get_abst_indices())
      output << "index: " + std::string(ent.first.c_str()) + "\n";
  }
}

void rra_spect::print_entities() const
{
  std::ostringstream output;

  get_entities_string(output);

  // TODO: Avoid hard-wiring std::cout
  std::cout << output.str();
}

void rra_spect::spect::insert_entity(
  const irep_idt &_name,
  const rra_spect::spect::entityt &entity)
{
  std::string name_str = _name.c_str();
  std::unordered_map<irep_idt, std::unique_ptr<entityt>>
    *current_layer_entities = &abst_entities;
  while(!name_str.empty())
  {
    size_t arrow_pos = name_str.find("->", 0);
    size_t point_pos = name_str.find(".", 0);
    if(arrow_pos != std::string::npos || point_pos != std::string::npos)
    {
      if(arrow_pos < point_pos) // first layer is an "->"
      {
        std::string first_layer_name = name_str.substr(0, arrow_pos);
        name_str = name_str.substr(arrow_pos + 2);
        if(
          current_layer_entities->find(first_layer_name) ==
          current_layer_entities->end())
          current_layer_entities->insert(
            {first_layer_name,
             std::unique_ptr<entityt>(
               new struct_pointer_entityt(first_layer_name))});
        if(
          (*current_layer_entities)[first_layer_name]->type !=
          entityt::STRUCT_POINTER)
          throw "the entity " + first_layer_name +
            " doesn't seem to be a struct pointer. " +
            "Most likely the json file is wrong.";
        current_layer_entities =
          &((*current_layer_entities)[first_layer_name]->sub_entities);
      }
      else // first layer is an "."
      {
        std::string first_layer_name = name_str.substr(0, point_pos);
        name_str = name_str.substr(point_pos + 1);
        if(
          current_layer_entities->find(first_layer_name) ==
          current_layer_entities->end())
          current_layer_entities->insert(
            {first_layer_name,
             std::unique_ptr<entityt>(new struct_entityt(first_layer_name))});
        if((*current_layer_entities)[first_layer_name]->type != entityt::STRUCT)
          throw "the entity " + first_layer_name +
            " doesn't seem to be a struct. " +
            "Most likely the json file is wrong.";
        current_layer_entities =
          &((*current_layer_entities)[first_layer_name]->sub_entities);
      }
    }
    else // "->" and "." are not found
    {
      // this is at the leaf
      INVARIANT(
        name_str == std::string(entity.name.c_str()),
        "the full name and the entity name should match.");
      INVARIANT(
        current_layer_entities->find(name_str) == current_layer_entities->end(),
        "the entity " + name_str + " already exists");
      current_layer_entities->insert(
        {name_str, std::unique_ptr<entityt>(new entityt(entity))});
      name_str = "";
    }
  }
}

void rra_spect::spect::insert_entity(
  const irep_idt &_name,
  const entityt::entityt_type &_type)
{
  std::string name_str = _name.c_str();
  std::unordered_map<irep_idt, std::unique_ptr<entityt>>
    *current_layer_entities = &abst_entities;
  while(!name_str.empty())
  {
    size_t arrow_pos = name_str.find("->", 0);
    size_t point_pos = name_str.find(".", 0);
    if(arrow_pos != std::string::npos || point_pos != std::string::npos)
    {
      if(arrow_pos < point_pos) // first layer is an "->"
      {
        std::string first_layer_name = name_str.substr(0, arrow_pos);
        name_str = name_str.substr(arrow_pos + 2);
        if(
          current_layer_entities->find(first_layer_name) ==
          current_layer_entities->end())
          current_layer_entities->insert(
            {first_layer_name,
             std::unique_ptr<entityt>(
               new struct_pointer_entityt(first_layer_name))});
        if(
          (*current_layer_entities)[first_layer_name]->type !=
          entityt::STRUCT_POINTER)
          throw "the entity " + first_layer_name +
            " doesn't seem to be a struct pointer." +
            "Most likely the json file is wrong.";
        current_layer_entities =
          &((*current_layer_entities)[first_layer_name]->sub_entities);
      }
      else // first layer is an "."
      {
        std::string first_layer_name = name_str.substr(0, point_pos);
        name_str = name_str.substr(point_pos + 1);
        if(
          current_layer_entities->find(first_layer_name) ==
          current_layer_entities->end())
          current_layer_entities->insert(
            {first_layer_name,
             std::unique_ptr<entityt>(new struct_entityt(first_layer_name))});
        if((*current_layer_entities)[first_layer_name]->type != entityt::STRUCT)
          throw "the entity " + first_layer_name +
            " doesn't seem to be a struct." +
            "Most likely the json file is wrong.";
        current_layer_entities =
          &((*current_layer_entities)[first_layer_name]->sub_entities);
      }
    }
    else // "->" and "." are not found
    {
      // this is at the leaf
      if(
        current_layer_entities->find(name_str) == current_layer_entities->end())
        current_layer_entities->insert(
          {name_str, std::unique_ptr<entityt>(new entityt(name_str, _type))});
      else
        throw "entity " + name_str + " already exists";
      name_str = "";
    }
  }
}

void rra_spect::spect::insert_entity(
  const irep_idt &_name,
  const std::string &_type)
{
  if(_type == "array")
    insert_entity(_name, entityt::ARRAY);
  else if(_type == "scalar")
    insert_entity(_name, entityt::SCALAR);
  else if(_type == "length")
    insert_entity(_name, entityt::LENGTH);
  else if(_type == "const_c_str")
    insert_entity(_name, entityt::CONST_C_STR);
  else
    throw "unknown entity type: " + _type;
}

std::vector<exprt>
rra_spect::spect::get_assumption_exprs(const namespacet &ns) const
{
  return shape.get_assumption_exprs(ns, spect_index);
}

// this is a re-write of ansi_c_languaget::to_expr
// to add the prefix before the variable name
bool shape_assumption_to_expr(
  const std::string &code,
  const std::string &module,
  exprt &expr,
  const namespacet &ns)
{
  // change symbol expression "name" to "<prefix>name"
  class add_prefixt : public expr_visitort
  {
  public:
    add_prefixt(const irep_idt &_prefix, const namespacet &_ns)
      : prefix(_prefix), ns(_ns)
    {
    }
    void operator()(exprt &expr) override
    {
      if(expr.id() == ID_symbol)
      {
        const symbol_exprt symb_expr = to_symbol_expr(expr);
        // get the old name
        irep_idt name = symb_expr.get_identifier();
        // get the new name
        irep_idt new_name =
          irep_idt(std::string(prefix.c_str()) + std::string(name.c_str()));
        // replace the expr
        const symbol_tablet symbol_table = ns.get_symbol_table();
        INVARIANT(
          symbol_table.has_symbol(new_name),
          "The concrete index variable " + std::string(new_name.c_str()) +
            " is not defined");
        const symbolt &new_symb = symbol_table.lookup_ref(new_name);
        expr = new_symb.symbol_expr();
      }
    }

  protected:
    irep_idt prefix;
    const namespacet &ns; // the ns need to live through the scope of this clss
  };
  expr.make_nil();

  // no preprocessing yet...
  std::istringstream i_preprocessed(
    "void __my_expression = (void) (\n" + code + "\n);");

  null_message_handlert null_message_handler;

  // parsing
  ansi_c_parser.clear();
  ansi_c_parser.set_file(irep_idt());
  ansi_c_parser.in = &i_preprocessed;
  ansi_c_parser.set_message_handler(null_message_handler);
  ansi_c_parser.mode = config.ansi_c.mode;
  ansi_c_parser.ts_18661_3_Floatn_types = config.ansi_c.ts_18661_3_Floatn_types;
  ansi_c_scanner_init();

  bool result = ansi_c_parser.parse();

  if(ansi_c_parser.parse_tree.items.empty())
    result = true;
  else
  {
    expr = ansi_c_parser.parse_tree.items.front().declarator().value();

    // change symbols into symbols with exprs
    add_prefixt ap(module, ns);
    expr.visit(ap);

    // typecheck it
    result = ansi_c_typecheck(expr, null_message_handler, ns);
  }

  // save some memory
  ansi_c_parser.clear();

  // now remove that (void) cast
  if(
    expr.id() == ID_typecast && expr.type().id() == ID_empty &&
    expr.operands().size() == 1)
  {
    expr = to_typecast_expr(expr).op();
  }

  return result;
}

std::vector<exprt> rra_spect::spect::abst_shapet::get_assumption_exprs(
  const namespacet &ns,
  const size_t &spec_index) const
{
  // helper class for parsing assumptions
  std::string module = get_index_name(irep_idt(""), spec_index).c_str();

  std::vector<exprt> result;
  for(const auto &assumption : assumptions)
  {
    exprt expr;
    if(shape_assumption_to_expr(assumption, module, expr, ns))
      throw "cannot parse assumption statements in the json file: " +
        assumption;
    result.push_back(expr);
  }

  return result;
}

std::unordered_map<irep_idt, rra_spect::spect::entityt>
rra_spect::spect::get_all_entities(
  const rra_spect::spect::entityt &ent,
  const irep_idt &prefix)
{
  std::unordered_map<irep_idt, entityt> result;
  result.insert(
    {irep_idt(std::string(prefix.c_str()) + std::string(ent.name.c_str())),
     ent});
  for(const auto &sub_ent : ent.sub_entities)
  {
    irep_idt new_prefix =
      std::string(prefix.c_str()) + std::string(ent.name.c_str());
    if(ent.type == entityt::STRUCT)
      new_prefix = std::string(new_prefix.c_str()) + ".";
    else if(ent.type == entityt::STRUCT_POINTER)
      new_prefix = std::string(new_prefix.c_str()) + "->";
    else
    {
    }

    auto sub_result = get_all_entities(*(sub_ent.second), new_prefix);
    result.insert(sub_result.begin(), sub_result.end());
  }
  return result;
}

std::unordered_map<irep_idt, rra_spect::spect::entityt>
rra_spect::spect::search_for_entities(
  const rra_spect::spect::entityt &ent,
  const rra_spect::spect::entityt::entityt_type &type,
  const irep_idt &prefix)
{
  std::unordered_map<irep_idt, entityt> result;
  if(ent.type == type)
    result.insert(
      {irep_idt(std::string(prefix.c_str()) + std::string(ent.name.c_str())),
       ent});
  for(const auto &sub_ent : ent.sub_entities)
  {
    irep_idt new_prefix =
      std::string(prefix.c_str()) + std::string(ent.name.c_str());
    if(ent.type == entityt::STRUCT)
      new_prefix = std::string(new_prefix.c_str()) + ".";
    else if(ent.type == entityt::STRUCT_POINTER)
      new_prefix = std::string(new_prefix.c_str()) + "->";
    else
    {
    }

    auto sub_result = search_for_entities(*(sub_ent.second), type, new_prefix);
    result.insert(sub_result.begin(), sub_result.end());
  }
  return result;
}

std::unordered_map<irep_idt, rra_spect::spect::entityt>
rra_spect::spect::get_top_level_entities() const
{
  std::unordered_map<irep_idt, entityt> result;
  for(const auto &ent : abst_entities)
    result.insert({ent.first, *(ent.second)});
  return result;
}

std::unordered_map<irep_idt, rra_spect::spect::entityt>
rra_spect::spect::get_all_abst_entities() const
{
  std::unordered_map<irep_idt, entityt> result;
  for(const auto &ent : abst_entities)
  {
    std::unordered_map<irep_idt, entityt> sub_result =
      get_all_entities(*(ent.second), "");
    result.insert(sub_result.begin(), sub_result.end());
  }
  return result;
}

std::unordered_map<irep_idt, rra_spect::spect::entityt>
rra_spect::spect::get_abst_arrays() const
{
  std::unordered_map<irep_idt, entityt> result;
  for(const auto &ent : abst_entities)
  {
    std::unordered_map<irep_idt, entityt> sub_result =
      search_for_entities(*(ent.second), entityt::ARRAY, "");
    result.insert(sub_result.begin(), sub_result.end());
  }
  return result;
}

std::unordered_map<irep_idt, rra_spect::spect::entityt>
rra_spect::spect::get_abst_const_c_strs() const
{
  std::unordered_map<irep_idt, entityt> result;
  for(const auto &ent : abst_entities)
  {
    std::unordered_map<irep_idt, entityt> sub_result =
      search_for_entities(*(ent.second), entityt::CONST_C_STR, "");
    result.insert(sub_result.begin(), sub_result.end());
  }
  return result;
}

std::unordered_map<irep_idt, rra_spect::spect::entityt>
rra_spect::spect::get_abst_indices() const
{
  std::unordered_map<irep_idt, entityt> result;
  for(const auto &ent : abst_entities)
  {
    std::unordered_map<irep_idt, entityt> sub_result_scalar =
      search_for_entities(*(ent.second), entityt::SCALAR, "");
    std::unordered_map<irep_idt, entityt> sub_result_length =
      search_for_entities(*(ent.second), entityt::LENGTH, "");
    result.insert(sub_result_scalar.begin(), sub_result_scalar.end());
    result.insert(sub_result_length.begin(), sub_result_length.end());
  }
  return result;
}

std::unordered_map<irep_idt, rra_spect::spect::entityt>
rra_spect::spect::get_abst_lengths() const
{
  std::unordered_map<irep_idt, entityt> result;
  for(const auto &ent : abst_entities)
  {
    std::unordered_map<irep_idt, entityt> sub_result =
      search_for_entities(*(ent.second), entityt::LENGTH, "");
    result.insert(sub_result.begin(), sub_result.end());
  }
  return result;
}

void rra_spect::spect::search_all_lengths_and_generate_path(
  std::vector<rra_spect::spect::entityt> &current_path,
  std::vector<std::vector<rra_spect::spect::entityt>> &results)
{
  INVARIANT(
    !current_path.empty(),
    "The current path should not be empty when calling "
    "search_all_lengths_and_gererate_path");
  const entityt current_entity = *(current_path.end() - 1);
  if(current_entity.type == entityt::LENGTH)
    results.push_back(current_path);
  for(const auto &ent : current_entity.sub_entities)
  {
    current_path.push_back(*ent.second);
    search_all_lengths_and_generate_path(current_path, results);
    current_path.pop_back();
  }
}

std::vector<std::pair<irep_idt, exprt>>
rra_spect::spect::get_abst_lengths_with_expr(const namespacet &ns) const
{
  // helper function to translate a length variable entity path to exprt
  // say the path is [foo(entity), buf(entity), len(entity)]
  // step 1: foo_expr: ID_symbol
  // step 2: member_exprt(foo_expr, buf): ID_member
  // step 3: member_exprt(member_exprt(foo_expr, buf), len)
  auto generate_expr_from_path = [&ns](std::vector<entityt> path) {
    const symbol_tablet &symbol_table = ns.get_symbol_table();
    INVARIANT(path.size() > 0, "The length entity path should not be empty");
    INVARIANT(
      symbol_table.has_symbol(path[0].name),
      "The symbol " + std::string(path[0].name.c_str()) + " should exist");
    exprt current_expr = symbol_table.lookup_ref(path[0].name).symbol_expr();
    for(size_t i = 1; i < path.size(); i++)
    {
      const typet full_type = ns.follow(current_expr.type());
      const struct_typet &struct_type = to_struct_type(full_type);
      struct_typet::componentt component;
      bool component_found = false;
      for(const auto &comp : struct_type.components())
      {
        if(comp.get_name() == path[i].name)
        {
          component = comp;
          component_found = true;
          break;
        }
      }
      INVARIANT(
        component_found,
        std::string(path[i].name.c_str()) + " not found in the component list");
      current_expr = member_exprt(current_expr, component);
    }
    return current_expr;
  };

  // find all length variables with their corresponding path
  // path is the entities we need to visit to find the variable
  // e.g. "buffer", "array", "len" in buffer->array.len
  std::vector<std::vector<entityt>> all_length_paths;
  std::vector<entityt> current_path;
  for(const auto &ent : abst_entities)
  {
    current_path.push_back(*ent.second);
    search_all_lengths_and_generate_path(current_path, all_length_paths);
    current_path.pop_back();
  }

  std::vector<std::pair<irep_idt, exprt>> result;
  for(const auto &path : all_length_paths)
  {
    INVARIANT(path.size() > 0, "The length entity path should not be empty");
    result.push_back(
      std::make_pair(path[0].name, generate_expr_from_path(path)));
  }

  return result;
}

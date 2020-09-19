/*******************************************************************\

Module:

Authors: Murali Talupur talupur@amazon.com
         Lefan Zhang    lefanz@amazon.com

\*******************************************************************/

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

#include "rr_abstraction_spect.h"

rr_abstraction_spect::rr_abstraction_spect(
  std::string filename,
  message_handlert &message_handler)
{
  jsont json;
  parse_json(filename, message_handler, json);
  const auto &json_object = to_json_object(json);
  const auto &json_entries = json_object.find("entries")->second;
  const auto &json_entries_array = to_json_array(json_entries);
  for(auto it = json_entries_array.begin(); it != json_entries_array.end();
      ++it)
  {
    const auto &entry_obj = to_json_object(*it);
    spect spec;
    size_t spec_index = specs.size();
    spec.set_spect_index(spec_index);

    // we assume all entries in json file belong to the same function
    function = entry_obj.find("function")->second.value;
    // insert the entity
    spec.insert_entity(
      entry_obj.find("name")->second.value,
      entry_obj.find("entity")->second.value);
    const auto &json_re_array =
      to_json_array(entry_obj.find("related-entities")->second);
    for(auto it_r = json_re_array.begin(); it_r != json_re_array.end(); ++it_r)
    {
      const auto &related_entity = to_json_object(*it_r);
      spec.insert_entity(
        related_entity.find("name")->second.value,
        related_entity.find("entity")->second.value);
    }

    // initialize the abst functions
    spec.set_abst_func_file(
      get_absolute_path(entry_obj.find("abst-function-file")->second.value));
    spec.set_addition_func(
      to_json_object(entry_obj.find("abst-functions")->second)
        .find("add-abs-conc")
        ->second.value);
    spec.set_minus_func(to_json_object(entry_obj.find("abst-functions")->second)
                          .find("sub-abs-conc")
                          ->second.value);
    spec.set_precise_func(
      to_json_object(entry_obj.find("abst-functions")->second)
        .find("precise-check")
        ->second.value);
    spec.set_abstract_func(
      to_json_object(entry_obj.find("abst-functions")->second)
        .find("abstract-index")
        ->second.value);

    // initialize the shape of this spect
    const auto &json_shape_obj =
      to_json_object(entry_obj.find("shape")->second);
    const auto &json_shape_i_array =
      to_json_array(json_shape_obj.find("indices")->second);
    const auto &json_shape_a_array =
      to_json_array(json_shape_obj.find("assumptions")->second);
    std::vector<irep_idt> indices;
    std::vector<std::string> assumptions;
    for(auto it_i = json_shape_i_array.begin();
        it_i != json_shape_i_array.end();
        ++it_i)
      indices.push_back(to_json_string(*it_i).value);
    for(auto it_a = json_shape_a_array.begin();
        it_a != json_shape_a_array.end();
        ++it_a)
      assumptions.push_back(to_json_string(*it_a).value);
    std::string shape_type =
      to_json_string(json_shape_obj.find("shape-type")->second).value;
    spec.set_shape(indices, assumptions, shape_type);
    specs.push_back(spec);
  }
}

std::vector<std::string>
rr_abstraction_spect::get_abstraction_function_files() const
{
  std::vector<std::string> files;
  for(const spect &s : specs)
  {
    files.push_back(s.get_abst_func_file());
  }
  return files;
}

rr_abstraction_spect::spect rr_abstraction_spect::spect::update_abst_spec(
  irep_idt old_function,
  irep_idt new_function,
  std::unordered_map<irep_idt, irep_idt> _name_pairs) const
{
  // copy the spec into a new one
  spect new_spec(*this);

  // store the entity names in the original spect
  std::vector<irep_idt> abst_array_ids;
  std::vector<irep_idt> abst_index_ids;
  for(const auto &p : abst_arrays)
    abst_array_ids.push_back(p.first);
  for(const auto &p : abst_indices)
    abst_index_ids.push_back(p.first);

  for(const auto &name : abst_array_ids)
  {
    if(
      std::string(abst_arrays.at(name).entity_name().c_str())
        .rfind(old_function.c_str(), 0) ==
      0) // erase the old entity if it's not a global variable
      new_spec.abst_arrays.erase(name);
    if(_name_pairs.find(name) != _name_pairs.end())
    {
      // This array needs to be updated
      new_spec.abst_arrays.insert(
        {_name_pairs[name], entityt(_name_pairs[name])});
    }
  }
  for(const auto &name : abst_index_ids)
  {
    if(
      std::string(abst_indices.at(name).entity_name().c_str())
        .rfind(old_function.c_str(), 0) ==
      0) // erase the old entity if it's not a global variable
      new_spec.abst_indices.erase(name);
    if(_name_pairs.find(name) != _name_pairs.end())
    {
      // This index variable needs to be updated
      new_spec.abst_indices.insert(
        {_name_pairs[name], entityt(_name_pairs[name])});
    }
  }

  return new_spec;
}

rr_abstraction_spect rr_abstraction_spect::update_abst_spec(
  irep_idt old_function,
  irep_idt new_function,
  std::unordered_map<irep_idt, irep_idt> _name_pairs) const
{
  if(function != old_function)
  {
    throw "old rr_abstraction_spect should match the callee";
  }

  rr_abstraction_spect new_abst_spec;
  new_abst_spec.function = new_function;
  for(const auto &spec : specs)
  {
    spect new_spec =
      spec.update_abst_spec(old_function, new_function, _name_pairs);
    if(!spec.compare_shape_only(new_spec))
      throw "updated spect's shape should be the same as the original one";
    new_abst_spec.specs.push_back(new_spec);
  }
  if(specs.size() != new_abst_spec.specs.size())
    throw "updated specs' size should remain the same";
  return new_abst_spec;
}

std::string rr_abstraction_spect::get_entities_string() const
{
  std::string str = "";
  for(const auto &spec : specs)
  {
    for(const auto &ent : spec.get_abst_arrays())
      str += "array: " + std::string(ent.second.entity_name().c_str()) + "\n";
    for(const auto &ent : spec.get_abst_indices())
      str += "index: " + std::string(ent.second.entity_name().c_str()) + "\n";
  }
  return str;
}

void rr_abstraction_spect::print_entities() const
{
  std::cout << get_entities_string();
}

std::vector<exprt>
rr_abstraction_spect::spect::get_assumption_exprs(const namespacet &ns) const
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

std::vector<exprt> rr_abstraction_spect::spect::abst_shapet::get_assumption_exprs(
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

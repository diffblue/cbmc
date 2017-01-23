/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <algorithm>
#include <iterator>

#include <util/symbol.h>
#include <util/symbol_table.h>
#include <util/namespace.h>
#include <util/std_expr.h>
#include <util/std_types.h>
#include <util/vtable.h>

const char ID_virtual_name[] = "virtual_name";

class is_virtual_name_equalt {
  const irep_idt &virtual_name;
public:
  is_virtual_name_equalt(const class_typet::methodt &method) :
      virtual_name(method.get(ID_virtual_name)) {
  }
  bool operator()(const class_typet::methodt &method) const {
    return virtual_name == method.get(ID_virtual_name);
  }
};

class is_name_equalt {
  const irep_idt &name;
public:
  is_name_equalt(const irep_idt &name) :
      name(name) {
  }
  bool operator()(const class_typet::componentt &component) const {
    return name == component.get_name();
  }
};

class java_bytecode_vtable_factoryt
{
  symbol_tablet &symbol_table;
  const std::string &module;
  const namespacet ns;

public:
  bool has_error;

  java_bytecode_vtable_factoryt(symbol_tablet &symbol_table,
      const std::string &module) :
      symbol_table(symbol_table), module(module), ns(symbol_table), has_error(
          false)
  {
  }

  symbolt &get_vt_type_symbol(const class_typet &class_type)
  {
    const std::string &class_name(id2string(class_type.get(ID_name)));
    return symbol_table.lookup(vtnamest::get_type(class_name));
  }

  void create_vtable_symbol(symbolt &result, const class_typet &class_type)
  {
    const std::string &class_name=id2string(class_type.get(ID_name));
    const std::string &base_class_name=id2string(class_type.get(ID_base_name));
    const symbolt &type_symbol(get_vt_type_symbol(class_type));
    result.name = vtnamest::get_table(class_name);
    result.base_name = vtnamest::get_table_base(base_class_name);
    result.pretty_name = result.base_name;
    result.mode = type_symbol.mode;
    result.module = module;
    result.location = type_symbol.location;
    result.type = symbol_typet(type_symbol.name);
    result.is_lvalue = true;
    result.is_state_var = true;
    result.is_static_lifetime = true;
  }

  bool has_component(const class_typet &vtable_type, const irep_idt &ifc_name)
  {
    const class_typet::componentst &comps(vtable_type.components());
    const is_name_equalt pred(ifc_name);
    return std::find_if(comps.begin(), comps.end(), pred) != comps.end();
  }

  void add_vtable_entry(struct_exprt &vtable_value,
      const class_typet &interface, const class_typet &implementor,
      const class_typet::methodt &implementation)
  {
    const class_typet::methodst &methods(interface.methods());
    const is_virtual_name_equalt pred(implementation);
    const class_typet::methodst::const_iterator ifc_method(
        std::find_if(methods.begin(), methods.end(), pred));
    assert(methods.end() != ifc_method);
    symbolt &vtable_type_symbol(get_vt_type_symbol(implementor));
    class_typet &vtable_type(to_class_type(vtable_type_symbol.type));
    const irep_idt &ifc_name(ifc_method->get_name());
    if (has_component(vtable_type, ifc_name)) return;

    struct_typet::componentt entry_component;
    entry_component.set_name(ifc_name);
    entry_component.set_base_name(ifc_method->get_base_name());
    entry_component.type() = pointer_typet(implementation.type());
    vtable_type.components().push_back(entry_component);

    const irep_idt &impl_name(implementation.get_name());
    const symbol_exprt impl_symbol(impl_name, implementation.type());
    const address_of_exprt impl_ref(impl_symbol);
    vtable_value.copy_to_operands(impl_ref);
  }

  const class_typet &get_class_type(const irept &base)
  {
    const typet &type(static_cast<const typet &>(base.find(ID_type)));
    const symbol_typet &symbol_type(to_symbol_type(type));
    const irep_idt &base_class_name(symbol_type.get_identifier());
    assert(symbol_table.has_symbol(base_class_name));
    const symbolt &base_class_symbol(ns.lookup(base_class_name));
    return to_class_type(base_class_symbol.type);
  }

  bool has_method(const irept &base, const class_typet::methodt &method)
  {
    const typet &type(static_cast<const typet &>(base.find(ID_type)));
    const symbol_typet &symbol_type(to_symbol_type(type));
    const irep_idt &base_class_name(symbol_type.get_identifier());
    if (!symbol_table.has_symbol(base_class_name)) return false;
    const symbolt &base_class_symbol(ns.lookup(base_class_name));
    const class_typet &base_class_type(to_class_type(base_class_symbol.type));
    const class_typet::methodst &methods(base_class_type.methods());
    const is_virtual_name_equalt pred(method);
    return std::find_if(methods.begin(), methods.end(), pred) != methods.end();
  }

  void extract_types(
    std::vector<class_typet> &result,
    const irept::subt &types,
    const class_typet::methodt &method)
  {
    for(irept::subt::const_iterator it=types.begin();
        it != types.end(); ++it)
    {
      if (!has_method(*it, method)) continue;
      result.push_back(get_class_type(*it));
    }
  }

  bool is_virtual(const class_typet::methodt &method)
  {
    return method.get_bool(ID_is_virtual)
      && !method.get_bool(ID_constructor);
  }

  void create_base_vtable_entries(
    struct_exprt &vtable_value,
    const class_typet &class_type,
    const class_typet::methodt &method)
  {
    if (!is_virtual(method)) return;
    std::vector<class_typet> bases;
    extract_types(bases, class_type.bases(), method);
    //extract_types(bases, class_type.find(ID_interfaces).get_sub(), method);
    for(const std::vector<class_typet>::value_type &b : bases)
      add_vtable_entry(vtable_value, b, class_type, method);
  }

  void create_vtable_entry(struct_exprt &vtable_value,
      const class_typet &class_type, const class_typet::methodt &method)
  {
    if (!is_virtual(method)) return;
    add_vtable_entry(vtable_value, class_type, class_type, method);
  }

  void set_vtable_value(symbolt &vtable_symbol, const class_typet &class_type,
      struct_exprt &vtable_value) {
    const std::string &class_name(id2string(class_type.get(ID_name)));
    const irep_idt vttype(vtnamest::get_type(class_name));
    vtable_value.type() = symbol_typet(vttype);
    vtable_symbol.value = vtable_value;
  }

  bool is_class_with_vt(const symbolt &symbol)
  {
    if (!symbol.is_type || ID_struct != symbol.type.id()) return false;
    const class_typet &class_type(to_class_type(symbol.type));
    const std::string &class_name(id2string(class_type.get(ID_name)));
    return symbol_table.has_symbol(vtnamest::get_type(class_name));
  }

  void operator()(const irep_idt &symbol_name)
  {
    const symbolt &symbol = symbol_table.lookup(symbol_name);
    if (!is_class_with_vt(symbol)) return;
    const class_typet &class_type(to_class_type(symbol.type));
    const std::string &class_name(id2string(symbol_name));
    if (symbol_table.has_symbol(vtnamest::get_table(class_name))) return;
    symbolt vtable_symbol;
    create_vtable_symbol(vtable_symbol, class_type);
    const class_typet::methodst &methods(class_type.methods());
    struct_exprt vtable_value;
    for (const class_typet::methodst::value_type &m : methods)
      create_base_vtable_entries(vtable_value, class_type, m);
    for (const class_typet::methodst::value_type &m : methods)
      create_vtable_entry(vtable_value, class_type, m);
    set_vtable_value(vtable_symbol, class_type, vtable_value);
    assert(!symbol_table.add(vtable_symbol));
  }
};


/*******************************************************************

 Function: java_bytecode_vtable

 Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool java_bytecode_vtable(
  symbol_tablet &symbol_table,
  const std::string &module)
{
  const symbol_tablet::symbolst &symbols(symbol_table.symbols);
  std::vector<irep_idt> names;
  names.reserve(symbols.size());
  std::transform(symbols.begin(), symbols.end(), std::back_inserter(names),
      [](const std::pair<irep_idt, symbolt> &entry)
      { return entry.first;});
  java_bytecode_vtable_factoryt factory(symbol_table, module);
  std::for_each(names.begin(), names.end(), factory);
  return factory.has_error;
}

namespace
{

void create_vtable_type(const irep_idt &vt_name, symbol_tablet &symbol_table,
    const symbolt &class_symbol) {
  symbolt vt_symb_type;
  vt_symb_type.name = vt_name;
  vt_symb_type.base_name = vtnamest::get_type_base(
      id2string(class_symbol.base_name));
  vt_symb_type.pretty_name = vt_symb_type.base_name;
  vt_symb_type.mode = class_symbol.mode;
  vt_symb_type.module = class_symbol.module;
  vt_symb_type.location = class_symbol.location;
  vt_symb_type.type = struct_typet();
  vt_symb_type.type.set(ID_name, vt_symb_type.name);
  vt_symb_type.is_type = true;
  assert(!symbol_table.add(vt_symb_type));
}

const char ID_isvtptr[] = "is_vtptr";
const char ID_vtable_pointer[] = "@vtable_pointer";

void add_vtable_pointer_member(
  const irep_idt &vt_name,
  symbolt &class_symbol)
{
  struct_typet::componentt comp;

  comp.type()=pointer_typet(symbol_typet(vt_name));
  comp.set_name(ID_vtable_pointer);
  comp.set_base_name(ID_vtable_pointer);
  comp.set_pretty_name(ID_vtable_pointer);
  comp.set(ID_isvtptr, true);

  struct_typet &class_type=to_struct_type(class_symbol.type);
  class_type.components().push_back(comp);
}

}

/*******************************************************************

 Function: create_vtable_symbol

 Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void create_vtable_symbol(
  symbol_tablet &symbol_table,
  const symbolt &class_symbol)
{
  const irep_idt vttype=
    vtnamest::get_type(id2string(class_symbol.name));

  if(!symbol_table.has_symbol(vttype))
    create_vtable_type(vttype, symbol_table, class_symbol);
}

/*******************************************************************

 Function: has_vtable_info

 Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool has_vtable_info(
  const symbol_tablet &symbol_table,
  const symbolt &class_symbol)
{
  return symbol_table.has_symbol(vtnamest::get_type(id2string(class_symbol.name)))
      && to_struct_union_type(class_symbol.type).has_component(ID_vtable_pointer);
}

/*******************************************************************

 Function: create_vtable_pointer

 Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void create_vtable_pointer(symbolt &class_symbol)
{
  const irep_idt vttype=
    vtnamest::get_type(id2string(class_symbol.name));

  add_vtable_pointer_member(vttype, class_symbol);
}

namespace {
const char NAME_SEP = '.';
}

/*******************************************************************

 Function: get_virtual_name

 Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void set_virtual_name(class_typet::methodt &method)
{
  const std::string &name(id2string(method.get(ID_name)));
  const std::string::size_type vname_start(name.find_last_of(NAME_SEP) + 1);
  std::string virtual_name(name.substr(vname_start));
  method.set(ID_virtual_name, virtual_name);
}

namespace {

exprt get_ref(
  const exprt &this_obj,
  const symbol_typet &target_type)
{
  const typet &type(this_obj.type());
  const irep_idt &type_id(type.id());
  if(ID_symbol == type_id)
    return get_ref(address_of_exprt(this_obj), target_type);
  assert(ID_pointer == type_id);
  const typecast_exprt cast(this_obj, pointer_typet(target_type));
  return dereference_exprt(cast, target_type);
}

const char JAVA_NS[] = "java::";
const size_t JAVA_NS_LENGTH(6);
const char CLS_MTD_SEP(':');
const char NSEP('.');

std::string get_full_class_name(const std::string &name) {
  const bool has_prefix(name.find(JAVA_NS) != std::string::npos);
  const std::string::size_type offset(has_prefix ? JAVA_NS_LENGTH : 0);
  const std::string::size_type end(name.find_first_of(CLS_MTD_SEP, offset));
  const std::string::size_type last_sep(name.rfind(NSEP, end));
  return name.substr(0, last_sep);
}
}

/*******************************************************************

 Function: make_vtable_function

 Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt make_vtable_function(
  const exprt &func,
  const exprt &this_obj)
{
  const irep_idt &func_name(func.get(ID_identifier));
  const std::string class_id(get_full_class_name(id2string(func_name)));

  // TODO: Handle unavailable models!
  if (class_id.find("java.") != std::string::npos) {
    // When translating a single java_bytecode_parse_treet, we don't know
    // which classes will eventually be available yet. If we could provide
    // access to the class loader here, we know which classes have been
    // loaded successfully. For classes which have not been loaded, returning
    // "func" is equivalent to an unimplemented function.
    return func;
  }

  const symbol_typet vtable_type(vtnamest::get_type(class_id));
  const pointer_typet vt_ptr_type(vtable_type);
  const symbol_typet target_type(class_id);
  const exprt this_ref(get_ref(this_obj, target_type));
  const typet ref_type(this_ref.type());
  const member_exprt vtable_member(this_ref, ID_vtable_pointer, vt_ptr_type);
  const dereference_exprt vtable(vtable_member, vtable_type); // TODO: cast?
  const pointer_typet func_ptr_type(func.type());
  const member_exprt func_ptr(vtable, func_name, func_ptr_type);
  const dereference_exprt virtual_func(func_ptr, func.type());
  return virtual_func;
}

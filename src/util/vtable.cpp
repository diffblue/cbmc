#include <util/std_types.h>
#include <util/vtable.h>

namespace {
const char VT_NS[] = "virtual_table::";
const char VT_SEP = '@';
const char ID_virtual_name[] = "virtual_name";
const char NS_SEP[] = "::";
}

const char vtnamest::VT_PTR[] = "@vtable_pointer";

std::string vtnamest::get_type(const std::string &class_name) {
  return VT_NS + class_name;
}

std::string vtnamest::get_table(const std::string &class_name) {
  return get_type(class_name) + VT_SEP + class_name;
}

std::string vtnamest::get_table(const typet &class_type) {
  const irep_idt &type_id(class_type.id());
  if (ID_pointer == type_id) return get_table(class_type.subtype());
  assert(ID_symbol == type_id);
  const irep_idt &id(to_symbol_type(class_type).get_identifier());
  return get_table(id2string(id));
}

std::string vtnamest::get_table(const exprt &this_obj) {
  return get_table(this_obj.type());
}


std::string vtnamest::get_table_base(
    const std::string &class_base_name) {
  return get_type_base(class_base_name) + VT_SEP + class_base_name;
}

std::string vtnamest::get_type(const typet &class_type) {
  const irep_idt &type_id(class_type.id());
  if (ID_pointer == type_id) return get_type(class_type.subtype());
  assert(ID_symbol == type_id);
  const irep_idt &id(to_symbol_type(class_type).get_identifier());
  return get_type(id2string(id));
}

std::string vtnamest::get_type(const exprt &this_obj) {
  return get_type(this_obj.type());
}

std::string vtnamest::get_type_base(
    const std::string &class_base_name) {
  return VT_NS + class_base_name;
}

std::string vtnamest::get_pointer(const std::string &class_name) {
  return class_name + NS_SEP + std::string(VT_PTR);
}

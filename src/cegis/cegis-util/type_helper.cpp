#include <util/std_types.h>
#include <util/symbol_table.h>

#define TAG_PREFIX "tag-"

const typet &replace_struct_by_symbol_type(const symbol_tablet &st,
    const typet &type)
{
  const irep_idt &type_id=type.id();
  if (ID_struct != type_id && ID_incomplete_struct != type_id
      && ID_union != type_id && ID_incomplete_union != type_id) return type;
  std::string tag(TAG_PREFIX);
  tag+=id2string(to_struct_union_type(type).get_tag());
  return st.lookup(tag).type;
}

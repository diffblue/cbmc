#include <algorithm>

#include <util/std_types.h>
#include <util/symbol_table.h>
#include <util/type_eq.h>
#include <util/namespace.h>

#include <cegis/cegis-util/type_helper.h>

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

namespace
{
bool instanceof(const typet &lhs, const typet &rhs, const namespacet &ns)
{
  if (type_eq(lhs, rhs, ns)) return true;
  assert(ID_class == lhs.id());
  const class_typet &lhs_class=to_class_type(lhs);
  const irept::subt &bases=lhs_class.bases();
  for (const irept &base : bases)
  {
    const typet &type=static_cast<const typet &>(base.find(ID_type));
    if (instanceof(ns.follow(type), rhs, ns)) return true;
  }
  return false;
}
}

bool instanceof(const symbol_tablet &st, const typet &lhs, const typet &rhs)
{
  const namespacet ns(st);
  const typet &resolved_lhs=ns.follow(lhs);
  const typet &resolved_rhs=ns.follow(rhs);
  if (ID_class != resolved_lhs.id() || ID_class != resolved_rhs.id())
    return type_eq(resolved_lhs, resolved_rhs, ns);
  return instanceof(resolved_lhs, resolved_rhs, ns);
}

instanceof_anyt::instanceof_anyt(const symbol_tablet &st,
    const std::set<typet> &types) :
    st(st), types(types)
{
}

bool instanceof_anyt::operator ()(const typet &type) const
{
  if (types.empty()) return true;
  return types.end()
      != std::find_if(types.begin(), types.end(),
          [this, &type](const typet &rhs)
          { return instanceof(st, type, rhs);});
}

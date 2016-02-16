#include <util/message.h>
#include <util/symbol_table.h>
#include <linking/linking.h>

namespace {
class java_bytecode_load_classt {
  symbol_tablet &dest_symbol_table;
  symbol_tablet &new_symbol_table;
  message_handlert &message_handler;

  static bool is_incomplete(const symbolt &symbol) {
    if (!symbol.is_type) return false;
    return symbol.type.get_bool(ID_incomplete_class);
  }

  void mark_for_erasure(std::vector<irep_idt> &ids,
      const std::pair<const irep_idt, symbolt> &named_symbol,
      const symbol_tablet &src, symbol_tablet &dst) {
    if (!is_incomplete(named_symbol.second)) return;
    const irep_idt &name(named_symbol.first);
    if (!src.has_symbol(name)) return;
    ids.push_back(name);
  }

  void erase_symbols(symbol_tablet &st, std::vector<irep_idt> &ids) {
    for (typeof(ids.begin()) it(ids.begin()); it != ids.end(); ++it) {
      st.remove(*it);
    }
    ids.clear();
  }
public:
  java_bytecode_load_classt(symbol_tablet &dest_symbol_table,
      symbol_tablet &new_symbol_table, message_handlert &message_handler) :
      dest_symbol_table(dest_symbol_table), new_symbol_table(new_symbol_table), message_handler(
          message_handler) {
  }

  bool operator()() {
    const symbol_tablet::symbolst &src(new_symbol_table.symbols);
    std::vector<irep_idt> ids;
    for (typeof(src.begin()) it(src.begin()); it != src.end(); ++it)
      mark_for_erasure(ids, *it, dest_symbol_table, new_symbol_table);
    erase_symbols(new_symbol_table, ids);
    const symbol_tablet::symbolst &dst(dest_symbol_table.symbols);
    for (typeof(dst.begin()) it(dst.begin()); it != dst.end(); ++it)
      mark_for_erasure(ids, *it, new_symbol_table, dest_symbol_table);
    erase_symbols(dest_symbol_table, ids);
    return linking(dest_symbol_table, new_symbol_table, message_handler);
  }
};
}

bool java_bytecode_load_class(symbol_tablet &dst, symbol_tablet &src,
    message_handlert &msg_handler) {
  java_bytecode_load_classt load_class(dst, src, msg_handler);
  return load_class();
}

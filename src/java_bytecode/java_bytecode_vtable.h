#ifndef CPROVER_JAVA_BYTECODE_VTABLE_H
#define CPROVER_JAVA_BYTECODE_VTABLE_H

#include <util/std_types.h>

bool java_bytecode_vtable(class symbol_tablet &symbol_table,
    const std::string &module);

void create_vtable_type_and_pointer(symbol_tablet &symbol_table,
    class symbolt &class_symbol);

code_assignt make_vtable_assignment(const symbol_tablet &symbol_table,
    const exprt &func);

exprt make_vtable_function(const exprt &function, const exprt &this_obj);

void set_virtual_name(class_typet::methodt &method);

#endif /* CPROVER_JAVA_BYTECODE_VTABLE_H */

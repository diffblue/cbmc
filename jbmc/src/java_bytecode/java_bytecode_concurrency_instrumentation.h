/*******************************************************************\

Module: Java Convert Thread blocks

Author: Kurt Degiogrio, kurt.degiorgio@diffblue.com

\*******************************************************************/
#ifndef CPROVER_JAVA_BYTECODE_JAVA_BYTECODE_CONCURRENCY_INSTRUMENTATION_H
#define CPROVER_JAVA_BYTECODE_JAVA_BYTECODE_CONCURRENCY_INSTRUMENTATION_H

class message_handlert;
class symbol_table_baset;

void convert_threadblock(symbol_table_baset &symbol_table);
void convert_synchronized_methods(
  symbol_table_baset &symbol_table,
  message_handlert &message_handler);

#endif

/*******************************************************************\

Module: Java Static Initializers

Author: Chris Smowton, chris.smowton@diffblue.com

\*******************************************************************/

#ifndef CPROVER_JAVA_BYTECODE_SYNTHETIC_METHODS_MAP_H
#define CPROVER_JAVA_BYTECODE_SYNTHETIC_METHODS_MAP_H

enum class synthetic_method_typet
{
  STATIC_INITIALIZER_WRAPPER,
  STUB_CLASS_STATIC_INITIALIZER
};

typedef std::unordered_map<irep_idt, synthetic_method_typet, irep_id_hash>
  synthetic_methods_mapt;

#endif

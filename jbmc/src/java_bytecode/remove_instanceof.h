/*******************************************************************\

Module: Remove Instance-of Operators

Author: Chris Smowton, chris.smowton@diffblue.com

\*******************************************************************/

/// \file
/// Remove Instance-of Operators
///
/// Java has an operator called `instanceof`, which is used to check if an
/// instance of a class is of a particular type. For example given that `A` and
/// `B` are the identifiers of classes, which directly extend Object. If the
/// following example java code is executed -
/// ```java
/// Object a = new A();
/// boolean x = a instanceof A; // true
/// boolean y = a instanceof B; // false
/// ```
/// Then, `x` will be set to `true` and `y` will be set to `false`.
///
/// `instanceof` also works with inheritance. Given classes `C` and `D`, where
/// `C` extends from `Object` and `D` extends `C`. If the following example java
/// code is executed -
/// ```java
/// Object c = new C();
/// Object d = new D();
/// boolean b1 = c instanceof C; // true
/// boolean b2 = c instanceof D; // false
/// boolean b3 = d instanceof C; // true
/// boolean b4 = d instanceof D; // true
/// ```
/// Then, `b1` will be `true`, `b2` will be `false`, `b3` will be `true` and
/// `b4` will be `true`.
///
/// `instanceof` has its own instruction type in the java bytecode. We need to
/// rewrite it in terms of other, more fundamental operations in order to
/// analyse it. This operation is referred to as "lowering" or in this
/// specific case - `remove_instanceof`.
///
/// For a simple example where class `A` extends `Object` and no classes extend
/// `A`, the expression `e instanceof A` needs to be lowered to an expression
/// equivalent to `e == null ? false : e->@class_identifier == "A"`. The null
/// case needs to be taken into account first, as we can't lookup the value of
/// a `@class_identifier` field in a null pointer. Note that according to the
/// Java specification, `null` is not an instance of any type.
///
/// For an example with inheritance where class `D` extends `C` and `C` extends
/// `Object`, then `e instanceof C` needs to be lowered to an expression
/// equivalent to `e == null ? false : (e->@class_identifier == "C" ||
/// e->@class_identifier == "D")`. To lower `e instanceof C` correctly, we need
/// to take into account each of the classes extends from `C`. Working out what
/// classes extend a given class type is performed using an instance of the
/// `class_hierarchyt` class.
///
/// In terms of the goto program, the `instanceof` operator is identified in the
/// expression tree, based on the `exprt.id()` being `ID_java_instance_of`. The
/// left hand side of the operator must be a pointer and the right hand side
/// must be a type.
///
/// The lowered form has a refinement to help with null pointer analysis later
/// on. Instead of dereferencing the pointer to get `@class_identifier` in each
/// comparision, it is dereferenced a single time and the result is reused. This
/// is easier to analyse for null pointers, because there is only a single
/// dereference to consider. So the constructed program takes the form -
/// ```cpp
/// if(expr == null)
///   instanceof_result = false;
/// else
///   string class_identifier_tmpX = expr->@class_identifier;
///   instanceof_result =
///     class_identifier_tmpX == "C" ||
///     class_identifier_tmpX == "D";
/// ```
/// Where the `X` in `class_identifier_tmp` is a number which makes the
/// identifier unique.

#ifndef CPROVER_JAVA_BYTECODE_REMOVE_INSTANCEOF_H
#define CPROVER_JAVA_BYTECODE_REMOVE_INSTANCEOF_H

#include <goto-programs/class_hierarchy.h>
#include <goto-programs/goto_functions.h>
#include <goto-programs/goto_model.h>

#include <util/message.h>
#include <util/symbol_table.h>

void remove_instanceof(
  const irep_idt &function_identifier,
  goto_programt::targett target,
  goto_programt &goto_program,
  symbol_table_baset &symbol_table,
  const class_hierarchyt &class_hierarchy,
  message_handlert &);

void remove_instanceof(
  const irep_idt &function_identifier,
  goto_functionst::goto_functiont &function,
  symbol_table_baset &symbol_table,
  const class_hierarchyt &class_hierarchy,
  message_handlert &);

void remove_instanceof(
  goto_functionst &goto_functions,
  symbol_table_baset &symbol_table,
  const class_hierarchyt &class_hierarchy,
  message_handlert &);

void remove_instanceof(
  goto_modelt &model,
  const class_hierarchyt &class_hierarchy,
  message_handlert &);

#endif

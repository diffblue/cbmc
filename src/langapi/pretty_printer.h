/*******************************************************************\

Module: Generic expression / type pretty-printer

Author: Chris Smowton, chris.smowton@diffblue.com

\*******************************************************************/

/// \file
/// Generic expression / type pretty-printer

#ifndef CPROVER_LANGAPI_PRETTY_PRINTER_H
#define CPROVER_LANGAPI_PRETTY_PRINTER_H

#include <util/lispirep.h>
#include <util/lispexpr.h>
#include <util/expr.h>
#include <util/type.h>
// Borrow MetaString, a simple string-escaping routine
#include <ansi-c/c_misc.h>

#include <cassert>

/*
 * Interface to an expression and/or type pretty-printer.
 * The convert(...) routines should pretty-print the expressions
 * they know how to deal with, and defer to next_pretty_printer
 * for those they can't handle, and top_pretty_printer for
 * subexpressions (whether it understands them or not).
 * Per default they always defer.
 * See `util/language_util.h` and particularly
 * `register_global_pretty_printer` for detail on how these are used.
 */
class pretty_printert
{
 public:
  pretty_printert():
  next_pretty_printer(nullptr),
  top_pretty_printer(nullptr)
  {}

  virtual ~pretty_printert() {}

  virtual std::string convert(const typet &src)
  {
    assert(next_pretty_printer);
    return next_pretty_printer->convert(src);
  }
  virtual std::string convert(const exprt &src)
  {
    assert(next_pretty_printer);
    return next_pretty_printer->convert(src);
  }

  void set_next_pretty_printer(
    pretty_printert *next)
  {
    next_pretty_printer=next;
  }
  void set_top_pretty_printer(
    pretty_printert *top)
  {
    top_pretty_printer=top;
  }

 protected:
  pretty_printert *next_pretty_printer;
  pretty_printert *top_pretty_printer;
};

class norep_pretty_printert:public pretty_printert
{
 public:
  std::string convert(const typet &src) override
  {
    lispexprt lisp;
    irep2lisp(src, lisp);
    return "irep(\""+MetaString(lisp.expr2string())+"\")";
  }

  std::string convert(const exprt &src) override
  {
    lispexprt lisp;
    irep2lisp(src, lisp);
    return "irep(\""+MetaString(lisp.expr2string())+"\")";
  }
};

#endif

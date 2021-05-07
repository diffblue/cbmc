/*******************************************************************\

Module: Taint Parser

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Taint Parser

#ifndef CPROVER_GOTO_ANALYZER_TAINT_PARSER_H
#define CPROVER_GOTO_ANALYZER_TAINT_PARSER_H

#include <string>
#include <list>
#include <iosfwd>

#include <util/irep.h>

class message_handlert;

class taint_parse_treet
{
public:
  class rulet
  {
  public:
    enum { SOURCE, SINK, SANITIZER } kind;
    enum { THIS, PARAMETER, RETURN_VALUE } where;

    bool is_source() const
    {
      return kind==SOURCE;
    }

    bool is_sink() const
    {
      return kind==SINK;
    }

    bool is_sanitizer() const
    {
      return kind==SANITIZER;
    }

    irep_idt id;
    irep_idt function_identifier;
    irep_idt taint;
    unsigned parameter_number; // the first one is '1'
    std::string message;

    void output(std::ostream &) const;

    rulet():
      parameter_number(0)
      // The other class members are initialized by taint_parser().
    {
    }
  };

  typedef std::list<rulet> rulest;
  rulest rules;

  void output(std::ostream &) const;
};

bool taint_parser(
  const std::string &taint_file_name,
  taint_parse_treet &,
  message_handlert &);

#endif // CPROVER_GOTO_ANALYZER_TAINT_PARSER_H

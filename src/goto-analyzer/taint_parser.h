/*******************************************************************\

Module: Taint Parser

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_TAINT_PARSER_H
#define CPROVER_TAINT_PARSER_H

#include <string>
#include <list>
#include <iosfwd>

#include <util/message.h>
#include <util/irep.h>

class taint_parse_treet
{
public:
  class rulet
  {
  public:
    enum { SOURCE, SINK, SANITIZER } kind;
    enum { THIS, PARAMETER, RETURN_VALUE } where;
    
    inline bool is_source() const
    {
      return kind==SOURCE;
    }

    inline bool is_sink() const
    {
      return kind==SINK;
    }

    inline bool is_sanitizer() const
    {
      return kind==SANITIZER;
    }

    irep_idt id;
    irep_idt function_identifier;
    irep_idt taint;
    unsigned parameter_number; // the frist one is '1'
    std::string message;
    
    void output(std::ostream &) const;
    
    inline rulet():parameter_number(0)
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

#endif

/*******************************************************************\

Module: Horn-clause Encoding

Author: Saswat Padhi

\*******************************************************************/

/// \file
/// Horn-clause Encoding

#ifndef CPROVER_GOTO_INSTRUMENT_HORN_ENCODING_H
#define CPROVER_GOTO_INSTRUMENT_HORN_ENCODING_H

#include <goto-programs/goto_model.h>

#include <solvers/decision_procedure.h>
#include <solvers/smt2/smt2_conv.h>

#include <util/mathematical_expr.h>
#include <util/string_utils.h>

#include <fstream>
#include <iostream>
#include <vector>

using std::function;
using std::ostream;
using std::string;
using std::vector;

enum horn_formatt
{
  ASCII,
  SMT2
};

class encoding_targett
{
public:
  virtual void comment(const string &str)
  {
    *_comment_stream << str;
  }

  virtual void comment_break(char c = '-')
  {
    *_comment_stream << string(80, c) << "\n";
    _comment_stream->flush();
  }

  virtual ostream &comment_stream()
  {
    return *_comment_stream;
  };

  virtual void output(const string &str)
  {
    *_output_stream << str;
  }

  virtual void output_exprt(const exprt &e)
  {
  }

  virtual void output_break(char c = '-')
  {
    *_output_stream << string(80, c) << "\n";
    _output_stream->flush();
  }

  virtual ostream &output_stream()
  {
    return *_output_stream;
  }

  encoding_targett &
  operator<<(const function<void(encoding_targett &)> &encoder)
  {
    encoder(*this);
    return *this;
  }

  ~encoding_targett()
  {
    for(const auto &p : to_be_freed)
      delete p;
  }

protected:
  encoding_targett(ostream *__out, ostream *__comm)
    : _output_stream(__out), _comment_stream(__comm)
  {
    if(!_comment_stream)
    {
      _comment_stream = new std::ofstream("/dev/null", std::ofstream::out);
      to_be_freed.push_back(_comment_stream);
    }
    if(!_output_stream)
    {
      _output_stream = new std::ofstream("/dev/null", std::ofstream::out);
      to_be_freed.push_back(_output_stream);
    }
  }

  ostream *_output_stream;
  ostream *_comment_stream;
  vector<ostream *> to_be_freed;
};

class smt2_encoding_targett : public encoding_targett
{
public:
  smt2_encoding_targett(ostream &__out, const namespacet &__ns)
    : encoding_targett(&__out, nullptr),
      smt2_conv(__ns, "", "", "HORN", smt2_convt::solvert::Z3, __out)
  {
    smt2_conv.use_datatypes = true;
  }

  void comment_break(char c = '-') override
  {
    *_comment_stream << ";\n";
    _comment_stream->flush();
  }

  void comment(const string &str) override
  {
    *_comment_stream << "; " << str;
  }

  void output_exprt(const exprt &e) override
  {
    smt2_conv.set_to_true(e);
  }

  void output_break(char c = '-') override
  {
    *_output_stream << "\n";
    _output_stream->flush();
  }

protected:
  smt2_convt smt2_conv;
};

class text_encoding_targett : public encoding_targett
{
public:
  explicit text_encoding_targett(ostream &__out)
    : encoding_targett(&__out, &__out)
  {
  }

  explicit text_encoding_targett(ostream &__out, ostream &__comment)
    : encoding_targett(&__out, &__comment)
  {
  }

  void comment(const string &str) override
  {
    *_comment_stream << "Comment: " << str;
  }
};

void horn_encoding(const goto_modelt &, horn_formatt, ostream &);

void horn_encoding(const goto_modelt &, ostream &,
        bool mem, bool deref_check, bool dump_cfg);

#endif // CPROVER_GOTO_INSTRUMENT_HORN_ENCODING_H

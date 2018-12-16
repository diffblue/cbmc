/*******************************************************************\

Module: SMT2 Solver that uses boolbv and the default SAT solver

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "smt2_parser.h"

#include "smt2_format.h"

#include <fstream>
#include <iostream>

#include <util/message.h>
#include <util/namespace.h>
#include <util/replace_symbol.h>
#include <util/simplify_expr.h>
#include <util/symbol_table.h>

#include <solvers/sat/satcheck.h>
#include <solvers/flattening/boolbv.h>

class smt2_solvert:public smt2_parsert
{
public:
  smt2_solvert(std::istream &_in, decision_proceduret &_solver)
    : smt2_parsert(_in), solver(_solver), status(NOT_SOLVED)
  {
  }

protected:
  decision_proceduret &solver;

  void command(const std::string &) override;
  void define_constants();
  void expand_function_applications(exprt &);

  std::set<irep_idt> constants_done;

  enum
  {
    NOT_SOLVED,
    SAT,
    UNSAT
  } status;
};

void smt2_solvert::define_constants()
{
  for(const auto &id : id_map)
  {
    if(id.second.type.id() == ID_mathematical_function)
      continue;

    if(id.second.definition.is_nil())
      continue;

    const irep_idt &identifier = id.first;

    // already done?
    if(constants_done.find(identifier)!=constants_done.end())
      continue;

    constants_done.insert(identifier);

    exprt def = id.second.definition;
    expand_function_applications(def);
    solver.set_to_true(
      equal_exprt(symbol_exprt(identifier, id.second.type), def));
  }
}

void smt2_solvert::expand_function_applications(exprt &expr)
{
  for(exprt &op : expr.operands())
    expand_function_applications(op);

  if(expr.id()==ID_function_application)
  {
    auto &app=to_function_application_expr(expr);

    // look it up
    irep_idt identifier=app.function().get_identifier();
    auto f_it=id_map.find(identifier);

    if(f_it!=id_map.end())
    {
      const auto &f=f_it->second;

      DATA_INVARIANT(f.type.id()==ID_mathematical_function,
        "type of function symbol must be mathematical_function_type");

      const auto f_type=
        to_mathematical_function_type(f.type);

      const auto &domain = f_type.domain();

      DATA_INVARIANT(
        domain.size() == app.arguments().size(),
        "number of function parameters");

      replace_symbolt replace_symbol;

      std::map<irep_idt, exprt> parameter_map;
      for(std::size_t i = 0; i < domain.size(); i++)
      {
        const symbol_exprt s(f.parameters[i], domain[i]);
        replace_symbol.insert(s, app.arguments()[i]);
      }

      exprt body=f.definition;
      replace_symbol(body);
      expand_function_applications(body);
      expr=body;
    }
  }
}

void smt2_solvert::command(const std::string &c)
{
  {
    if(c == "assert")
    {
      exprt e = expression();
      if(e.is_not_nil())
      {
        expand_function_applications(e);
        solver.set_to_true(e);
      }
    }
    else if(c == "check-sat")
    {
      // add constant definitions as constraints
      define_constants();

      switch(solver())
      {
      case decision_proceduret::resultt::D_SATISFIABLE:
        std::cout << "sat\n";
        status = SAT;
        break;

      case decision_proceduret::resultt::D_UNSATISFIABLE:
        std::cout << "unsat\n";
        status = UNSAT;
        break;

      case decision_proceduret::resultt::D_ERROR:
        std::cout << "error\n";
        status = NOT_SOLVED;
      }
    }
    else if(c == "check-sat-assuming")
    {
      throw error("not yet implemented");
    }
    else if(c == "display")
    {
      // this is a command that Z3 appears to implement
      exprt e = expression();
      if(e.is_not_nil())
        std::cout << smt2_format(e) << '\n';
    }
    else if(c == "get-value")
    {
      std::vector<exprt> ops;

      if(next_token() != OPEN)
        throw error("get-value expects list as argument");

      while(peek() != CLOSE && peek() != END_OF_FILE)
        ops.push_back(expression()); // any term

      if(next_token() != CLOSE)
        throw error("get-value expects ')' at end of list");

      if(status != SAT)
        throw error("model is not available");

      std::vector<exprt> values;
      values.reserve(ops.size());

      for(const auto &op : ops)
      {
        if(op.id() != ID_symbol)
          throw error("get-value expects symbol");

        const auto &identifier = to_symbol_expr(op).get_identifier();

        const auto id_map_it = id_map.find(identifier);

        if(id_map_it == id_map.end())
          throw error() << "unexpected symbol `" << identifier << '\'';

        const exprt value = solver.get(op);

        if(value.is_nil())
          throw error() << "no value for `" << identifier << '\'';

        values.push_back(value);
      }

      std::cout << '(';

      for(std::size_t op_nr = 0; op_nr < ops.size(); op_nr++)
      {
        if(op_nr != 0)
          std::cout << "\n ";

        std::cout << '(' << smt2_format(ops[op_nr]) << ' '
                  << smt2_format(values[op_nr]) << ')';
      }

      std::cout << ")\n";
    }
    else if(c == "echo")
    {
      if(next_token() != STRING_LITERAL)
        throw error("expected string literal");

      std::cout << smt2_format(constant_exprt(buffer, string_typet())) << '\n';
    }
    else if(c == "get-assignment")
    {
      // print satisfying assignment for all named expressions

      if(status != SAT)
        throw error("model is not available");

      bool first = true;

      std::cout << '(';
      for(const auto &named_term : named_terms)
      {
        const symbol_tablet symbol_table;
        const namespacet ns(symbol_table);
        const auto value =
          simplify_expr(solver.get(named_term.second.term), ns);

        if(value.is_constant())
        {
          if(first)
            first = false;
          else
            std::cout << '\n' << ' ';

          std::cout << '(' << smt2_format(named_term.second.name) << ' '
                    << smt2_format(value) << ')';
        }
      }
      std::cout << ')' << '\n';
    }
    else if(c == "get-model")
    {
      // print a model for all identifiers

      if(status != SAT)
        throw error("model is not available");

      const symbol_tablet symbol_table;
      const namespacet ns(symbol_table);

      bool first = true;

      std::cout << '(';
      for(const auto &id : id_map)
      {
        const symbol_exprt name(id.first, id.second.type);
        const auto value = simplify_expr(solver.get(name), ns);

        if(value.is_not_nil())
        {
          if(first)
            first = false;
          else
            std::cout << '\n' << ' ';

          std::cout << "(define-fun " << smt2_format(name) << ' ';

          if(id.second.type.id() == ID_mathematical_function)
            throw error("models for functions unimplemented");
          else
            std::cout << "() " << smt2_format(id.second.type);

          std::cout << ' ' << smt2_format(value) << ')';
        }
      }
      std::cout << ')' << '\n';
    }
    else if(c == "simplify")
    {
      // this is a command that Z3 appears to implement
      exprt e = expression();
      if(e.is_not_nil())
      {
        const symbol_tablet symbol_table;
        const namespacet ns(symbol_table);
        exprt e_simplified = simplify_expr(e, ns);
        std::cout << smt2_format(e) << '\n';
      }
    }
#if 0
    // TODO:
    | ( declare-const hsymboli hsorti )
    | ( declare-datatype hsymboli hdatatype_deci)
    | ( declare-datatypes ( hsort_deci n+1 ) ( hdatatype_deci n+1 ) )
    | ( declare-fun hsymboli ( hsorti ??? ) hsorti )
    | ( declare-sort hsymboli hnumerali )
    | ( define-fun hfunction_def i )
    | ( define-fun-rec hfunction_def i )
    | ( define-funs-rec ( hfunction_deci n+1 ) ( htermi n+1 ) )
    | ( define-sort hsymboli ( hsymboli ??? ) hsorti )
    | ( get-assertions )
    | ( get-info hinfo_flag i )
    | ( get-option hkeywordi )
    | ( get-proof )
    | ( get-unsat-assumptions )
    | ( get-unsat-core )
    | ( pop hnumerali )
    | ( push hnumerali )
    | ( reset )
    | ( reset-assertions )
    | ( set-info hattributei )
    | ( set-option hoptioni )
#endif
    else
      smt2_parsert::command(c);
  }
}

class smt2_message_handlert : public message_handlert
{
public:
  void print(unsigned level, const std::string &message) override
  {
    message_handlert::print(level, message);

    if(level < 4) // errors
      std::cout << "(error \"" << message << "\")\n";
    else
      std::cout << "; " << message << '\n';
  }

  void print(unsigned level, const xmlt &xml) override
  {
  }

  void print(unsigned level, const jsont &json) override
  {
  }

  void flush(unsigned) override
  {
    std::cout << std::flush;
  }
};

int solver(std::istream &in)
{
  symbol_tablet symbol_table;
  namespacet ns(symbol_table);

  smt2_message_handlert message_handler;
  messaget message(message_handler);

  // this is our default verbosity
  message_handler.set_verbosity(messaget::M_STATISTICS);

  satcheckt satcheck;
  boolbvt boolbv(ns, satcheck);
  satcheck.set_message_handler(message_handler);
  boolbv.set_message_handler(message_handler);

  smt2_solvert smt2_solver(in, boolbv);
  smt2_solver.set_message_handler(message_handler);
  bool error_found = false;

  while(!smt2_solver.exit)
  {
    try
    {
      smt2_solver.parse();
    }
    catch(const smt2_solvert::smt2_errort &error)
    {
      smt2_solver.skip_to_end_of_list();
      error_found = true;
      messaget message(message_handler);
      message.error().source_location.set_line(error.get_line_no());
      message.error() << error.what() << messaget::eom;
    }
    catch(const analysis_exceptiont &error)
    {
      smt2_solver.skip_to_end_of_list();
      error_found = true;
      messaget message(message_handler);
      message.error() << error.what() << messaget::eom;
    }
  }

  if(error_found)
    return 20;
  else
    return 0;
}

int main(int argc, const char *argv[])
{
  if(argc==1)
    return solver(std::cin);

  if(argc!=2)
  {
    std::cerr << "usage: smt2_solver file\n";
    return 1;
  }

  std::ifstream in(argv[1]);
  if(!in)
  {
    std::cerr << "failed to open " << argv[1] << '\n';
    return 1;
  }

  return solver(in);
}

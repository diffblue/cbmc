/*******************************************************************\

Module: SMT2 Solver that uses boolbv and the default SAT solver

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <fstream>
#include <iostream>

#include "smt2_parser.h"

#include <util/namespace.h>
#include <util/symbol_table.h>
#include <util/cout_message.h>
#include <util/simplify_expr.h>
#include <util/replace_symbol.h>

#include <solvers/sat/satcheck.h>
#include <solvers/flattening/boolbv.h>

class smt2_solvert:public smt2_parsert
{
public:
  smt2_solvert(
    std::istream &_in,
    decision_proceduret &_solver):
    smt2_parsert(_in),
    solver(_solver)
  {
  }

protected:
  decision_proceduret &solver;

  void command(const std::string &) override;
  void define_constants(const exprt &);
  void expand_function_applications(exprt &);

  id_sett constants_done;
};

void smt2_solvert::define_constants(const exprt &expr)
{
  for(const auto &op : expr.operands())
    define_constants(op);

  if(expr.id()==ID_symbol)
  {
    irep_idt identifier=to_symbol_expr(expr).get_identifier();

    // already done?
    if(constants_done.find(identifier)!=constants_done.end())
      return;

    constants_done.insert(identifier);

    auto f_it=id_map.find(identifier);

    if(f_it!=id_map.end())
    {
      const auto &f=f_it->second;

      if(f.type.id()!=ID_mathematical_function &&
         f.definition.is_not_nil())
      {
        exprt def=f.definition;
        expand_function_applications(def);
        define_constants(def); // recursive!
        solver.set_to_true(equal_exprt(expr, def));
      }
    }
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

      DATA_INVARIANT(f_type.domain().size()==
                     app.arguments().size(),
                     "number of function parameters");

      replace_symbolt replace_symbol;

      std::map<irep_idt, exprt> parameter_map;
      for(std::size_t i=0; i<f_type.domain().size(); i++)
      {
        const irep_idt p_identifier=
          f_type.domain()[i].get_identifier();

        replace_symbol.insert(p_identifier, app.arguments()[i]);
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
  try
  {
    if(c=="assert")
    {
      exprt e=expression();
      if(e.is_not_nil())
      {
        expand_function_applications(e);
        define_constants(e);
        solver.set_to_true(e);
      }
    }
    else if(c=="check-sat")
    {
      switch(solver())
      {
      case decision_proceduret::resultt::D_SATISFIABLE:
        std::cout << "sat\n";
        break;

      case decision_proceduret::resultt::D_UNSATISFIABLE:
        std::cout << "unsat\n";
        break;

      case decision_proceduret::resultt::D_ERROR:
        std::cout << "error\n";
      }
    }
    else if(c=="check-sat-assuming")
    {
      std::cout << "not yet implemented\n";
    }
    else if(c=="display")
    {
      // this is a command that Z3 appears to implement
      exprt e=expression();
      if(e.is_not_nil())
      {
        std::cout << e.pretty() << '\n'; // need to do an 'smt2_format'
      }
    }
    else if(c=="simplify")
    {
      // this is a command that Z3 appears to implement
      exprt e=expression();
      if(e.is_not_nil())
      {
        const symbol_tablet symbol_table;
        const namespacet ns(symbol_table);
        exprt e_simplified=simplify_expr(e, ns);
        std::cout << e.pretty() << '\n'; // need to do an 'smt2_format'
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
    | ( echo hstringi )
    | ( exit )
    | ( get-assertions )
    | ( get-assignment )
    | ( get-info hinfo_flag i )
    | ( get-model )
    | ( get-option hkeywordi )
    | ( get-proof )
    | ( get-unsat-assumptions )
    | ( get-unsat-core )
    | ( get-value ( htermi + ) )
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
  catch(const char *error)
  {
    std::cout << "error: " << error << '\n';
  }
  catch(const std::string &error)
  {
    std::cout << "error: " << error << '\n';
  }
}

int solver(std::istream &in)
{
  symbol_tablet symbol_table;
  namespacet ns(symbol_table);

  console_message_handlert message_handler;
  messaget message(message_handler);

  // this is our default verbosity
  message_handler.set_verbosity(messaget::M_STATISTICS);

  satcheckt satcheck;
  boolbvt boolbv(ns, satcheck);
  satcheck.set_message_handler(message_handler);
  boolbv.set_message_handler(message_handler);

  smt2_solvert smt2_solver(in, boolbv);
  smt2_solver.set_message_handler(message_handler);

  smt2_solver.parse();

  if(!smt2_solver)
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

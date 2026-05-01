/*******************************************************************\

Module: SMT2 Solver that uses boolbv and the default SAT solver

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/message.h>
#include <util/namespace.h>
#include <util/simplify_expr.h>
#include <util/symbol_table.h>

#include <solvers/flattening/boolbv.h>
#include <solvers/sat/satcheck.h>
#ifdef SATCHECK_CADICAL
#  include <solvers/sat/satcheck_cadical.h>
#endif
#ifdef SATCHECK_MINISAT2
#  include <solvers/sat/satcheck_minisat2.h>
#endif
#ifdef SATCHECK_CRYPTOMINISAT
#  include <solvers/sat/satcheck_cryptominisat.h>
#endif

#include "smt2_format.h"
#include "smt2_parser.h"

#include <fstream> // IWYU pragma: keep
#include <iostream>

class smt2_solvert : public smt2_parsert
{
public:
  smt2_solvert(std::istream &_in, stack_decision_proceduret &_solver)
    : smt2_parsert(_in), solver(_solver), status(NOT_SOLVED)
  {
    setup_commands();
  }

protected:
  stack_decision_proceduret &solver;

  void setup_commands();
  void define_constants();
  void expand_function_applications(exprt &);

  std::set<irep_idt> constants_done;
  std::vector<exprt> deferred_assertions;

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
    if(constants_done.find(identifier) != constants_done.end())
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

  if(expr.id() == ID_function_application)
  {
    auto &app = to_function_application_expr(expr);

    if(app.function().id() == ID_symbol)
    {
      // look up the symbol
      auto identifier = to_symbol_expr(app.function()).identifier();
      auto f_it = id_map.find(identifier);

      if(f_it != id_map.end())
      {
        const auto &f = f_it->second;

        DATA_INVARIANT(
          f.type.id() == ID_mathematical_function,
          "type of function symbol must be mathematical_function_type");

        const auto &domain = to_mathematical_function_type(f.type).domain();

        DATA_INVARIANT(
          domain.size() == app.arguments().size(),
          "number of parameters must match number of arguments");

        // Does it have a definition? It's otherwise uninterpreted.
        if(!f.definition.is_nil())
        {
          exprt body = f.definition;

          if(body.id() == ID_lambda)
            body = to_lambda_expr(body).application(app.arguments());

          expand_function_applications(body); // rec. call
          expr = body;
        }
      }
    }
  }
}

void smt2_solvert::setup_commands()
{
  {
    commands["assert"] = [this]()
    {
      exprt e = expression();
      if(e.is_not_nil())
      {
        expand_function_applications(e);
        deferred_assertions.push_back(std::move(e));
      }
    };

    commands["check-sat"] = [this]()
    {
      // Pre-scan: count symbolic multiplications in deferred assertions.
      // If 3+, disable popcount so comba-cs uses shift-add for BVE.
      {
        std::size_t mult_count = 0;
        for(const auto &e : deferred_assertions)
          e.visit_pre(
            [&mult_count](const exprt &sub)
            {
              if(
                sub.id() == ID_mult && sub.operands().size() == 2 &&
                !sub.operands()[0].is_constant() &&
                !sub.operands()[1].is_constant())
                ++mult_count;
            });
        if(mult_count > 2)
        {
          if(auto *bv = dynamic_cast<boolbvt *>(&solver))
            bv->set_comba_carry_save(false);
        }
      }

      // Simplify assertions (word-level: commutativity, distributivity)
      {
        const symbol_tablet empty_symbol_table;
        const namespacet simplify_ns{empty_symbol_table};
        for(auto &e : deferred_assertions)
          e = simplify_expr(e, simplify_ns);
      }

      // Now encode all deferred assertions
      for(const auto &e : deferred_assertions)
        solver.set_to_true(e);
      deferred_assertions.clear();

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
    };

    commands["check-sat-assuming"] = [this]()
    {
      std::vector<exprt> assumptions;

      if(next_token() != smt2_tokenizert::OPEN)
        throw error("check-sat-assuming expects list as argument");

      while(smt2_tokenizer.peek() != smt2_tokenizert::CLOSE &&
            smt2_tokenizer.peek() != smt2_tokenizert::END_OF_FILE)
      {
        auto e = expression(); // any term
        expand_function_applications(e);
        assumptions.push_back(solver.handle(e));
      }

      if(next_token() != smt2_tokenizert::CLOSE)
        throw error("check-sat-assuming expects ')' at end of list");

      // add constant definitions as constraints
      define_constants();

      // add the assumptions
      solver.push(assumptions);

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

      // remove the assumptions again
      solver.pop();
    };

    commands["display"] = [this]()
    {
      // this is a command that Z3 appears to implement
      exprt e = expression();
      if(e.is_not_nil())
        std::cout << smt2_format(e) << '\n';
    };

    commands["get-unsat-assumptions"] = [this]()
    { throw error("not yet implemented"); };

    commands["get-value"] = [this]()
    {
      std::vector<exprt> ops;

      if(next_token() != smt2_tokenizert::OPEN)
        throw error("get-value expects list as argument");

      while(smt2_tokenizer.peek() != smt2_tokenizert::CLOSE &&
            smt2_tokenizer.peek() != smt2_tokenizert::END_OF_FILE)
      {
        ops.push_back(expression()); // any term
      }

      if(next_token() != smt2_tokenizert::CLOSE)
        throw error("get-value expects ')' at end of list");

      if(status != SAT)
        throw error("model is not available");

      std::vector<exprt> values;
      values.reserve(ops.size());

      for(const auto &op : ops)
      {
        if(op.id() != ID_symbol)
          throw error("get-value expects symbol");

        const auto &identifier = to_symbol_expr(op).identifier();

        const auto id_map_it = id_map.find(identifier);

        if(id_map_it == id_map.end())
          throw error() << "unexpected symbol '" << identifier << '\'';

        const exprt value = solver.get(op);

        if(value.is_nil())
          throw error() << "no value for '" << identifier << '\'';

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
    };

    commands["echo"] = [this]()
    {
      auto str_token = next_token();
      if(str_token != smt2_tokenizert::STRING_LITERAL)
        throw error("expected string literal");

      std::cout << smt2_format(constant_exprt(str_token.text, string_typet()))
                << '\n';
    };

    commands["get-assignment"] = [this]()
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
    };

    commands["get-model"] = [this]()
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
    };

    commands["simplify"] = [this]()
    {
      // this is a command that Z3 appears to implement
      exprt e = expression();
      if(e.is_not_nil())
      {
        const symbol_tablet symbol_table;
        const namespacet ns(symbol_table);
        exprt e_simplified = simplify_expr(e, ns);
        std::cout << smt2_format(e_simplified) << '\n';
      }
    };
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

  void print(unsigned, const xmlt &) override
  {
  }

  void print(unsigned, const jsont &) override
  {
  }

  void flush(unsigned) override
  {
    std::cout << std::flush;
  }
};

int solver(
  std::istream &in,
  bool xor_gauss,
  bool reorder_vars,
  bool use_cadical,
  bool use_cryptominisat,
  const std::string &multiplier_encoding_arg,
  const std::string &adder_encoding_str)
{
  // Default to comba-cs (carry-save Comba), matching cbmc's default.
  const std::string multiplier_encoding =
    multiplier_encoding_arg.empty() ? "comba-cs" : multiplier_encoding_arg;

  // Helper: apply multiplier and adder encoding to a boolbvt
  auto configure_encodings = [&](boolbvt &boolbv)
  {
    if(multiplier_encoding == "comba")
      boolbv.set_comba(true);
    else if(multiplier_encoding == "dadda")
      boolbv.set_dadda(true);
    else if(multiplier_encoding == "wallace")
      boolbv.set_wallace_tree(true);
    else if(multiplier_encoding == "comba-cs")
      boolbv.set_comba_carry_save(true);
    else if(multiplier_encoding == "dadda-cs")
      boolbv.set_dadda_carry_save(true);

    if(adder_encoding_str == "brent-kung")
      boolbv.set_adder_encoding(bv_utilst::adder_encodingt::BRENT_KUNG);
    else if(adder_encoding_str == "kogge-stone")
      boolbv.set_adder_encoding(bv_utilst::adder_encodingt::KOGGE_STONE);
    else if(adder_encoding_str == "g-only")
      boolbv.set_adder_encoding(bv_utilst::adder_encodingt::ADAPTIVE);
    else if(adder_encoding_str == "ripple")
    {
      // Explicitly selected ripple-carry
    }
    else
    {
      // Default: g-only (ADAPTIVE)
      boolbv.set_adder_encoding(bv_utilst::adder_encodingt::ADAPTIVE);
    }
  };

  symbol_tablet symbol_table;
  namespacet ns(symbol_table);

  smt2_message_handlert message_handler;
  messaget message(message_handler);

  // this is our default verbosity
  message_handler.set_verbosity(messaget::M_STATISTICS);

  satcheckt satcheck{message_handler};
#ifdef SATCHECK_CADICAL
  // Use CaDiCaL when requested or when xor-gauss is requested
  if(use_cadical || xor_gauss)
  {
    satcheck_cadical_no_preprocessingt cadical_satcheck{message_handler};
    if(xor_gauss)
      cadical_satcheck.enable_xor_gauss();
    if(reorder_vars)
      cadical_satcheck.enable_variable_renumbering();
    boolbvt boolbv{ns, cadical_satcheck, message_handler};
    configure_encodings(boolbv);
    smt2_solvert smt2_solver{in, boolbv};
    bool error_found = false;
    while(!smt2_solver.exit)
    {
      try
      {
        smt2_solver.parse();
      }
      catch(const smt2_tokenizert::smt2_errort &error)
      {
        smt2_solver.skip_to_end_of_list();
        error_found = true;
      }
    }
    if(error_found)
      return 1;
    return 0;
  }
#endif
#ifdef SATCHECK_CRYPTOMINISAT
  if(use_cryptominisat)
  {
    satcheck_cryptominisatt cms_satcheck{message_handler};
    boolbvt boolbv{ns, cms_satcheck, message_handler};
    configure_encodings(boolbv);
    smt2_solvert smt2_solver{in, boolbv};
    bool error_found = false;
    while(!smt2_solver.exit)
    {
      try
      {
        smt2_solver.parse();
      }
      catch(const smt2_tokenizert::smt2_errort &error)
      {
        smt2_solver.skip_to_end_of_list();
        error_found = true;
      }
    }
    if(error_found)
      return 1;
    return 0;
  }
#endif
  (void)xor_gauss;
  (void)reorder_vars;
  (void)use_cryptominisat;
  boolbvt boolbv{ns, satcheck, message_handler};
  configure_encodings(boolbv);

  smt2_solvert smt2_solver{in, boolbv};
  bool error_found = false;

  while(!smt2_solver.exit)
  {
    try
    {
      smt2_solver.parse();
    }
    catch(const smt2_tokenizert::smt2_errort &error)
    {
      smt2_solver.skip_to_end_of_list();
      error_found = true;
      message.error().source_location.set_line(error.get_line_no());
      message.error() << error.what() << messaget::eom;
    }
    catch(const analysis_exceptiont &error)
    {
      smt2_solver.skip_to_end_of_list();
      error_found = true;
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
  bool xor_gauss = false;
  bool reorder_vars = false;
  bool use_cadical = false;
  bool use_cryptominisat = false;
  std::string multiplier_encoding;
  std::string adder_encoding;
  const char *filename = nullptr;

  for(int i = 1; i < argc; ++i)
  {
    if(std::string{argv[i]} == "--xor-gauss")
      xor_gauss = true;
    else if(std::string{argv[i]} == "--reorder-vars")
      reorder_vars = true;
    else if(std::string{argv[i]} == "--cadical")
      use_cadical = true;
    else if(std::string{argv[i]} == "--cryptominisat")
      use_cryptominisat = true;
    else if(std::string{argv[i]} == "--multiplier-encoding" && i + 1 < argc)
      multiplier_encoding = argv[++i];
    else if(std::string{argv[i]} == "--adder-encoding" && i + 1 < argc)
      adder_encoding = argv[++i];
    else if(filename == nullptr)
      filename = argv[i];
    else
    {
      std::cerr << "usage: smt2_solver [--cadical] [--cryptominisat] "
                   "[--multiplier-encoding ENC] [--adder-encoding ENC] "
                   "[--xor-gauss] [--reorder-vars] [file]\n";
      return 1;
    }
  }

  if(filename == nullptr)
    return solver(
      std::cin,
      xor_gauss,
      reorder_vars,
      use_cadical,
      use_cryptominisat,
      multiplier_encoding,
      adder_encoding);

  std::ifstream in(filename);
  if(!in)
  {
    std::cerr << "failed to open " << filename << '\n';
    return 1;
  }

  return solver(
    in,
    xor_gauss,
    reorder_vars,
    use_cadical,
    use_cryptominisat,
    multiplier_encoding,
    adder_encoding);
}

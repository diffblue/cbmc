/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cstdlib>

#if defined(__linux__) || \
    defined(__FreeBSD_kernel__) || \
    defined(__GNU__) || \
    defined(__unix__) || \
    defined(__CYGWIN__) || \
    defined(__MACH__)
#include <unistd.h>
#endif

#include <util/std_expr.h>
#include <util/std_types.h>
#include <util/tempfile.h>
#include <util/arith_tools.h>
#include <util/i2string.h>
#include <util/ieee_float.h>

#include "smt2_dec.h"
#include "smt2irep.h"

/*******************************************************************\

Function: smt2_dect::decision_procedure_text

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string smt2_dect::decision_procedure_text() const
{
  return "SMT2 "+logic+
    (use_FPA_theory?" (with FPA)":"")+
    " using "+
    (solver==GENERIC?"Generic":
     solver==BOOLECTOR?"Boolector":
     solver==CVC3?"CVC3":
     solver==CVC4?"CVC4":
     solver==MATHSAT?"MathSAT":
     solver==OPENSMT?"OpenSMT":
     solver==YICES?"Yices":
     solver==Z3?"Z3":
     "(unknown)");
}

/*******************************************************************\

Function: smt2_temp_filet::smt2_temp_filet

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

smt2_temp_filet::smt2_temp_filet()
{
  temp_out_filename=get_temporary_file("smt2_dec_out_", "");

  temp_out.open(
    temp_out_filename.c_str(),
    std::ios_base::out | std::ios_base::trunc
  );
}

/*******************************************************************\

Function: smt2_temp_filet::~smt2_temp_filet

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

smt2_temp_filet::~smt2_temp_filet()
{
  temp_out.close();

  if(temp_out_filename!="")
    unlink(temp_out_filename.c_str());

  if(temp_result_filename!="")
    unlink(temp_result_filename.c_str());
}

/*******************************************************************\

Function: smt2_dect::dec_solve

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

decision_proceduret::resultt smt2_dect::dec_solve()
{
  // we write the problem into a file
  smt2_temp_filet smt2_temp_file;
  
  // copy from string buffer into file
  smt2_temp_file.temp_out << stringstream.str();

  // this finishes up and closes the SMT2 file
  write_footer(smt2_temp_file.temp_out);
  smt2_temp_file.temp_out.close();

  smt2_temp_file.temp_result_filename=
    get_temporary_file("smt2_dec_result_", "");

  std::string command;

  switch(solver)
  {
  case BOOLECTOR:
    command = "boolector --smt2 "
            + smt2_temp_file.temp_out_filename
            + " -m > "
            + smt2_temp_file.temp_result_filename;
    break;

  case CVC3:
    command = "cvc3 +model -lang smtlib -output-lang smtlib "
            + smt2_temp_file.temp_out_filename
            + " > "
            + smt2_temp_file.temp_result_filename;
    break;

  case CVC4:
    // The flags --bitblast=eager --bv-div-zero-const help but only
    // work for pure bit-vector formulas.
    command = "cvc4 -L smt2 "
            + smt2_temp_file.temp_out_filename
            + " > "
            + smt2_temp_file.temp_result_filename;
    break;

  case MATHSAT:
    // The options below were recommended by Alberto Griggio
    // on 10 July 2013
    command = "mathsat -input=smt2"
              " -preprocessor.toplevel_propagation=true"
              " -preprocessor.simplification=7"
              " -dpll.branching_random_frequency=0.01"
              " -dpll.branching_random_invalidate_phase_cache=true"
              " -dpll.restart_strategy=3"
              " -dpll.glucose_var_activity=true"
              " -dpll.glucose_learnt_minimization=true"
              " -theory.bv.eager=true"
              " -theory.bv.bit_blast_mode=1"
              " -theory.bv.delay_propagated_eqs=true"
              " -theory.fp.mode=1"
              " -theory.fp.bit_blast_mode=2"
              " -theory.arr.mode=1"
              " < "+smt2_temp_file.temp_out_filename
            + " > "+smt2_temp_file.temp_result_filename;
    break;

  case OPENSMT:
    command = "opensmt "
            + smt2_temp_file.temp_out_filename
            + " > "
            + smt2_temp_file.temp_result_filename;
    break;


  case YICES:
    //    command = "yices -smt -e "   // Calling convention for older versions
    command = "yices-smt2 "  //  Calling for 2.2.1
            + smt2_temp_file.temp_out_filename
            + " > "
            + smt2_temp_file.temp_result_filename;
    break;

  case Z3:
    command = "z3 -smt2 "
            + smt2_temp_file.temp_out_filename
            + " > "
            + smt2_temp_file.temp_result_filename;
    break;

  default:
    assert(false);
  }

  #if defined(__linux__) || defined(__APPLE__)
  command+=" 2>&1";
  #endif

  int res=system(command.c_str());
  if(res<0)
  {
    error() << "error running SMT2 soler" << eom;
    return decision_proceduret::D_ERROR;
  }

  std::ifstream in(smt2_temp_file.temp_result_filename.c_str());
  
  return read_result(in);
}

/*******************************************************************\

Function: smt2_dect::read_result

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

decision_proceduret::resultt smt2_dect::read_result(std::istream &in)
{
  std::string line;
  decision_proceduret::resultt res=D_ERROR;

  boolean_assignment.clear();
  boolean_assignment.resize(no_boolean_variables, false);

  typedef hash_map_cont<irep_idt, irept, irep_id_hash> valuest;
  valuest values;

  while(in)
  {
    irept parsed=smt2irep(in);
    
    if(parsed.id()=="sat")
      res=D_SATISFIABLE;
    else if(parsed.id()=="unsat")
      res=D_UNSATISFIABLE;
    else if(parsed.id()=="" &&
            parsed.get_sub().size()==1 &&
            parsed.get_sub().front().get_sub().size()==2)
    {
      const irept &s0=parsed.get_sub().front().get_sub()[0];
      const irept &s1=parsed.get_sub().front().get_sub()[1];

      // Examples:
      // ( (B0 true) )
      // ( (|__CPROVER_pipe_count#1| (_ bv0 32)) )
      
      values[s0.id()]=s1;
    }
    else if(parsed.id()=="" &&
            parsed.get_sub().size()==2 &&
            parsed.get_sub().front().id()=="error")
    {
      // We ignore errors after UNSAT because get-value after check-sat
      // returns unsat will give an error.
      if(res!=D_UNSATISFIABLE)
      {
        error() << "SMT2 solver returned error message:\n"
                << "\t\"" << parsed.get_sub()[1].id() <<"\"" << eom;
        return decision_proceduret::D_ERROR;
      }
    }
  }

  for(identifier_mapt::iterator
      it=identifier_map.begin();
      it!=identifier_map.end();
      it++)
  {
    std::string conv_id=convert_identifier(it->first);
    const irept &value=values[conv_id];
    it->second.value=parse_rec(value, it->second.type);
  }

  // Booleans
  for(unsigned v=0; v<no_boolean_variables; v++)
  {
    const irept &value=values["B"+i2string(v)];
    boolean_assignment[v]=(value.id()==ID_true);
  }

  return res;
}


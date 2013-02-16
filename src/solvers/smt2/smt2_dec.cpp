/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <stdlib.h>

#ifdef __linux__
#include <unistd.h>
#endif

#ifdef __FreeBSD_kernel__
#include <unistd.h>
#endif

#ifdef __GNU__
#include <unistd.h>
#endif

#ifdef __MACH__
#include <unistd.h>
#endif

#include <std_expr.h>
#include <std_types.h>
#include <tempfile.h>
#include <arith_tools.h>
#include <i2string.h>

#include "smt2_dec.h"

/*******************************************************************\

Function: smt2_dect::decision_procedure_text

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string smt2_dect::decision_procedure_text() const
{
  return "SMT "+logic+" using "+
    (solver==BOOLECTOR?"Boolector":
     solver==CVC3?"CVC3":
     solver==MATHSAT?"MathSAT":
     solver==Z3?"Z3":
     solver==YICES?"Yices":
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
  post_process();

  // this closes the SMT2 file
  smt2_prop.finalize();
  temp_out.close();

  temp_result_filename=
    get_temporary_file("smt2_dec_result_", "");

  std::string command;

  switch(solver)
  {
  case CVC3:
    command = "cvc3 +model -lang smtlib -output-lang smtlib "
            + temp_out_filename
            + " > "
            + temp_result_filename;
    break;

  case YICES:
    command = "yices -smt -e "
            + temp_out_filename
            + " > "
            + temp_result_filename;
    break;

  case BOOLECTOR:
    command = "boolector --smt "
            + temp_out_filename
            + " -fm --output "
            + temp_result_filename;
    break;

  case MATHSAT:
    command = "mathsat -input=smt2"
              " < "+temp_out_filename
            + " > "+temp_result_filename;
    break;

  case Z3:
    command = "z3 -smt2 "
            + temp_out_filename
            + " > "
            + temp_result_filename;
    break;

  default:
    assert(false);
  }

  #if defined(__linux__) || defined(__APPLE__)
  command+=" 2>&1";
  #endif

  system(command.c_str());

  std::ifstream in(temp_result_filename.c_str());

  switch(solver)
  {
  case CVC3:
    return read_result_cvc3(in);

  case YICES:
    return read_result_yices(in);
    
  case MATHSAT:
    return read_result_mathsat(in);

  case BOOLECTOR:
    return read_result_boolector(in);

  case Z3:
    return read_result_z3(in);

  default:
    assert(false);
  }
}

/*******************************************************************\

Function: smt2_dect::read_result_boolector

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

decision_proceduret::resultt smt2_dect::read_result_boolector(std::istream &in)
{
  std::string line;

  std::getline(in, line);

  if(line=="sat")
  {
    smt2_prop.reset_assignment();

    typedef hash_map_cont<std::string, std::string, string_hash> valuest;
    valuest values;

    while(std::getline(in, line))
    {
      std::size_t pos=line.find(' ');
      if(pos!=std::string::npos)
        values[std::string(line, 0, pos)]=
          std::string(line, pos+1, std::string::npos);
    }

    // Theory variables

    for(identifier_mapt::iterator
        it=identifier_map.begin();
        it!=identifier_map.end();
        it++)
    {
      it->second.value.make_nil();
      std::string conv_id=convert_identifier(it->first);
      std::string value=values[conv_id];
      if(value=="") continue;
      set_value(it->second, value);
    }

    // Booleans

    for(unsigned v=0; v<smt2_prop.no_variables(); v++)
    {
      std::string value=values["B"+i2string(v)];
      if(value=="") continue;
      smt2_prop.set_assignment(literalt(v, false), value=="1");
    }

    return D_SATISFIABLE;
  }
  else if(line=="unsat")
    return D_UNSATISFIABLE;
  else
    error("Unexpected result from SMT-Solver: "+line);

  return D_ERROR;
}

/*******************************************************************\

Function: smt2_dect::read_result_yices

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

decision_proceduret::resultt smt2_dect::read_result_yices(std::istream &in)
{
  std::string line;

  while(std::getline(in, line))
  {
  }

  error("Unexpected result from SMT-Solver");

  return D_ERROR;
}

/*******************************************************************\

Function: smt2_dect::read_result_mathsat

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

decision_proceduret::resultt smt2_dect::read_result_mathsat(std::istream &in)
{
  std::string line;
  decision_proceduret::resultt res=D_ERROR;

  smt2_prop.reset_assignment();

  typedef hash_map_cont<std::string, std::string, string_hash> valuest;
  valuest values;

  while(std::getline(in, line))
  {
    if(line=="sat")
      res=D_SATISFIABLE;
    else if(line=="unsat")
      res=D_UNSATISFIABLE;
    else if(line.size()>=2 && line[0]=='(')
    {
      // ( (B0 true) )
      std::size_t pos1=line.find('(', 1);
      std::size_t pos2=line.find(' ', pos1);
      std::size_t pos3=line.find(')', pos2);
      if(pos1!=std::string::npos &&
         pos2!=std::string::npos &&
         pos3!=std::string::npos)
      {
        std::string id=std::string(line, pos1+1, pos2-pos1-1);
        std::string value=std::string(line, pos2+1, pos3-pos2-1);
        values[id]=value;
      }
    }
  }

  for(identifier_mapt::iterator
      it=identifier_map.begin();
      it!=identifier_map.end();
      it++)
  {
    it->second.value.make_nil();
    std::string conv_id=convert_identifier(it->first);
    std::string value=values[conv_id];
    if(value=="") continue;
    if (value.substr(0, 5) == "(_ bv") {
      // value is "(_ bvDECIMAL_VALUE SIZE"
      // convert to binary
      value = value.substr(5);
      size_t pos = value.find(' ');
      std::string v = value.substr(0, pos);
      std::string w = value.substr(pos+1);
      value = integer2binary(string2integer(v, 10),
                             string2integer(w, 10).to_ulong());
    }
    set_value(it->second, value);
  }

  // Booleans
  for(unsigned v=0; v<smt2_prop.no_variables(); v++)
  {
    std::string value=values["B"+i2string(v)];
    if(value=="") continue;
    smt2_prop.set_assignment(literalt(v, false), value=="true");
  }

  return res;
}

/*******************************************************************\

Function: smt2_dect::read_result_z3

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

decision_proceduret::resultt smt2_dect::read_result_z3(std::istream &in)
{
  std::string line;
  decision_proceduret::resultt res = D_ERROR;

  smt2_prop.reset_assignment();

  typedef hash_map_cont<std::string, std::string, string_hash> valuest;
  valuest values;

  while(std::getline(in, line))
  {
    if(line=="sat")
      res = D_SATISFIABLE;
    else if(line=="unsat")
      res = D_UNSATISFIABLE;
    // XXX -- this is a really nasty hack.  It'll disappear when I write a
    // proper parser (Matt).
    else if(line.substr(0, 11) == "(core_expr_")
    {
      // This is the unsat core.  It looks like
      //
      // (core_expr_N1 core_expr_N2 ... core_expr_Nk)
      //
      // where each Ni is an integer.
      size_t start, end;

      // Start scanning from the 2nd character, so we skip over the leading
      // '('.
      start = 1;

      while (start < line.size()) {
        for (end = start; line[end] != ' ' && line[end] != ')'; end++);

        std::string core_name = line.substr(start, end-start);
        exprt &core_expr = core_map[core_name];
        unsat_core.insert(core_expr);

        start = end+1;
      }
    }
    else
    {
      // Values look like:
      //
      // ((identifer value))
      size_t start, mid, end;

      for (start = 0; start < line.size() && line[start] == '('; start++);
      for (mid = start; mid < line.size() && line[mid] != ' '; mid++);
      for (end = mid; end < line.size() && line[end] != ')'; end++);

      if (start < line.size() && mid < line.size() && end < line.size())
      {
        std::string identifier = line.substr(start, mid-start);
        std::string value = line.substr(mid+1, end-(mid+1));

        values[identifier] = value;
      }
    }
  }

  for(identifier_mapt::iterator
      it=identifier_map.begin();
      it!=identifier_map.end();
      it++)
  {
    it->second.value.make_nil();
    std::string conv_id=convert_identifier(it->first);
    std::string value=values[conv_id];
    if(value=="") continue;

//    std::cout << it->first << " := " << value << std::endl;

    exprt e;
    if(string_to_expr_z3(it->second.type, value, e))
    {
//      std::cout << "E: " << e << std::endl;
      it->second.value=e;
    }
    else
      set_value(it->second, value);
  }

  // Booleans
  for(unsigned v=0; v<smt2_prop.no_variables(); v++)
  {
    std::string value=values["B"+i2string(v)];
    if(value=="") continue;
    smt2_prop.set_assignment(literalt(v, false), value=="true");
  }

  return res;
}

/*******************************************************************\

Function: smt2_dect::string_to_expr_z3

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool smt2_dect::string_to_expr_z3(
  const typet &type,
  const std::string &value,
  exprt &e) const
{
  if(value.substr(0,2)=="bv")
  {
    std::string v=value.substr(2, value.find('[')-2);
    size_t p = value.find('[')+1;
    std::string w=value.substr(p, value.find(']')-p);

    std::string binary=integer2binary(string2integer(v,10),
                                      string2integer(w,10).to_ulong());

    if(type.id()==ID_struct ||
       type.id()==ID_union)
    {
      // TODO
    }
    else
    {
      constant_exprt c(type);
      c.set_value(binary);
      e=c;
    }

    return true;
  }
  else if(value.substr(0,6)=="(const") // const arrays
  {
    std::string av = value.substr(7, value.length()-8);

    exprt ae;
    if(!string_to_expr_z3(type.subtype(), av, ae)) return false;

    array_of_exprt ao;
    ao.type() = typet(ID_array);
    ao.type().subtype()=ae.type();
    ao.what() = ae;

    e = ao;

    return true;
  }
  else if(value.substr(0,6)=="(store")
  {
//    std::cout << "STR: " << value << std::endl;

    size_t p1=value.rfind(' ')+1;
    size_t p2=value.rfind(' ', p1-2)+1;

    assert(p1!=std::string::npos && p2!=std::string::npos);

    std::string elem = value.substr(p1, value.size()-p1-1);
    std::string inx = value.substr(p2, p1-p2-1);
    std::string array = value.substr(7, p2-8);

//    std::cout << "ELEM: " << elem << std::endl;
//    std::cout << "INX: " << inx << std::endl;
//    std::cout << "ARR: " << array << std::endl;

    exprt old;
    if(!string_to_expr_z3(type, array, old)) return false;

    exprt where;
    if(!string_to_expr_z3(array_index_type(), inx, where)) return false;

    exprt new_val;
    if(!string_to_expr_z3(type.subtype(), elem, new_val)) return false;

    e = with_exprt(old, where, new_val);

    return true;
  }
  else if(value=="false")
  {
    e = false_exprt();
    return true;
  }
  else if(value=="true")
  {
    e = true_exprt();
    return true;
  }
  else if(value.substr(0,8)=="array_of")
  {
    // We assume that array_of has only concrete arguments...
    irep_idt id=value;
    defined_expressionst::const_iterator fit=defined_expressions.begin();
    while(fit!=defined_expressions.end() && fit->second!=id) fit++;

    if(fit==defined_expressions.end()) return false;

    e = fit->first;

    return true;
  }
  else if(type.id()==ID_rational)
  {
    constant_exprt result;
    result.type()=rational_typet();

    if(value.substr(0,4)=="val!")
      result.set_value(value.substr(4));
    else
      result.set_value(value);

    e = result;
    return true;
  }

  return false;
}

/*******************************************************************\

Function: smt2_dect::read_result_cvc3

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

decision_proceduret::resultt smt2_dect::read_result_cvc3(std::istream &in)
{
  std::string line;
  decision_proceduret::resultt res = D_ERROR;

  smt2_prop.reset_assignment();

  typedef hash_map_cont<std::string, std::string, string_hash> valuest;
  valuest values;

  while(std::getline(in, line))
  {
    if(line=="sat")
      res = D_SATISFIABLE;
    else if(line=="unsat")
      res = D_UNSATISFIABLE;
    else if(line.find("Current scope level")!=std::string::npos ||
            line.find("Variable Assignment")!=std::string::npos)
      ; //ignore
    else
    {
      assert(line.substr(0,13)=="  :assumption");
      std::size_t pos=line.find('(');

      if(pos!=std::string::npos)
      {
        std::string var;
        std::string val;

        if(line[pos+1]=='=')
        {
          std::string ops = line.substr(pos+3, line.length()-pos-4);
          std::size_t blank=ops.find(' ');
          var = ops.substr(0, blank);
          val = ops.substr(blank+1, ops.length()-blank);

          if((var.length()>=4 && var.substr(0,4)=="cvc3") ||
             (val.length()>=4 && val.substr(0,4)=="cvc3") ||
             var==val)
            continue;
          else if((var.substr(0,9)=="array_of'") ||
                  (var.substr(0,2)=="bv" && val.substr(0,2)!="bv"))
          {
            std::string t=var; var=val; val=t;
          }

//          std::cout << "OPS: " << ops << std::endl;
        }
        else if(line.substr(pos+1,3)=="not")
        {
          var = line.substr(pos+5, line.length()-pos-6);
          val = "false";
        }
        else
        {
          var = line.substr(pos+1, line.length()-pos-2);
          assert(var.find(' ')==std::string::npos);
          val = "true";
        }

//        std::cout << "VAR: " << var << std::endl;
//        std::cout << "VAL: " << val << std::endl;

        values[var]=val;
      }
    }
  }

  for(identifier_mapt::iterator
      it=identifier_map.begin();
      it!=identifier_map.end();
      it++)
  {
    it->second.value.make_nil();
    std::string conv_id=convert_identifier(it->first);
    std::string value=values[conv_id];
    if(value=="") continue;

//    std::cout << it->first << " := " << value << std::endl;

    if(value.substr(0,2)=="bv")
    {
      std::string v=value.substr(2, value.find('[')-2);
      size_t p = value.find('[')+1;
      std::string w=value.substr(p, value.find(']')-p);

      std::string binary=integer2binary(string2integer(v,10),
                                        string2integer(w,10).to_ulong());

      set_value(it->second, binary);
    }
    else if(value=="false")
      it->second.value.make_false();
    else if(value=="true")
      it->second.value.make_true();
    else if(value.substr(0,8)=="array_of")
    {
      // We assume that array_of has only concrete arguments...
      irep_idt id=value;
      defined_expressionst::const_iterator fit=defined_expressions.begin();
      while(fit!=defined_expressions.end() && fit->second!=id) fit++;

      if(fit!=defined_expressions.end())
        it->second.value=fit->first;
    }
    else
      set_value(it->second, value);
  }

  // Booleans
  for(unsigned v=0; v<smt2_prop.no_variables(); v++)
  {
    std::string value=values["B"+i2string(v)];
    if(value=="") continue;
    smt2_prop.set_assignment(literalt(v, false), value=="true");
  }

  return res;
}


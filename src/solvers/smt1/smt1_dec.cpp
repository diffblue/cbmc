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
#include <string2int.h>
#include <prefix.h>

#include "smt1_dec.h"

/*******************************************************************\

Function: smt1_dect::decision_procedure_text

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string smt1_dect::decision_procedure_text() const
{
  return "SMT1 "+logic+" using "+
    (solver==BOOLECTOR?"Boolector":
     solver==CVC3?"CVC3":
     solver==OPENSMT?"OpenSMT":
     solver==YICES?"Yices":
     solver==MATHSAT?"MathSAT":
     solver==Z3?"Z3":
     "(unknown)");
}

/*******************************************************************\

Function: smt1_temp_filet::smt1_temp_filet

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

smt1_temp_filet::smt1_temp_filet()
{
  temp_out_filename=get_temporary_file("smt1_dec_out_", "");

  temp_out.open(
    temp_out_filename.c_str(),
    std::ios_base::out | std::ios_base::trunc
  );
}

/*******************************************************************\

Function: smt1_temp_filet::~smt1_temp_filet

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

smt1_temp_filet::~smt1_temp_filet()
{
  temp_out.close();

  if(temp_out_filename!="")
    unlink(temp_out_filename.c_str());

  if(temp_result_filename!="")
    unlink(temp_result_filename.c_str());
}

/*******************************************************************\

Function: smt1_dect::dec_solve

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

decision_proceduret::resultt smt1_dect::dec_solve()
{
  // SMT1 is really not incremental
  assert(!dec_solve_was_called);
  dec_solve_was_called=true;

  post_process();

  // this closes the SMT benchmark
  smt1_prop.finalize();
  temp_out.close();

  temp_result_filename=
    get_temporary_file("smt1_dec_result_", "");

  std::string command;

  switch(solver)
  {
  case CVC3:
    command = "cvc3 +model -lang smtlib -output-lang smtlib "
            + temp_out_filename
            + " > "
            + temp_result_filename;
    break;

  case BOOLECTOR:
    // –rwl0 disables rewriting, which makes things slower,
    // but in return values for arrays appear
    command = "boolector -rwl0 --smt "
            + temp_out_filename
            + " -fm --output "
            + temp_result_filename;
    break;

  case OPENSMT:
    command = "todo "
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

  case MATHSAT:
    command = "mathsat -model -input=smt"
              " < "+temp_out_filename
            + " > "+temp_result_filename;
    break;

  case Z3:
    command = "z3 -m "
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
  case BOOLECTOR:
    return read_result_boolector(in);

  case CVC3:
    return read_result_cvc3(in);

  case OPENSMT:
    return read_result_opensmt(in);

  case YICES:
    return read_result_yices(in);

  case MATHSAT:
    return read_result_mathsat(in);

  case Z3:
    return read_result_z3(in);

  default:
    assert(false);
  }
}

/*******************************************************************\

Function: smt1_dect::read_result_boolector

  Inputs:

 Outputs:

 Purpose: read model produced by Boolector

\*******************************************************************/

decision_proceduret::resultt smt1_dect::read_result_boolector(std::istream &in)
{
  std::string line;

  std::getline(in, line);

  if(line=="sat")
  {
    smt1_prop.reset_assignment();

    typedef hash_map_cont<std::string, valuet, string_hash> valuest;
    valuest values;

    while(std::getline(in, line))
    {
      std::size_t pos=line.find(' ');
      if(pos!=std::string::npos && pos!=0)
      {
        std::string id=std::string(line, 0, pos);
        std::string value=std::string(line, pos+1, std::string::npos);
      
        // Boolector offers array values as follows:
        //
        // ID[INDEX] VALUE
        //
        // There may be more than one line per ID
        
        if(id!="" && id[id.size()-1]==']') // array?
        {
          std::size_t pos2=id.find('[');
          
          if(pos2!=std::string::npos)
          {
            std::string new_id=std::string(id, 0, pos2);
            std::string index=std::string(id, pos2+1, id.size()-pos2-2);
            values[new_id].index_value_map[index]=value;
          }
        }
        else
          values[id].value=value;
      }
    }

    // Theory variables

    for(identifier_mapt::iterator
        it=identifier_map.begin();
        it!=identifier_map.end();
        it++)
    {
      it->second.value.make_nil();
      std::string conv_id=convert_identifier(it->first);
      const valuet &v=values[conv_id];

      for(valuet::index_value_mapt::const_iterator
          i_it=v.index_value_map.begin(); i_it!=v.index_value_map.end(); i_it++)
        set_value(it->second, i_it->first, i_it->second);
        
      if(v.value!="") set_value(it->second, "", v.value);
    }

    // Booleans

    for(unsigned v=0; v<smt1_prop.no_variables(); v++)
    {
      std::string value=values["B"+i2string(v)].value;
      if(value=="") continue;
      smt1_prop.set_assignment(literalt(v, false), value=="1");
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

Function: smt1_dect::read_result_opensmt

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

decision_proceduret::resultt smt1_dect::read_result_opensmt(std::istream &in)
{
  return D_ERROR;
}

/*******************************************************************\

Function: smt1_dect::read_result_yices

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

decision_proceduret::resultt smt1_dect::read_result_yices(std::istream &in)
{
  std::string line;

  while(std::getline(in, line))
  {
    if (line=="sat")
    {
      // fixme: read values
      return D_SATISFIABLE;
    }
    else if (line=="unsat")
      return D_UNSATISFIABLE;
  }

  error("Unexpected result from SMT-Solver");

  return D_ERROR;
}

/*******************************************************************\

Function: smt1_dect::read_result_mathsat

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string smt1_dect::mathsat_value(const std::string &src)
{
  std::size_t pos=src.find('[');

  if(std::string(src, 0, 2)=="bv" && 
     pos!=std::string::npos &&
     src[src.size()-1]==']') 
  {
    unsigned width=safe_string2unsigned(std::string(src, pos+1, src.size()-pos-2));
    mp_integer i=string2integer(std::string(src, 2, pos-2));
    return integer2binary(i, width);
  }
  
  return "";
}

/*******************************************************************\

Function: smt1_dect::read_result_mathsat

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

decision_proceduret::resultt smt1_dect::read_result_mathsat(std::istream &in)
{
  std::string line;
  decision_proceduret::resultt res = D_ERROR;

  smt1_prop.reset_assignment();

  typedef hash_map_cont<std::string, valuet, string_hash> valuest;
  valuest values;

  while(std::getline(in, line))
  {
    if(line=="sat")
      res=D_SATISFIABLE;
    else if(line=="unsat")
      res=D_UNSATISFIABLE;
    else if(line.size()>=1 && line[0]=='(')
    {
      // (= c_h39__h39___CPROVER_malloc_size_h39_35_h39_1 bv0[64])
      // (= (select __h64_0 bv0[32]) bv5[8])
      std::size_t pos1=line.find(' ');
      std::size_t pos2=line.rfind(' ');
      if(pos1!=std::string::npos &&
         pos2!=std::string::npos &&
         pos1!=pos2)
      {
        std::string id=std::string(line, pos1+1, pos2-pos1-1);
        std::string value=std::string(line, pos2+1, line.size()-pos2-2);

        if(has_prefix(id, "(select "))
        {
          #if 0
          std::size_t pos3=id.rfind(' ');
          std::string index=std::string(pos3+1, id.size()-pos3-1);
          id=std::string(id, 8, pos3-8);
          #endif
        }
        else
          values[id].value=value;
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
    std::string value=mathsat_value(values[conv_id].value);

    if(value!="")
      set_value(it->second, "", value);
  }

  // Booleans
  for(unsigned v=0; v<smt1_prop.no_variables(); v++)
  {
    std::string value=values["B"+i2string(v)].value;
    if(value=="") continue;
    smt1_prop.set_assignment(literalt(v, false), value=="true");
  }

  return res;
}

/*******************************************************************\

Function: smt1_dect::read_result_z3

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

decision_proceduret::resultt smt1_dect::read_result_z3(std::istream &in)
{
  std::string line;
  decision_proceduret::resultt res = D_ERROR;

  smt1_prop.reset_assignment();

  typedef hash_map_cont<std::string, std::string, string_hash> valuest;
  valuest values;

  while(std::getline(in, line))
  {
    if(line=="sat")
      res = D_SATISFIABLE;
    else if(line=="unsat")
      res = D_UNSATISFIABLE;
    else
    {
      std::size_t pos=line.find(" -> ");
      if(pos!=std::string::npos)
        values[std::string(line, 0, pos)]=
          std::string(line, pos+4, std::string::npos);
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

    exprt e;
    if(string_to_expr_z3(it->second.type, value, e))
      it->second.value=e;
    else
      set_value(it->second, "", value);
  }

  // Booleans
  for(unsigned v=0; v<smt1_prop.no_variables(); v++)
  {
    std::string value=values["B"+i2string(v)];
    if(value=="") continue;
    smt1_prop.set_assignment(literalt(v, false), value=="true");
  }

  return res;
}

/*******************************************************************\

Function: smt1_dect::string_to_expr_z3

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool smt1_dect::string_to_expr_z3(
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

    if(type.id()==ID_struct)
    {
      e=binary2struct(to_struct_type(type), binary);
    }
    else if(type.id()==ID_union)
    {
      e=binary2union(to_union_type(type), binary);
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
    ao.type() = typet("array");
    ao.type().subtype()=ae.type();
    ao.what() = ae;

    e = ao;

    return true;
  }
  else if(value.substr(0,6)=="(store")
  {
    size_t p1=value.rfind(' ')+1;
    size_t p2=value.rfind(' ', p1-2)+1;

    assert(p1!=std::string::npos && p2!=std::string::npos);

    std::string elem = value.substr(p1, value.size()-p1-1);
    std::string inx = value.substr(p2, p1-p2-1);
    std::string array = value.substr(7, p2-8);

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
    irep_idt id(value);
    array_of_mapt::const_iterator fit=array_of_map.begin();
    while(fit!=array_of_map.end() && fit->second!=id) fit++;

    if(fit==array_of_map.end()) return false;

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

Function: smt1_dect::read_result_cvc3

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

decision_proceduret::resultt smt1_dect::read_result_cvc3(std::istream &in)
{
  std::string line;
  decision_proceduret::resultt res = D_ERROR;

  smt1_prop.reset_assignment();

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

    if(value.substr(0,2)=="bv")
    {
      std::string v=value.substr(2, value.find('[')-2);
      size_t p = value.find('[')+1;
      std::string w=value.substr(p, value.find(']')-p);

      std::string binary=integer2binary(string2integer(v,10),
                                        string2integer(w,10).to_ulong());

      set_value(it->second, "", binary);
    }
    else if(value=="false")
      it->second.value.make_false();
    else if(value=="true")
      it->second.value.make_true();
    else if(value.substr(0,8)=="array_of")
    {
      // We assume that array_of has only concrete arguments...
      irep_idt id(value);
      array_of_mapt::const_iterator fit=array_of_map.begin();
      while(fit!=array_of_map.end() && fit->second!=id) fit++;

      if(fit!=array_of_map.end())
        it->second.value = fit->first;
    }
    else
      set_value(it->second, "", value);
  }

  // Booleans
  for(unsigned v=0; v<smt1_prop.no_variables(); v++)
  {
    std::string value=values["B"+i2string(v)];
    if(value=="") continue;
    smt1_prop.set_assignment(literalt(v, false), value=="true");
  }

  return res;
}


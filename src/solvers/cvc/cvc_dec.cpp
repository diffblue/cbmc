/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cstring>
#include <cassert>
#include <cstdlib> // for system()

#if defined(__linux__) || \
    defined(__FreeBSD_kernel__) || \
    defined(__GNU__) || \
    defined(__unix__) || \
    defined(__CYGWIN__) || \
    defined(__MACH__)
#include <unistd.h>
#endif

#ifdef _WIN32
#include <process.h>
#define getpid _getpid
#endif

#include <util/i2string.h>
#include <util/prefix.h>
#include <util/string2int.h>

#include "cvc_dec.h"

/*******************************************************************\

Function: cvc_temp_filet::cvc_temp_filet

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

cvc_temp_filet::cvc_temp_filet()
{
  temp_out_filename="cvc_dec_out_"+i2string(getpid())+".tmp";

  temp_out.open(
    temp_out_filename.c_str(),
    std::ios_base::out | std::ios_base::trunc);
}

/*******************************************************************\

Function: cvc_temp_filet::~cvc_temp_filet

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

cvc_temp_filet::~cvc_temp_filet()
{
  temp_out.close();
  
  if(temp_out_filename!="")
    unlink(temp_out_filename.c_str());
    
  if(temp_result_filename!="")
    unlink(temp_result_filename.c_str());
}

/*******************************************************************\

Function: cvc_dect::dec_solve

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

decision_proceduret::resultt cvc_dect::dec_solve()
{
  out << "QUERY FALSE;" << std::endl;
  out << "COUNTERMODEL;" << std::endl;
  
  temp_out.close();

  temp_result_filename=
    "cvc_dec_result_"+i2string(getpid())+".tmp";
    
  std::string command=
    "cvcl "+temp_out_filename+" > "+temp_result_filename+" 2>&1";
    
  int res=system(command.c_str());
  assert(0 == res);
  
  status() << "Reading result from CVCL" << eom;

  return read_cvcl_result();
}

/*******************************************************************\

Function: cvc_dect::read_assert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cvc_dect::read_assert(std::istream &in, std::string &line)
{
  // strip ASSERT
  line=std::string(line, strlen("ASSERT "), std::string::npos);
  if(line=="") return;
  
  // bit-vector
  if(line[0]=='(')
  {
    // get identifier
    std::string::size_type pos=
      line.find(' ');

    std::string identifier=std::string(line, 1, pos-1);
    
    // get value
    if(!std::getline(in, line)) return;

    // skip spaces    
    pos=0;
    while(pos<line.size() && line[pos]==' ') pos++;
    
    // get final ")"
    std::string::size_type pos2=line.rfind(')');
    if(pos2==std::string::npos) return;    
    
    std::string value=std::string(line, pos, pos2-pos);

    #if 0    
    std::cout << ">" << identifier << "< = >" << value << "<";
    std::cout << std::endl;
    #endif
  }
  else
  {
    // boolean
    bool value=true;
    
    if(has_prefix(line, "NOT "))
    {
      line=std::string(line, strlen("NOT "), std::string::npos);
      value=false;
    }
    
    if(line=="") return;
    
    if(line[0]=='l')
    {
      unsigned number=unsafe_c_str2unsigned(line.c_str()+1);
      assert(number<no_boolean_variables);
      assert(no_boolean_variables==boolean_assignment.size());
      boolean_assignment[number]=value;
    }
  }
}

/*******************************************************************\

Function: cvc_dect::read_cvcl_result

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

decision_proceduret::resultt cvc_dect::read_cvcl_result()
{
  std::ifstream in(temp_result_filename.c_str());
  
  std::string line;
  
  while(std::getline(in, line))
  {
    if(has_prefix(line, "Invalid."))
    {
      boolean_assignment.clear();
      boolean_assignment.resize(no_boolean_variables);
    
      while(std::getline(in, line))
      {
        if(has_prefix(line, "ASSERT "))
          read_assert(in, line);
      }
      
      return D_SATISFIABLE;
    }
    else if(has_prefix(line, "Valid."))
      return D_UNSATISFIABLE;
  }
  
  error() << "Unexpected result from CVC-Lite" << eom;
  
  return D_ERROR;
}


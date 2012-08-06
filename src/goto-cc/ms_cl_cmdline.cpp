/*******************************************************************\

Module: A special command line object for the CL options

Author: Daniel Kroening

\*******************************************************************/

#include <assert.h>
#include <string.h>
#include <stdlib.h>

#include <iostream>
#include <fstream>

#include <unicode.h>

#include "ms_cl_cmdline.h"

/*******************************************************************\
 
Function: ms_cl_cmdlinet::parse
 
  Inputs: argument count, argument strings
 
 Outputs: none
 
 Purpose: parses the commandline options into a cmdlinet
 
\*******************************************************************/

const char *non_ms_cl_options[]=
{
  "--dot",
  "--show-symbol-table",
  "--show-function-table",
  "--ppc-macos",
  "--i386-linux",
  "--i386-win32",
  "--i386-macos",
  "--string-abstraction",
  "--no-library",
  "--16",
  "--32",
  "--64",
  "--little-endian",
  "--big-endian",
  "--unsigned-char",
  "--no-arch",            
  "--help",
  "--xml",
  "--partial-inlining",
  "--verbosity",
  "--function",
  NULL
};

bool ms_cl_cmdlinet::parse(const std::vector<std::string> &options)
{
  for(unsigned i=0; i<options.size(); i++)
  {
    // is it a non-cl option?
    if(std::string(options[i], 0, 2)=="--")
    {
      process_non_cl_option(options[i]);

      if(options[i]=="--verbosity" ||
         options[i]=="--function")
        if(i<options.size()-1)
        {
          set(options[i].substr(2), options[i+1]);
          i++; // skip ahead
        }
    }
    else if(!options[i].empty() && options[i][0]=='@')
    {
      // potentially recursive
      process_response_file(
        std::string(options[i], 1, std::string::npos));
    }
    else if(options[i]=="/link" ||
            options[i]=="-link")
    {
      // anything that follows goes to the linker
      i=options.size()-1;
    }
    else if(options[i].size()==2 &&
            (options[i]=="/D" || options[i]=="-D") &&
            i!=options.size()-1)
    {
      // this requires special treatment, as you can do "/D something"
      std::string tmp="/D"+options[i+1];
      i++;
      process_cl_option(tmp);
    }
    else
      process_cl_option(options[i]);
  }

  return false;
}

/*******************************************************************\
 
Function: ms_cl_cmdlinet::parse_env
 
  Inputs:
 
 Outputs: none
 
 Purpose:
 
\*******************************************************************/

void ms_cl_cmdlinet::parse_env()
{
  // first do environment
  
  #ifdef _WIN32

  const wchar_t *CL_env=_wgetenv(L"CL");

  if(CL_env!=NULL)
    process_response_file_line(narrow(CL_env));

  #else

  const char *CL_env=getenv("CL");

  if(CL_env!=NULL)
    process_response_file_line(CL_env);

  #endif  
}

/*******************************************************************\
 
Function: ms_cl_cmdlinet::parse
 
  Inputs: argument count, argument strings
 
 Outputs: none
 
 Purpose: parses the commandline options into a cmdlinet
 
\*******************************************************************/

bool ms_cl_cmdlinet::parse(int argc, const char **argv)
{
  // should really use "wide" argv from wmain()

  std::vector<std::string> options;

  // skip argv[0]
  for(int i=1; i<argc; i++)
    options.push_back(argv[i]);
  
  return parse(options);
}

/*******************************************************************\
 
Function: my_wgetline
 
  Inputs: 
 
 Outputs:
 
 Purpose: 
 
\*******************************************************************/

static std::istream &my_wgetline(std::istream &in, std::wstring &dest)
{
  // We should support this properly,
  // but will just strip right now.
  dest.clear();

  while(in)
  {
    char ch1, ch2;
    in.get(ch1);
    in.get(ch2);
    
    if(!in)
    {
      if(!dest.empty()) in.clear();
      break;
    }

    if(ch1=='\r')
    {
      // ignore
    }
    else if(ch1=='\n')
    {
      in.clear();
      break; // line end
    }
    else
      dest+=wchar_t(ch1+(ch2<<8));
  }
        
  return in;
}

/*******************************************************************\
 
Function: ms_cl_cmdlinet::process_response_file
 
  Inputs: 
 
 Outputs: none
 
 Purpose: 
 
\*******************************************************************/

void ms_cl_cmdlinet::process_response_file(const std::string &file)
{
  std::ifstream infile(file.c_str());
  
  if(!infile)
  {
    std::cerr << "failed to open response file `"
              << file << "'" << std::endl;
    return;
  }

  // these may be Unicode -- which is indicated by 0xff 0xfe
  std::string line;
  getline(infile, line);
  if(line.size()>=2 &&
     line[0]==char(0xff) &&
     line[1]==char(0xfe))
  {
    // Unicode, UTF-16 little endian
    
    #if 1
    // Re-open -- should be using wifstream,
    // but this isn't available everywhere.
    std::ifstream infile2(file.c_str(), std::ios::binary);
    infile2.seekg(2);
    std::wstring wline;
    
    while(my_wgetline(infile2, wline))
      process_response_file_line(narrow(wline)); // we UTF-8 it

    #else
    
    std::wifstream infile2(file.c_str(), std::ios::binary);
    std::wstring wline;
    
    while(std::getline(infile2, wline))
      process_response_file_line(narrow(wline)); // we UTF-8 it
    
    #endif
  }
  else if(line.size()>=3 &&
          line[0]==char(0xef) &&
          line[1]==char(0xbb) &&
          line[2]==char(0xbf))
  {
    // This is the UTF-8 BOM. We can proceed as usual, since
    // we use UTF-8 internally.
    infile.seekg(3);
    
    while(getline(infile, line))
      process_response_file_line(line);
  }
  else
  {
    // normal ASCII
    infile.seekg(0);
    while(getline(infile, line))
      process_response_file_line(line);
  }
}

/*******************************************************************\
 
Function: ms_cl_cmdlinet::process_response_file_line
 
  Inputs: 
 
 Outputs: none
 
 Purpose: 
 
\*******************************************************************/

void ms_cl_cmdlinet::process_response_file_line(const std::string &line)
{
  // In a response file, multiple compiler options and source-code files can
  // appear on one line.  A single compiler-option specification must appear
  // on one line (cannot span multiple lines).  Response files can have
  // comments that begin with the # symbol.

  if(line.empty()) return;
  if(line[0]=='#') return; // comment

  std::vector<std::string> options;
  std::string option;
  bool in_quotes=false;

  for(unsigned i=0; i<line.size(); i++)
  {
    char ch=line[i];
    
    if(ch==' ' && !in_quotes)
    {
      if(!option.empty()) options.push_back(option);
      option.clear();
    }
    else if(ch=='"')
    {
      in_quotes=!in_quotes;
    }
    else
      option+=ch;
  }

  if(!option.empty()) options.push_back(option);

  parse(options);
}

/*******************************************************************\
 
Function: ms_cl_cmdlinet::process_non_cl_option
 
  Inputs: 
 
 Outputs: none
 
 Purpose: 
 
\*******************************************************************/

void ms_cl_cmdlinet::process_non_cl_option(
  const std::string &s)
{
  cmdlinet::optiont option;

  option.isset=true;
  option.islong=true;
  option.optstring=std::string(s, 2, std::string::npos);
  option.optchar=0;

  int optnr=getoptnr(option.optstring);

  if(optnr==-1)
  {
    options.push_back(option);
    optnr=options.size()-1;
  }

  options[optnr].isset=true;
      
  for(unsigned j=0; non_ms_cl_options[j]!=NULL; j++)
    if(s==non_ms_cl_options[j])
      return;

  // unrecognized option
  std::cout << "Warning: uninterpreted non-CL option `"
            << s << "'" << std::endl;
}

/*******************************************************************\
 
Function: ms_cl_cmdlinet::process_cl_option
 
  Inputs: 
 
 Outputs: none
 
 Purpose: 
 
\*******************************************************************/

const char *ms_cl_flags[]=
{
  "c", // compile only
  NULL
};

const char *ms_cl_prefixes[]=
{
  "O1", // minimize space
  "O2", // maximize speed
  "Ob", // <n> inline expansion (default n=0)
  "Od", // disable optimizations (default)
  "Og", // enable global optimization
  "Oi", // [-] enable intrinsic functions
  "Os", // favor code space
  "Ot", // favor code speed
  "Ox", // maximum optimizations
  "Oy", // [-] enable frame pointer omission
  "GF", // enable read-only string pooling
  "Gm", // [-] enable minimal rebuild
  "Gy", // [-] separate functions for linker
  "GS", // [-] enable security checks
  "GR", // [-] enable C++ RTTI
  "GX", // [-] enable C++ EH (same as /EHsc)
  "EHs", // enable C++ EH (no SEH exceptions)
  "EHa", // enable C++ EH (w/ SEH exceptions)
  "EHc", // extern "C" defaults to nothrow
  "fp", // floating-point model
  "GL", // [-] enable link-time code generation
  "GA", // optimize for Windows Application
  "Ge", // force stack checking for all funcs
  "Gs", // [num] control stack checking calls
  "Gh", // enable _penter function call
  "GH", // enable _pexit function call
  "GT", // generate fiber-safe TLS accesses
  "RTC1", // Enable fast checks (/RTCsu)
  "RTCc", // Convert to smaller type checks
  "RTCs", // Stack Frame runtime checking
  "RTCu", // Uninitialized local usage checks
  "clr", // compile for common language runtime
  "Gd", // __cdecl calling convention
  "Gr", // __fastcall calling convention
  "Gz", // __stdcall calling convention
  "GZ", // Enable stack checks (/RTCs)
  "QIfist", // [-] use FIST instead of ftol()
  "hotpatch", // ensure function padding for hotpatchable images
  "arch:", // <SSE|SSE2> minimum CPU architecture requirements
  "Fa", // [file] name assembly listing file
  "FA", // [scu] configure assembly listing
  "Fd", // [file] name .PDB file
  "Fe", // <file> name executable file
  "Fm", // [file] name map file
  "Fo", // <file> name object file
  "Fp", // <file> name precompiled header file
  "Fr", // [file] name source browser file
  "FR", // [file] name extended .SBR file
  "doc", // [file] process XML documentation comments
  "AI", // <dir> add to assembly search path
  "FU", // <file> forced using assembly/module
  "C", //  don't strip comments
  "D", // <name>{=|#}<text> define macro
  "E", //  preprocess to stdout
  "EP", //  preprocess to stdout, no #line
  "P", //  preprocess to file
  "Fx", //  merge injected code to file
  "FI", // <file> name forced include file
  "U", // <name> remove predefined macro
  "u", //  remove all predefined macros
  "I", // <dir> add to include search path
  "X", //  ignore "standard places"
  "Zi", //  enable debugging information
  "Z7", //  enable old-style debug info
  "Zp", // [n] pack structs on n-byte boundary
  "Za", //  disable extensions
  "Ze", //  enable extensions (default)
  "Zl", //  omit default library name in .OBJ
  "Zg", //  generate function prototypes
  "Zs", //  syntax check only
  "vd", // {0|1|2} disable/enable vtordisp
  "vm", // <x> type of pointers to members
  "Zc:", // arg1[,arg2] C++ language conformance, where arguments can be:
  "ZI", //  enable Edit and Continue debug info
  "openmp", //  enable OpenMP 2.0 language extensions
  "analyze",
  "errorReport",
  "?",
  "help", //  print this help message
  "FC", //  use full pathnames in diagnostics /H<num> max external name length
  "J", //  default char type is unsigned
  "nologo", //  suppress copyright message
  "show", // Includes show include file names
  "Tc", // <source file> compile file as .c
  "Tp", // <source file> compile file as .cpp
  "TC", // compile all files as .c
  "TP", // compile all files as .cpp
  "V", // <string> set version string
  "w", // disable all warnings
  "wd", // <n> disable warning n
  "we", // <n> treat warning n as an error
  "wo", // <n> issue warning n once
  "w", // <l><n> set warning level 1-4 for n
  "W", // <n> set warning level (default n=1)
  "Wall", // enable all warnings
  "WL", // enable one line diagnostics
  "WX", // treat warnings as errors
  "Yc", // [file] create .PCH file
  "Yd", // put debug info in every .OBJ
  "Yl", // [sym] inject .PCH ref for debug lib
  "Yu", // [file] use .PCH file
  "Y", // - disable all PCH options
  "Zm", // <n> max memory alloc (% of default)
  "Wp64", // enable 64 bit porting warnings
  "LD", //  Create .DLL
  "LDd", //  Create .DLL debug library
  "LN", //  Create a .netmodule
  "F", // <num> set stack size
  "link", //  [linker options and libraries]
  "MD", //  link with MSVCRT.LIB
  "MT", //  link with LIBCMT.LIB
  "MDd", //  link with MSVCRTD.LIB debug lib
  "MTd", //  link with LIBCMTD.LIB debug lib
  NULL
};

void ms_cl_cmdlinet::process_cl_option(const std::string &s)
{
  if(s=="") return;

  if(s[0]!='/' && s[0]!='-')
  {
    args.push_back(s);
    return;
  }

  for(unsigned j=0; ms_cl_flags[j]!=NULL; j++)
  {
    if(std::string(s, 1, std::string::npos)==ms_cl_flags[j])
    {
      cmdlinet::optiont option;

      if(s.size()==2)
      {
        option.islong=false;
        option.optstring="";
        option.optchar=s[1];
      }
      else
      {
        option.islong=true;
        option.optstring=std::string(s, 1, std::string::npos);
        option.optchar=0;
      }

      int optnr=getoptnr(option.optstring);

      if(optnr==-1)
      {
        options.push_back(option);
        optnr=options.size()-1;
      }

      options[optnr].isset=true;
      return;
    }
  }
  
  for(unsigned j=0; ms_cl_prefixes[j]!=NULL; j++)
  {
    std::string ms_cl_prefix=ms_cl_prefixes[j];
    if(std::string(s, 1, ms_cl_prefix.size())==ms_cl_prefix)
    {
      cmdlinet::optiont option;
      
      int optnr;

      if(ms_cl_prefix.size()==1)
      {
        option.islong=false;
        option.optstring="";
        option.optchar=ms_cl_prefixes[j][0];
        optnr=getoptnr(option.optchar);
      }
      else
      {
        option.islong=true;
        option.optstring=std::string(s, 1, ms_cl_prefix.size());
        option.optchar=0;
        optnr=getoptnr(option.optstring);
      }

      if(optnr==-1)
      {
        options.push_back(option);
        optnr=options.size()-1;
      }

      options[optnr].isset=true;
      options[optnr].values.push_back(
        std::string(s, ms_cl_prefix.size()+1, std::string::npos));
      return;
    }
  }

  // unrecognized option
  std::cout << "Warning: uninterpreted CL option `"
            << s << "'" << std::endl;
}

/*******************************************************************\

Module: A special command line object for the CL options

Author: Daniel Kroening

\*******************************************************************/

#include <assert.h>
#include <string.h>
#include <stdlib.h>

#include <iostream>
#include <fstream>

#include "ms_cl_cmdline.h"

/*******************************************************************\
 
Function: ms_cl_cmdlinet::parse
 
  Inputs: argument count, argument strings
 
 Outputs: none
 
 Purpose: parses the commandline options into a cmdlinet
 
\*******************************************************************/

const wchar_t *non_ms_cl_options[]=
{
  L"--dot",
  L"--show-symbol-table",
  L"--show-function-table",
  L"--ppc-macos",
  L"--i386-linux",
  L"--i386-win32",
  L"--i386-macos",
  L"--string-abstraction",
  L"--no-library",
  L"--16",
  L"--32",
  L"--64",
  L"--little-endian",
  L"--big-endian",
  L"--unsigned-char",
  L"--no-arch",            
  L"--help",
  L"--xml",
  L"--partial-inlining",
  L"--verbosity",
  L"--function",
  NULL
};

bool ms_cl_cmdlinet::parse(const std::vector<std::wstring> &options)
{
  for(unsigned i=0; i<options.size(); i++)
  {
    // is it a non-cl option?
    if(std::wstring(options[i], 0, 2)==L"--")
    {
      process_non_cl_option(options[i]);

      if(options[i]==L"--verbosity" ||
         options[i]==L"--function")
        if(i<options.size()-1)
        {
          set(w2s(options[i]).substr(2), w2s(options[i+1]));
          i++; // skip ahead
        }
    }
    else if(!options[i].empty() && options[i][0]=='@')
    {
      // potentially recursive
      process_response_file(
        std::string(w2s(options[i]), 1, std::string::npos));
    }
    else if(options[i]==L"/link" ||
            options[i]==L"-link")
    {
      // anything that follows goes to the linker
      i=options.size()-1;
    }
    else if(options[i].size()==2 &&
            (options[i]==L"/D" || options[i]==L"-D") &&
            i!=options.size()-1)
    {
      // this requires special treatment, as you can do "/D something"
      std::wstring tmp=L"/D"+options[i+1];
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
    process_response_file_line(std::wstring(CL_env));

  #else

  const char *CL_env=getenv("CL");

  if(CL_env!=NULL)
    process_response_file_line(s2w(std::string(CL_env)));

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

  std::vector<std::wstring> options;

  // skip argv[0]
  for(int i=1; i<argc; i++)
    options.push_back(s2w(argv[i]));
  
  return parse(options);
}

/*******************************************************************\
 
Function: my_wgetline
 
  Inputs: 
 
 Outputs:
 
 Purpose: 
 
\*******************************************************************/

#if 0
static std::istream &my_wgetline(std::istream &in, std::string &dest)
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
    }
    else if(ch1=='\n')
    {
      in.clear();
      break;
    }
    else if(ch1==0)
    {
    }
    else
      dest+=ch1;
  }
        
  return in;
}
#endif

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
    std::cerr << "failed to open response file `" << file << "'"
              << std::endl;
    return;
  }

  // these may be Unicode -- which is indicated by 0xff 0xfe
  std::string line;
  getline(infile, line);
  if(line[0]==char(0xff) && line[1]==char(0xfe))
  {
    // Unicode!
    
    #if 0
    // re-open -- should be using wifstream
    std::ifstream infile2(file.c_str());
    infile2.seekg(2);
    
    while(my_wgetline(infile2, line))
      process_response_file_line(line);
    #else
    
    std::wifstream infile2(file.c_str());
    std::wstring wline;
    
    while(std::getline(infile2, wline))
      process_response_file_line(wline);
    
    #endif
  }
  else
  {
    // normal ASCII
    while(getline(infile, line))
      process_response_file_line(s2w(line));
  }
}

/*******************************************************************\
 
Function: ms_cl_cmdlinet::process_response_file_line
 
  Inputs: 
 
 Outputs: none
 
 Purpose: 
 
\*******************************************************************/

void ms_cl_cmdlinet::process_response_file_line(const std::wstring &line)
{
  // In a response file, multiple compiler options and source-code files can
  // appear on one line.  A single compiler-option specification must appear
  // on one line (cannot span multiple lines).  Response files can have
  // comments that begin with the # symbol.

  if(line.empty()) return;
  if(line[0]=='#') return; // comment

  std::vector<std::wstring> options;
  std::wstring option;
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
  const std::wstring &s)
{
  cmdlinet::optiont option;

  option.isset=true;
  option.islong=true;
  option.optstring=w2s(std::wstring(s, 2, std::string::npos));
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
  std::wcout << L"Warning: uninterpreted non-CL option `" 
             << s << L"'" << std::endl;
}

/*******************************************************************\
 
Function: ms_cl_cmdlinet::process_cl_option
 
  Inputs: 
 
 Outputs: none
 
 Purpose: 
 
\*******************************************************************/

const wchar_t *ms_cl_flags[]=
{
  L"c", // compile only
  NULL
};

const wchar_t *ms_cl_prefixes[]=
{
  L"O1", // minimize space
  L"O2", // maximize speed
  L"Ob", // <n> inline expansion (default n=0)
  L"Od", // disable optimizations (default)
  L"Og", // enable global optimization
  L"Oi", // [-] enable intrinsic functions
  L"Os", // favor code space
  L"Ot", // favor code speed
  L"Ox", // maximum optimizations
  L"Oy", // [-] enable frame pointer omission
  L"GF", // enable read-only string pooling
  L"Gm", // [-] enable minimal rebuild
  L"Gy", // [-] separate functions for linker
  L"GS", // [-] enable security checks
  L"GR", // [-] enable C++ RTTI
  L"GX", // [-] enable C++ EH (same as /EHsc)
  L"EHs", // enable C++ EH (no SEH exceptions)
  L"EHa", // enable C++ EH (w/ SEH exceptions)
  L"EHc", // extern "C" defaults to nothrow
  L"fp", // floating-point model
  L"GL", // [-] enable link-time code generation
  L"GA", // optimize for Windows Application
  L"Ge", // force stack checking for all funcs
  L"Gs", // [num] control stack checking calls
  L"Gh", // enable _penter function call
  L"GH", // enable _pexit function call
  L"GT", // generate fiber-safe TLS accesses
  L"RTC1", // Enable fast checks (/RTCsu)
  L"RTCc", // Convert to smaller type checks
  L"RTCs", // Stack Frame runtime checking
  L"RTCu", // Uninitialized local usage checks
  L"clr", // compile for common language runtime
  L"Gd", // __cdecl calling convention
  L"Gr", // __fastcall calling convention
  L"Gz", // __stdcall calling convention
  L"GZ", // Enable stack checks (/RTCs)
  L"QIfist", // [-] use FIST instead of ftol()
  L"hotpatch", // ensure function padding for hotpatchable images
  L"arch:", // <SSE|SSE2> minimum CPU architecture requirements
  L"Fa", // [file] name assembly listing file
  L"FA", // [scu] configure assembly listing
  L"Fd", // [file] name .PDB file
  L"Fe", // <file> name executable file
  L"Fm", // [file] name map file
  L"Fo", // <file> name object file
  L"Fp", // <file> name precompiled header file
  L"Fr", // [file] name source browser file
  L"FR", // [file] name extended .SBR file
  L"doc", // [file] process XML documentation comments
  L"AI", // <dir> add to assembly search path
  L"FU", // <file> forced using assembly/module
  L"C", //  don't strip comments
  L"D", // <name>{=|#}<text> define macro
  L"E", //  preprocess to stdout
  L"EP", //  preprocess to stdout, no #line
  L"P", //  preprocess to file
  L"Fx", //  merge injected code to file
  L"FI", // <file> name forced include file
  L"U", // <name> remove predefined macro
  L"u", //  remove all predefined macros
  L"I", // <dir> add to include search path
  L"X", //  ignore "standard places"
  L"Zi", //  enable debugging information
  L"Z7", //  enable old-style debug info
  L"Zp", // [n] pack structs on n-byte boundary
  L"Za", //  disable extensions
  L"Ze", //  enable extensions (default)
  L"Zl", //  omit default library name in .OBJ
  L"Zg", //  generate function prototypes
  L"Zs", //  syntax check only
  L"vd", // {0|1|2} disable/enable vtordisp
  L"vm", // <x> type of pointers to members
  L"Zc:", // arg1[,arg2] C++ language conformance, where arguments can be:
  L"ZI", //  enable Edit and Continue debug info
  L"openmp", //  enable OpenMP 2.0 language extensions
  L"analyze",
  L"errorReport",
  L"?",
  L"help", //  print this help message
  L"FC", //  use full pathnames in diagnostics /H<num> max external name length
  L"J", //  default char type is unsigned
  L"nologo", //  suppress copyright message
  L"show", // Includes show include file names
  L"Tc", // <source file> compile file as .c
  L"Tp", // <source file> compile file as .cpp
  L"TC", // compile all files as .c
  L"TP", // compile all files as .cpp
  L"V", // <string> set version string
  L"w", // disable all warnings
  L"wd", // <n> disable warning n
  L"we", // <n> treat warning n as an error
  L"wo", // <n> issue warning n once
  L"w", // <l><n> set warning level 1-4 for n
  L"W", // <n> set warning level (default n=1)
  L"Wall", // enable all warnings
  L"WL", // enable one line diagnostics
  L"WX", // treat warnings as errors
  L"Yc", // [file] create .PCH file
  L"Yd", // put debug info in every .OBJ
  L"Yl", // [sym] inject .PCH ref for debug lib
  L"Yu", // [file] use .PCH file
  L"Y", // - disable all PCH options
  L"Zm", // <n> max memory alloc (% of default)
  L"Wp64", // enable 64 bit porting warnings
  L"LD", //  Create .DLL
  L"LDd", //  Create .DLL debug library
  L"LN", //  Create a .netmodule
  L"F", // <num> set stack size
  L"link", //  [linker options and libraries]
  L"MD", //  link with MSVCRT.LIB
  L"MT", //  link with LIBCMT.LIB
  L"MDd", //  link with MSVCRTD.LIB debug lib
  L"MTd", //  link with LIBCMTD.LIB debug lib
  NULL
};

void ms_cl_cmdlinet::process_cl_option(const std::wstring &s)
{
  if(s==L"") return;

  if(s[0]!='/' && s[0]!='-')
  {
    args.push_back(w2s(s)); // loss!
    return;
  }

  for(unsigned j=0; ms_cl_flags[j]!=NULL; j++)
  {
    if(std::wstring(s, 1, std::string::npos)==ms_cl_flags[j])
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
        option.optstring=w2s(std::wstring(s, 1, std::string::npos)); // loss
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
    std::wstring ms_cl_prefix=ms_cl_prefixes[j];
    if(std::wstring(s, 1, ms_cl_prefix.size())==ms_cl_prefix)
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
        option.optstring=w2s(std::wstring(s, 1, ms_cl_prefix.size())); // loss
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
        w2s(std::wstring(s, ms_cl_prefix.size()+1, std::string::npos))); // loss
      return;
    }
  }

  // unrecognized option
  std::wcout << L"Warning: uninterpreted CL option `" 
             << s << L"'" << std::endl;
}

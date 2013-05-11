/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cstdio>
#include <cstdlib>
#include <cstring>

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

#include <fstream>

#include <util/config.h>
#include <util/i2string.h>
#include <util/message_stream.h>
#include <util/tempfile.h>
#include <util/unicode.h>

#include "c_preprocess.h"

#define GCC_DEFINES_16 \
  " -D__INT_MAX__=32767"\
  " -D__CHAR_BIT__=8"\
  " -D__WCHAR_MAX__=32767"\
  " -D__SCHAR_MAX__=127"\
  " -D__SHRT_MAX__=32767"\
  " -D__LONG_LONG_MAX__=2147483647L"\
  " -D__LONG_MAX__=2147483647" \
  " -D__SIZE_TYPE__=\"unsigned int\""\
  " -D__PTRDIFF_TYPE__=int"\
  " -D__WCHAR_TYPE__=int"\
  " -D__WINT_TYPE__=\"unsigned int\""\
  " -D__INTMAX_TYPE__=\"long long int\""\
  " -D__UINTMAX_TYPE__=\"long long unsigned int\""

#define GCC_DEFINES_32 \
  " -D__INT_MAX__=2147483647"\
  " -D__CHAR_BIT__=8"\
  " -D__WCHAR_MAX__=2147483647"\
  " -D__SCHAR_MAX__=127"\
  " -D__SHRT_MAX__=32767"\
  " -D__LONG_LONG_MAX__=9223372036854775807LL"\
  " -D__LONG_MAX__=2147483647L" \
  " -D__SIZE_TYPE__=\"long unsigned int\""\
  " -D__PTRDIFF_TYPE__=int"\
  " -D__WCHAR_TYPE__=int"\
  " -D__WINT_TYPE__=\"unsigned int\""\
  " -D__INTMAX_TYPE__=\"long long int\""\
  " -D__UINTMAX_TYPE__=\"long long unsigned int\""
                        
#define GCC_DEFINES_LP64 \
  " -D__INT_MAX__=2147483647"\
  " -D__CHAR_BIT__=8"\
  " -D__WCHAR_MAX__=2147483647"\
  " -D__SCHAR_MAX__=127"\
  " -D__SHRT_MAX__=32767"\
  " -D__LONG_LONG_MAX__=9223372036854775807LL"\
  " -D__LONG_MAX__=9223372036854775807L"\
  " -D__SIZE_TYPE__=\"long unsigned int\""\
  " -D__PTRDIFF_TYPE__=long"\
  " -D__WCHAR_TYPE__=int"\
  " -D__WINT_TYPE__=\"unsigned int\""\
  " -D__INTMAX_TYPE__=\"long int\""\
  " -D__UINTMAX_TYPE__=\"long unsigned int\""

/*******************************************************************\

Function: shell_quote

  Inputs:

 Outputs:

 Purpose: quote a string for bash and CMD

\*******************************************************************/

std::string shell_quote(const std::string &src)
{
  #ifdef _WIN32
  // first check if quoting is needed at all
  
  if(src.find(' ')==std::string::npos &&
     src.find('"')==std::string::npos &&
     src.find('&')==std::string::npos &&
     src.find('|')==std::string::npos &&
     src.find('(')==std::string::npos &&
     src.find(')')==std::string::npos &&
     src.find('<')==std::string::npos &&
     src.find('>')==std::string::npos &&
     src.find('^')==std::string::npos)
  {
    // seems fine -- return as is
    return src;
  }
  
  std::string result;
  
  result+='"';

  for(unsigned i=0; i<src.size(); i++)
  {
    const char ch=src[i];
    if(ch=='"') result+='"'; // quotes are doubled
    result+=ch;
  }  
  
  result+='"';

  return result;

  #else

  // first check if quoting is needed at all
  
  if(src.find(' ')==std::string::npos &&
     src.find('"')==std::string::npos &&
     src.find('*')==std::string::npos &&
     src.find('$')==std::string::npos &&
     src.find('\\')==std::string::npos &&
     src.find('?')==std::string::npos &&
     src.find('&')==std::string::npos &&
     src.find('|')==std::string::npos &&
     src.find('>')==std::string::npos &&
     src.find('<')==std::string::npos &&
     src.find('^')==std::string::npos &&
     src.find('\'')==std::string::npos)
  {
    // seems fine -- return as is
    return src;
  }
  
  std::string result;
  
  // the single quotes catch everything but themselves!
  result+='\'';

  for(unsigned i=0; i<src.size(); i++)
  {
    const char ch=src[i];
    if(ch=='\'') result+="'\\''";
    result+=ch;
  }  
  
  result+='\'';

  return result;
  #endif
}

/*******************************************************************\

Function: c_preprocess

  Inputs:

 Outputs:

 Purpose: ANSI-C preprocessing

\*******************************************************************/

bool c_preprocess(
  preprocess_modet mode,
  std::istream &instream,
  std::ostream &outstream,
  message_handlert &message_handler)
{
  std::string file=get_temporary_file("tmp.stdin", ".c");
  FILE *tmp=fopen(file.c_str(), "wt");

  char ch;
  while(instream.read(&ch, 1)!=NULL)
    fputc(ch, tmp);

  fclose(tmp);

  bool result=c_preprocess(mode, file, outstream, message_handler);
  
  unlink(file.c_str());
  
  return result;
}

/*******************************************************************\

Function: is_dot_i_file

  Inputs:

 Outputs:

 Purpose: ANSI-C preprocessing

\*******************************************************************/

static bool is_dot_i_file(const std::string &path)
{
  const char *ext=strrchr(path.c_str(), '.');
  if(ext==NULL) return false;
  if(std::string(ext)==".i" ||
     std::string(ext)==".ii") return true;
  return false;
}

/*******************************************************************\

Function: c_preprocess

  Inputs:

 Outputs:

 Purpose: ANSI-C preprocessing

\*******************************************************************/

bool c_preprocess_codewarrior(preprocess_modet, const std::string &, std::ostream &, message_handlert &);
bool c_preprocess_arm(preprocess_modet, const std::string &, std::ostream &, message_handlert &);
bool c_preprocess_gcc(preprocess_modet, const std::string &, std::ostream &, message_handlert &);
bool c_preprocess_none(preprocess_modet, const std::string &, std::ostream &, message_handlert &);
bool c_preprocess_visual_studio(preprocess_modet, const std::string &, std::ostream &, message_handlert &);

bool c_preprocess(
  preprocess_modet mode,
  const std::string &path,
  std::ostream &outstream,
  message_handlert &message_handler)
{
  switch(config.ansi_c.mode)
  {
  case configt::ansi_ct::MODE_CODEWARRIOR:
    return c_preprocess_codewarrior(mode, path, outstream, message_handler);
  
  case configt::ansi_ct::MODE_GCC:
    return c_preprocess_gcc(mode, path, outstream, message_handler);
  
  case configt::ansi_ct::MODE_VISUAL_STUDIO:
    return c_preprocess_visual_studio(mode, path, outstream, message_handler);
  
  case configt::ansi_ct::MODE_ARM:
    return c_preprocess_arm(mode, path, outstream, message_handler);
  
  default:
    assert(false);
  }

  // not reached  
  return true;
}

/*******************************************************************\

Function: c_preprocess_visual_studio

  Inputs:

 Outputs:

 Purpose: ANSI-C preprocessing

\*******************************************************************/

bool c_preprocess_visual_studio(
  preprocess_modet mode,
  const std::string &file,
  std::ostream &outstream,
  message_handlert &message_handler)
{
  // check extension
  if(is_dot_i_file(file))
    return c_preprocess_none(mode, file, outstream, message_handler);

  #ifndef _WIN32
  // we fall back to gcc
  return c_preprocess_gcc(mode, file, outstream, message_handler);
  #endif

  message_streamt message_stream(message_handler);

  // use Visual Studio's CL
  
  std::string stderr_file=get_temporary_file("tmp.stderr", "");
  std::string command_file_name=get_temporary_file("tmp.cl-cmd", "");

  {
    std::ofstream command_file(command_file_name.c_str());

    // This marks the file as UTF-8, which Visual Studio
    // understands.
    command_file << char(0xef) << char(0xbb) << char(0xbf);
  
    command_file << "/nologo" << std::endl;
    command_file << "/E" << std::endl;
    command_file << "/D__CPROVER__" << std::endl;
    command_file << "/D__WORDSIZE=" << config.ansi_c.pointer_width << std::endl;

    if(config.ansi_c.pointer_width==64)
    {
      command_file << "\"/D__PTRDIFF_TYPE__=long long int\""  << std::endl;
      // yes, both _WIN32 and _WIN64 get defined
      command_file << "/D_WIN64" << std::endl;
    }
    else
    {
      command_file << "/D__PTRDIFF_TYPE__=int" << std::endl;
      command_file << "/U_WIN64" << std::endl;
    }

    switch(config.ansi_c.arch)
    {
    case configt::ansi_ct::ARCH_I386:
      command_file << "/D_M_IX86" << std::endl;
      break;

    case configt::ansi_ct::ARCH_X86_64:
      command_file << "/D_M_X64" << std::endl
                   << "/D_M_AMD64" << std::endl;
      break;

    case configt::ansi_ct::ARCH_IA64:
      command_file << "/D_M_IA64" << std::endl;
      break;

    case configt::ansi_ct::ARCH_POWER:
      command_file << "/D_M_PPC" << std::endl;
      break;

    case configt::ansi_ct::ARCH_ARM:
      command_file << "/D_M_ARM" << std::endl;
      break;

    case configt::ansi_ct::ARCH_ALPHA:
      command_file << "/D_M_ALPHA" << std::endl;
      break;

    case configt::ansi_ct::ARCH_MIPS:
    case configt::ansi_ct::ARCH_SPARC:
    case configt::ansi_ct::ARCH_S390:
    case configt::ansi_ct::ARCH_S390X:
    case configt::ansi_ct::ARCH_X32:
      assert(false); // not supported by Visual Studio
      break;

    case configt::ansi_ct::NO_ARCH: break;
    }

    // Standard Defines, ANSI9899 6.10.8
    command_file << "/D__STDC_VERSION__=199901L" << std::endl;
    command_file << "/D__STDC_IEC_559__=1" << std::endl;
    command_file << "/D__STDC_IEC_559_COMPLEX__=1" << std::endl;
    command_file << "/D__STDC_ISO_10646__=1" << std::endl;
  
    for(std::list<std::string>::const_iterator
        it=config.ansi_c.defines.begin();
        it!=config.ansi_c.defines.end();
        it++)
      command_file << "/D" << shell_quote(*it) << std::endl;

    for(std::list<std::string>::const_iterator
        it=config.ansi_c.include_paths.begin();
        it!=config.ansi_c.include_paths.end();
        it++)
      command_file << "/I" << shell_quote(*it) << std::endl;

       for(std::list<std::string>::const_iterator
               it=config.ansi_c.include_files.begin();
               it!=config.ansi_c.include_files.end();
               it++)
         command_file << "/FI" << shell_quote(*it) << std::endl;

    // Finally, the file to be preprocessed
    // (this is already in UTF-8).
    command_file << shell_quote(file) << std::endl;
  }
  
  std::string tmpi=get_temporary_file("tmp.cl", "");
  
  std::string command="CL @"+command_file_name;
  command+=" > \""+tmpi+"\"";
  command+=" 2> \""+stderr_file+"\"";

  // _popen isn't very reliable on WIN32
  // that's why we use system()
  int result=system(command.c_str());

  FILE *stream=fopen(tmpi.c_str(), "r");

  if(stream==NULL)
  {
    unlink(tmpi.c_str());
    unlink(stderr_file.c_str());
    unlink(command_file_name.c_str());
    message_stream.error("CL Preprocessing failed (fopen failed)");
    return true;
  }

  {
    int ch;
    while((ch=fgetc(stream))!=EOF)
      outstream << (unsigned char)ch;
  }

  fclose(stream);
  unlink(tmpi.c_str());
  unlink(command_file_name.c_str());

  // errors/warnings
  {
    std::ifstream stderr_stream(stderr_file.c_str());
    char ch;
    while((stderr_stream.read(&ch, 1))!=NULL)
      message_stream.str << ch;
  }

  unlink(stderr_file.c_str());

  if(result!=0)
  {
    message_stream.error_parse(1);
    message_stream.error("CL Preprocessing failed");
    return true;
  }
  else
    message_stream.error_parse(2);  

  return false;
}

/*******************************************************************\

Function: postprocess_codewarrior

  Inputs:

 Outputs:

 Purpose: post-processing specifically for CodeWarrior

\*******************************************************************/

void postprocess_codewarrior(
  std::istream &instream,
  std::ostream &outstream)
{
  // CodeWarrior prepends some header to the file,
  // marked with '#' signs.
  // We skip over it.
  //
  // CodeWarrior has an ugly way of marking lines, e.g.:
  //
  // /* #line 1      "__ppc_eabi_init.cpp"   /* stack depth 0 */
  //
  // We remove the initial '/* ' prefix
  
  std::string line;
  
  while(instream)
  {
    std::getline(instream, line);
    
    if(line.size()>=2 &&
       line[0]=='#' && (line[1]=='#' || line[1]==' ' || line[1]=='\t'))
    {
      // skip the line!
    }
    else if(line.size()>=3 &&
            line[0]=='/' && line[1]=='*' && line[2]==' ')
    {
      outstream << line.c_str()+3 << std::endl; // strip the '/* '
    }
    else
      outstream << line << std::endl;
  }
}

/*******************************************************************\

Function: c_preprocess_codewarrior

  Inputs:

 Outputs:

 Purpose: ANSI-C preprocessing

\*******************************************************************/

bool c_preprocess_codewarrior(
  preprocess_modet mode,
  const std::string &file,
  std::ostream &outstream,
  message_handlert &message_handler)
{
  // check extension
  if(is_dot_i_file(file))
    return c_preprocess_none(mode, file, outstream, message_handler);

  // preprocessing
  message_streamt message_stream(message_handler);

  std::string stderr_file=get_temporary_file("tmp.stderr", "");

  std::string command;
  
  command="mwcceppc -E -P -D__CPROVER__ -ppopt line -ppopt full";

  for(std::list<std::string>::const_iterator
      it=config.ansi_c.defines.begin();
      it!=config.ansi_c.defines.end();
      it++)
    command+=" -D'"+*it+"'";

  for(std::list<std::string>::const_iterator
      it=config.ansi_c.include_paths.begin();
      it!=config.ansi_c.include_paths.end();
      it++)
    command+=" -I'"+*it+"'";

  for(std::list<std::string>::const_iterator
      it=config.ansi_c.include_files.begin();
      it!=config.ansi_c.include_files.end();
      it++)
    command+=" -include '"+*it+"'";

  for(std::list<std::string>::const_iterator
      it=config.ansi_c.preprocessor_options.begin();
      it!=config.ansi_c.preprocessor_options.end();
      it++)
    command+=" "+*it;
    
  int result;

  std::string tmpi=get_temporary_file("tmp.cl", "");
  command+=" \""+file+"\"";
  command+=" -o \""+tmpi+"\"";
  command+=" 2> \""+stderr_file+"\"";

  result=system(command.c_str());

  std::ifstream stream_i(tmpi.c_str());

  if(stream_i)
  {
    postprocess_codewarrior(stream_i, outstream);

    stream_i.close();
    unlink(tmpi.c_str());
  }
  else
  {
    unlink(tmpi.c_str());
    unlink(stderr_file.c_str());
    message_stream.error("Preprocessing failed (fopen failed)");
    return true;
  }

  // errors/warnings
  {
    std::ifstream stderr_stream(stderr_file.c_str());
    char ch;
    while((stderr_stream.read(&ch, 1))!=NULL)
      message_stream.str << ch;
  }

  unlink(stderr_file.c_str());

  if(result!=0)
  {
    message_stream.error_parse(1);
    message_stream.error("Preprocessing failed");
    return true;
  }
  else
    message_stream.error_parse(2);

  return false;
}

/*******************************************************************\

Function: c_preprocess_gcc

  Inputs:

 Outputs:

 Purpose: ANSI-C preprocessing

\*******************************************************************/

bool c_preprocess_gcc(
  preprocess_modet mode,
  const std::string &file,
  std::ostream &outstream,
  message_handlert &message_handler)
{
  // check extension
  if(is_dot_i_file(file))
    return c_preprocess_none(mode, file, outstream, message_handler);

  // preprocessing
  message_streamt message_stream(message_handler);

  std::string stderr_file=get_temporary_file("tmp.stderr", "");

  std::string command;
  
  command="gcc -E -undef -D__CPROVER__";

  if(config.ansi_c.os!=configt::ansi_ct::OS_WIN)
  {
    command+=" -D__null=0";
    command+=" -D__WORDSIZE="+i2string(config.ansi_c.pointer_width);
    
    // Tell the system library which standards we support.
    // these are not gcc-default!
    //command+=" -D_POSIX_SOURCE=1 -D_POSIX_C_SOURCE=200112L";
    //command+=" -D__STRICT_ANSI__=1";

    command+=" -D__DBL_MIN_EXP__=\"(-1021)\"";
    command+=" -D__FLT_MIN__=1.17549435e-38F";
    command+=" -D__DEC64_SUBNORMAL_MIN__=0.000000000000001E-383DD";
    command+=" -D__CHAR_BIT__=8";
    command+=" -D__DBL_DENORM_MIN__=4.9406564584124654e-324";
    command+=" -D__FLT_EVAL_METHOD__=0";
    command+=" -D__DBL_MIN_10_EXP__=\"(-307)\"";
    command+=" -D__FINITE_MATH_ONLY__=0";
    command+=" -D__DEC64_MAX_EXP__=384";
    command+=" -D__SHRT_MAX__=32767";
    command+=" -D__LDBL_MAX__=1.18973149535723176502e+4932L";
    command+=" -D__DEC32_EPSILON__=1E-6DF";
    command+=" -D__SCHAR_MAX__=127";
    command+=" -D__USER_LABEL_PREFIX__=_";
    command+=" -D__DEC64_MIN_EXP__=\"(-383)\"";
    command+=" -D__DBL_DIG__=15";
    command+=" -D__FLT_EPSILON__=1.19209290e-7F";
    command+=" -D__LDBL_MIN__=3.36210314311209350626e-4932L";
    command+=" -D__DEC32_MAX__=9.999999E96DF";
    command+=" -D__DECIMAL_DIG__=21";
    command+=" -D__LDBL_HAS_QUIET_NAN__=1";
    command+=" -D__DYNAMIC__=1";
    command+=" -D__GNUC__=4";
    command+=" -D__FLT_HAS_DENORM__=1";
    command+=" -D__DBL_MAX__=1.7976931348623157e+308";
    command+=" -D__DBL_HAS_INFINITY__=1";
    command+=" -D__DEC32_MIN_EXP__=\"(-95)\"";
    command+=" -D__LDBL_HAS_DENORM__=1";
    command+=" -D__DEC32_MIN__=1E-95DF";
    command+=" -D__DBL_MAX_EXP__=1024";
    command+=" -D__DEC128_EPSILON__=1E-33DL";
    command+=" -D__SSE2_MATH__=1";
    command+=" -D__GXX_ABI_VERSION=1002";
    command+=" -D__FLT_MIN_EXP__=\"(-125)\"";
    command+=" -D__DBL_MIN__=2.2250738585072014e-308";
    command+=" -D__DBL_HAS_QUIET_NAN__=1";
    command+=" -D__DEC128_MIN__=1E-6143DL";
    command+=" -D__REGISTER_PREFIX__=";
    command+=" -D__DBL_HAS_DENORM__=1";
    command+=" -D__DEC_EVAL_METHOD__=2";
    command+=" -D__DEC128_MAX__=9.999999999999999999999999999999999E6144DL";
    command+=" -D__FLT_MANT_DIG__=24";
    command+=" -D__DEC64_EPSILON__=1E-15DD";
    command+=" -D__DEC128_MIN_EXP__=\"(-6143)\"";
    command+=" -D__DEC32_SUBNORMAL_MIN__=0.000001E-95DF";
    command+=" -D__FLT_RADIX__=2";
    command+=" -D__LDBL_EPSILON__=1.08420217248550443401e-19L";
    command+=" -D__k8=1";
    command+=" -D__LDBL_DIG__=18";
    command+=" -D__FLT_HAS_QUIET_NAN__=1";
    command+=" -D__FLT_MAX_10_EXP__=38";
    command+=" -D__FLT_HAS_INFINITY__=1";
    command+=" -D__DEC64_MAX__=9.999999999999999E384DD";
    command+=" -D__DEC64_MANT_DIG__=16";
    command+=" -D__DEC32_MAX_EXP__=96";
    command+=" -D__DEC128_SUBNORMAL_MIN__=0.000000000000000000000000000000001E-6143DL";
    command+=" -D__LDBL_MANT_DIG__=64";
    command+=" -D__CONSTANT_CFSTRINGS__=1";
    command+=" -D__DEC32_MANT_DIG__=7";
    command+=" -D__k8__=1";
    command+=" -D__pic__=2";
    command+=" -D__FLT_DIG__=6";
    command+=" -D__FLT_MAX_EXP__=128";
    //command+=" -D__BLOCKS__=1";
    command+=" -D__DBL_MANT_DIG__=53";
    command+=" -D__DEC64_MIN__=1E-383DD";
    command+=" -D__LDBL_MIN_EXP__=\"(-16381)\"";
    command+=" -D__LDBL_MAX_EXP__=16384";
    command+=" -D__LDBL_MAX_10_EXP__=4932";
    command+=" -D__DBL_EPSILON__=2.2204460492503131e-16";
    command+=" -D__GNUC_PATCHLEVEL__=1";
    command+=" -D__LDBL_HAS_INFINITY__=1";
    command+=" -D__INTMAX_MAX__=9223372036854775807L";
    command+=" -D__FLT_DENORM_MIN__=1.40129846e-45F";
    command+=" -D__PIC__=2";
    command+=" -D__FLT_MAX__=3.40282347e+38F";
    command+=" -D__FLT_MIN_10_EXP__=\"(-37)\"";
    command+=" -D__DEC128_MAX_EXP__=6144";
    command+=" -D__GNUC_MINOR__=2";
    command+=" -D__DBL_MAX_10_EXP__=308";
    command+=" -D__LDBL_DENORM_MIN__=3.64519953188247460253e-4951L";
    command+=" -D__DEC128_MANT_DIG__=34";
    command+=" -D__LDBL_MIN_10_EXP__=\"(-4931)\"";

    if(config.ansi_c.int_width==16)
      command+=GCC_DEFINES_16;
    else if(config.ansi_c.int_width==32)
    {
      if(config.ansi_c.pointer_width==64)
        command+=GCC_DEFINES_LP64;
      else
      command+=GCC_DEFINES_32;
    }
  }
  
  switch(config.ansi_c.arch)
  {
  case configt::ansi_ct::ARCH_I386:
    command+=" -Di386 -D__i386 -D__i386__";
    break;

  case configt::ansi_ct::ARCH_X86_64:
    command+=" -D__LP64__ -D__x86_64 -D__x86_64__ -D_LP64 -D__amd64__ -D__amd64";
    break;

  case configt::ansi_ct::ARCH_X32:
    command+=" -D__ILP32__ -D__x86_64 -D__x86_64__ -D__amd64__ -D__amd64";
    break;

  case configt::ansi_ct::ARCH_IA64:
    command+=" -D__ia64__ -D_IA64 -D__IA64__";
    break;

  case configt::ansi_ct::ARCH_POWER:
    command+=" -D__powerpc -D__powerpc__ -D__POWERPC__ -D__ppc__";
    break;

  case configt::ansi_ct::ARCH_ARM:
    command+=" -D__arm__";
    break;

  case configt::ansi_ct::ARCH_ALPHA:
    command+=" -D__alpha__";
    break;

  case configt::ansi_ct::ARCH_MIPS:
    command+=" -D__mips__ -Dmips";
    command+=" -D_MIPS_SZPTR="+i2string(config.ansi_c.pointer_width);
    break;

  case configt::ansi_ct::ARCH_SPARC:
    command+=" -D__sparc__";
    break;

  case configt::ansi_ct::ARCH_S390:
    command+=" -D__s390__";
    break;

  case configt::ansi_ct::ARCH_S390X:
    command+=" -D__s390x__";
    break;

  case configt::ansi_ct::NO_ARCH: break;
  }
      
  switch(config.ansi_c.os)
  {
  case configt::ansi_ct::OS_LINUX:
    command+=" -Dlinux -D__linux -D__linux__ -D__gnu_linux__";
    command+=" -Dunix -D__unix -D__unix__";
    command+=" -D__USE_UNIX98";
    break;

  case configt::ansi_ct::OS_MACOS:
    if(config.ansi_c.arch==configt::ansi_ct::ARCH_I386 ||
       config.ansi_c.arch==configt::ansi_ct::ARCH_X86_64)
      command+=" -D__LITTLE_ENDIAN__";
    else if(config.ansi_c.arch==configt::ansi_ct::ARCH_POWER)
      command+=" -D__BIG_ENDIAN__";

    command+=" -D__APPLE__ -D__MACH__";
    // needs to be __APPLE_CPP__ for C++
    command+=" -D__APPLE_CC__";
    break;

  case configt::ansi_ct::OS_WIN:
    command+=" -D _MSC_VER=1400";
    command+=" -D _WIN32";
    command+=" -D _M_IX86=Blend";

    if(config.ansi_c.arch==configt::ansi_ct::ARCH_X86_64)
      command+=" -D _WIN64"; // yes, both _WIN32 and _WIN64 get defined

    if(config.ansi_c.char_is_unsigned)
      command+=" -D _CHAR_UNSIGNED";
    break;

  case configt::ansi_ct::NO_OS:
    command+=" -nostdinc"; // make sure we don't mess with the system library
    break;
    
  default:
    assert(false);
  }
  
  // Standard Defines, ANSI9899 6.10.8
  command += " -D __STDC_VERSION__=199901L";
  command += " -D __STDC_IEC_559__=1";
  command += " -D __STDC_IEC_559_COMPLEX__=1";
  command += " -D __STDC_ISO_10646__=1";
  
  for(std::list<std::string>::const_iterator
      it=config.ansi_c.defines.begin();
      it!=config.ansi_c.defines.end();
      it++)
    command+=" -D"+shell_quote(*it);

  for(std::list<std::string>::const_iterator
      it=config.ansi_c.include_paths.begin();
      it!=config.ansi_c.include_paths.end();
      it++)
    command+=" -I"+shell_quote(*it);

  for(std::list<std::string>::const_iterator
      it=config.ansi_c.include_files.begin();
      it!=config.ansi_c.include_files.end();
      it++)
    command+=" -include "+shell_quote(*it);

  for(std::list<std::string>::const_iterator
      it=config.ansi_c.preprocessor_options.begin();
      it!=config.ansi_c.preprocessor_options.end();
      it++)
    command+=" "+*it;
    
  int result;
  
  // the following forces the mode
  switch(mode)
  {
  case PREPROCESS_C: command+=" -x c"; break;
  case PREPROCESS_CPP: command+=" -x c++"; break;
  default:;
  }

  #ifdef _WIN32
  std::string tmpi=get_temporary_file("tmp.gcc", "");
  command+=" \""+file+"\"";
  command+=" -o \""+tmpi+"\"";
  command+=" 2> \""+stderr_file+"\"";

  // _popen isn't very reliable on WIN32
  // that's why we use system() and a temporary file
  result=system(command.c_str());

  FILE *stream=fopen(tmpi.c_str(), "r");

  // errors/warnings
  {
    std::ifstream stderr_stream(stderr_file.c_str());
    char ch;
    while((stderr_stream.read(&ch, 1))!=NULL)
      message_stream.str << ch;
  }

  unlink(stderr_file.c_str());

  if(stream!=NULL)
  {
    int ch;
    while((ch=fgetc(stream))!=EOF)
      outstream << (unsigned char)ch;

    fclose(stream);
    unlink(tmpi.c_str());
  }
  else
  {
    unlink(tmpi.c_str());
    message_stream.str << "GCC preprocessing failed (fopen failed)" << std::endl;
    result=1;
  }
  #else
  command+=" \""+file+"\"";
  command+=" 2> \""+stderr_file+"\"";

  FILE *stream=popen(command.c_str(), "r");

  if(stream!=NULL)
  {
    int ch;
    while((ch=fgetc(stream))!=EOF)
      outstream << (unsigned char)ch;

    result=pclose(stream);
  }
  else
  {
    message_stream.str << "GCC preprocessing failed (popen failed)" << std::endl;
    result=1;
  }

  // errors/warnings
  {
    std::ifstream stderr_stream(stderr_file.c_str());
    if(stderr_stream)
      message_stream.str << stderr_stream.rdbuf();
  }

  unlink(stderr_file.c_str());

  #endif

  if(result!=0)
  {
    message_stream.error_parse(1);
    message_stream.error("GCC preprocessing failed");
    return true;
  }
  else
    message_stream.error_parse(2);

  return false;
}

/*******************************************************************\

Function: c_preprocess_arm

  Inputs:

 Outputs:

 Purpose: ANSI-C preprocessing

\*******************************************************************/

bool c_preprocess_arm(
  preprocess_modet mode,
  const std::string &file,
  std::ostream &outstream,
  message_handlert &message_handler)
{
  // check extension
  if(is_dot_i_file(file))
    return c_preprocess_none(mode, file, outstream, message_handler);

  // preprocessing using armcc
  message_streamt message_stream(message_handler);

  std::string stderr_file=get_temporary_file("tmp.stderr", "");

  std::string command;
  
  command="armcc -E -D__CPROVER__";
  
//  command+=" -D__sizeof_int="+i2string(config.ansi_c.int_width/8);
//  command+=" -D__sizeof_long="+i2string(config.ansi_c.long_int_width/8);
//  command+=" -D__sizeof_ptr="+i2string(config.ansi_c.pointer_width/8);
  //command+=" -D__EDG_VERSION__=308";
  //command+=" -D__EDG__";
//  command+=" -D__CC_ARM=1";
  //command+=" -D__ARMCC_VERSION=410000";
//  command+=" -D__arm__";

//  if(config.ansi_c.endianness==configt::ansi_ct::IS_BIG_ENDIAN)
//    command+=" -D__BIG_ENDIAN";

//  if(config.ansi_c.char_is_unsigned)
//    command+=" -D__CHAR_UNSIGNED__";
    
  if(config.ansi_c.os!=configt::ansi_ct::OS_WIN)
  {
    command+=" -D__null=0";
    command+=" -D__WORDSIZE="+i2string(config.ansi_c.pointer_width);

    if(config.ansi_c.int_width==16)
      command+=GCC_DEFINES_16;
    else if(config.ansi_c.int_width==32)
      command+=GCC_DEFINES_32;
    else if(config.ansi_c.int_width==64)
      command+=GCC_DEFINES_LP64;
  }
      
  // Standard Defines, ANSI9899 6.10.8
  command+=" -D__STDC__";
  //command+=" -D__STDC_VERSION__=199901L";

  for(std::list<std::string>::const_iterator
      it=config.ansi_c.defines.begin();
      it!=config.ansi_c.defines.end();
      it++)
    command+=" \"-D"+*it+"\"";

  for(std::list<std::string>::const_iterator
      it=config.ansi_c.include_paths.begin();
      it!=config.ansi_c.include_paths.end();
      it++)
    command+=" \"-I"+*it+"\"";

  int result;

  #ifdef _WIN32
  std::string tmpi=get_temporary_file("tmp.cl", "");
  command+=" \""+file+"\"";
  command+=" > \""+tmpi+"\"";
  command+=" 2> \""+stderr_file+"\"";

  // _popen isn't very reliable on WIN32
  // that's why we use system() and a temporary file
  result=system(command.c_str());

  FILE *stream=fopen(tmpi.c_str(), "r");

  if(stream!=NULL)
  {
    int ch;
    while((ch=fgetc(stream))!=EOF)
      outstream << (unsigned char)ch;

    fclose(stream);
    unlink(tmpi.c_str());
  }
  else
  {
    unlink(tmpi.c_str());
    unlink(stderr_file.c_str());
    message_stream.error("ARMCC preprocessing failed (fopen failed)");
    return true;
  }
  #else
  command+=" \""+file+"\"";
  command+=" 2> \""+stderr_file+"\"";

  FILE *stream=popen(command.c_str(), "r");

  if(stream!=NULL)
  {
    int ch;
    while((ch=fgetc(stream))!=EOF)
      outstream << (unsigned char)ch;

    result=pclose(stream);
  }
  else
  {
    unlink(stderr_file.c_str());
    message_stream.error("ARMCC preprocessing failed (popen failed)");
    return true;
  }
  #endif

  // errors/warnings
  {
    std::ifstream stderr_stream(stderr_file.c_str());
    char ch;
    while((stderr_stream.read(&ch, 1))!=NULL)
      message_stream.str << ch;
  }

  unlink(stderr_file.c_str());

  if(result!=0)
  {
    message_stream.error_parse(1);
    message_stream.error("ARMCC preprocessing failed");
    return true;
  }
  else
    message_stream.error_parse(2);

  return false;
}

/*******************************************************************\

Function: c_preprocess_none

  Inputs:

 Outputs:

 Purpose: ANSI-C preprocessing

\*******************************************************************/

bool c_preprocess_none(
  preprocess_modet mode,
  const std::string &file,
  std::ostream &outstream,
  message_handlert &message_handler)
{
  #ifdef _MSC_VER
  std::ifstream infile(widen(file).c_str());
  #else
  std::ifstream infile(file.c_str());
  #endif
  
  if(!infile)
  {
    message_streamt message_stream(message_handler);
    message_stream.error("failed to open `"+file+"'");
    return true;
  }
  
  if(config.ansi_c.mode==configt::ansi_ct::MODE_CODEWARRIOR)
  {
    // special treatment for "/* #line"
    postprocess_codewarrior(infile, outstream);
  }
  else
  {
    char ch;

    while(infile.read(&ch, 1))
      outstream << ch;
  }

  return false;
}

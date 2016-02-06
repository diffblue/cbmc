/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cstdio>
#include <cstdlib>
#include <cstring>

#if defined(__linux__) || \
    defined(__FreeBSD_kernel__) || \
    defined(__GNU__) || \
    defined(__unix__) || \
    defined(__CYGWIN__) || \
    defined(__MACH__)
#include <unistd.h>
#endif

#include <fstream>

#include <util/config.h>
#include <util/i2string.h>
#include <util/message_stream.h>
#include <util/tempfile.h>
#include <util/unicode.h>
#include <util/arith_tools.h>
#include <util/std_types.h>

#include "c_types.h"
#include "c_preprocess.h"

#define GCC_DEFINES_16 \
  " -D__INT_MAX__=32767"\
  " -D__CHAR_BIT__=8"\
  " -D__SCHAR_MAX__=127"\
  " -D__SHRT_MAX__=32767"\
  " -D__LONG_LONG_MAX__=2147483647L"\
  " -D__LONG_MAX__=2147483647" \
  " -D__SIZE_TYPE__=\"unsigned int\""\
  " -D__PTRDIFF_TYPE__=int"\
  " -D__WINT_TYPE__=\"unsigned int\""\
  " -D__INTMAX_TYPE__=\"long long int\""\
  " -D__UINTMAX_TYPE__=\"long long unsigned int\""

#define GCC_DEFINES_32 \
  " -D__INT_MAX__=2147483647"\
  " -D__CHAR_BIT__=8"\
  " -D__SCHAR_MAX__=127"\
  " -D__SHRT_MAX__=32767"\
  " -D__LONG_LONG_MAX__=9223372036854775807LL"\
  " -D__LONG_MAX__=2147483647L" \
  " -D__SIZE_TYPE__=\"long unsigned int\""\
  " -D__PTRDIFF_TYPE__=int"\
  " -D__WINT_TYPE__=\"unsigned int\""\
  " -D__INTMAX_TYPE__=\"long long int\""\
  " -D__UINTMAX_TYPE__=\"long long unsigned int\""
                        
#define GCC_DEFINES_LP64 \
  " -D__INT_MAX__=2147483647"\
  " -D__CHAR_BIT__=8"\
  " -D__SCHAR_MAX__=127"\
  " -D__SHRT_MAX__=32767"\
  " -D__LONG_LONG_MAX__=9223372036854775807LL"\
  " -D__LONG_MAX__=9223372036854775807L"\
  " -D__SIZE_TYPE__=\"long unsigned int\""\
  " -D__PTRDIFF_TYPE__=long"\
  " -D__WINT_TYPE__=\"unsigned int\""\
  " -D__INTMAX_TYPE__=\"long int\""\
  " -D__UINTMAX_TYPE__=\"long unsigned int\""

#define GCC_DEFINES_LLP64 \
  " -D__INT_MAX__=2147483647"\
  " -D__CHAR_BIT__=8"\
  " -D__SCHAR_MAX__=127"\
  " -D__SHRT_MAX__=32767"\
  " -D__LONG_LONG_MAX__=9223372036854775807LL"\
  " -D__LONG_MAX__=2147483647"\
  " -D__SIZE_TYPE__=\"long long unsigned int\""\
  " -D__PTRDIFF_TYPE__=\"long long\""\
  " -D__WINT_TYPE__=\"unsigned int\""\
  " -D__INTMAX_TYPE__=\"long long int\""\
  " -D__UINTMAX_TYPE__=\"long long unsigned int\""

/*******************************************************************\

Function: type_max

  Inputs:

 Outputs:

 Purpose: produce a string with the maximum value of a given type

\*******************************************************************/

static std::string type_max(const typet &src)
{
  if(src.id()==ID_signedbv)
    return integer2string(
      power(2, to_signedbv_type(src).get_width()-1)-1);
  else if(src.id()==ID_unsignedbv)
    return integer2string(
      power(2, to_unsignedbv_type(src).get_width()-1)-1);
  else
    assert(false);
}

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
  std::istream &instream,
  std::ostream &outstream,
  message_handlert &message_handler)
{
  std::string file=get_temporary_file("tmp.stdin", ".c");
  FILE *tmp=fopen(file.c_str(), "wt");

  char ch;
  while(instream.read(&ch, 1))
    fputc(ch, tmp);

  fclose(tmp);

  bool result=c_preprocess(file, outstream, message_handler);
  
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

bool c_preprocess_codewarrior(const std::string &, std::ostream &, message_handlert &);
bool c_preprocess_arm(const std::string &, std::ostream &, message_handlert &);
bool c_preprocess_gcc_clang(const std::string &, std::ostream &, message_handlert &, configt::ansi_ct::preprocessort);
bool c_preprocess_none(const std::string &, std::ostream &, message_handlert &);
bool c_preprocess_visual_studio(const std::string &, std::ostream &, message_handlert &);

bool c_preprocess(
  const std::string &path,
  std::ostream &outstream,
  message_handlert &message_handler)
{
  switch(config.ansi_c.preprocessor)
  {
  case configt::ansi_ct::preprocessort::PP_CODEWARRIOR:
    return c_preprocess_codewarrior(path, outstream, message_handler);
  
  case configt::ansi_ct::preprocessort::PP_GCC:
    return c_preprocess_gcc_clang(path, outstream, message_handler, config.ansi_c.preprocessor);
  
  case configt::ansi_ct::preprocessort::PP_CLANG:
    return c_preprocess_gcc_clang(path, outstream, message_handler, config.ansi_c.preprocessor);
  
  case configt::ansi_ct::preprocessort::PP_VISUAL_STUDIO:
    return c_preprocess_visual_studio(path, outstream, message_handler);
  
  case configt::ansi_ct::preprocessort::PP_ARM:
    return c_preprocess_arm(path, outstream, message_handler);
  
  case configt::ansi_ct::preprocessort::NO_PP:
    return c_preprocess_none(path, outstream, message_handler);
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
  const std::string &file,
  std::ostream &outstream,
  message_handlert &message_handler)
{
  // check extension
  if(is_dot_i_file(file))
    return c_preprocess_none(file, outstream, message_handler);

  message_streamt message_stream(message_handler);

  // use Visual Studio's CL
  
  std::string stderr_file=get_temporary_file("tmp.stderr", "");
  std::string command_file_name=get_temporary_file("tmp.cl-cmd", "");

  {
    std::ofstream command_file(command_file_name.c_str());

    // This marks the file as UTF-8, which Visual Studio
    // understands.
    command_file << char(0xef) << char(0xbb) << char(0xbf);
  
    command_file << "/nologo" << "\n";
    command_file << "/E" << "\n";
    command_file << "/D__CPROVER__" << "\n";
    command_file << "/D__WORDSIZE=" << config.ansi_c.pointer_width << "\n";

    if(config.ansi_c.pointer_width==64)
    {
      command_file << "\"/D__PTRDIFF_TYPE__=long long int\""  << "\n";
      // yes, both _WIN32 and _WIN64 get defined
      command_file << "/D_WIN64" << "\n";
    }
    else
    {
      command_file << "/D__PTRDIFF_TYPE__=int" << "\n";
      command_file << "/U_WIN64" << "\n";
    }

    if(config.ansi_c.char_is_unsigned)
      command_file << "/J" << "\n"; // This causes _CHAR_UNSIGNED to be defined

    // Standard Defines, ANSI9899 6.10.8
    command_file << "/D__STDC_VERSION__=199901L" << "\n";
    command_file << "/D__STDC_IEC_559__=1" << "\n";
    command_file << "/D__STDC_IEC_559_COMPLEX__=1" << "\n";
    command_file << "/D__STDC_ISO_10646__=1" << "\n";
  
    for(std::list<std::string>::const_iterator
        it=config.ansi_c.defines.begin();
        it!=config.ansi_c.defines.end();
        it++)
      command_file << "/D" << shell_quote(*it) << "\n";

    for(std::list<std::string>::const_iterator
        it=config.ansi_c.include_paths.begin();
        it!=config.ansi_c.include_paths.end();
        it++)
      command_file << "/I" << shell_quote(*it) << "\n";

       for(std::list<std::string>::const_iterator
               it=config.ansi_c.include_files.begin();
               it!=config.ansi_c.include_files.end();
               it++)
         command_file << "/FI" << shell_quote(*it) << "\n";

    // Finally, the file to be preprocessed
    // (this is already in UTF-8).
    command_file << shell_quote(file) << "\n";
  }
  
  std::string tmpi=get_temporary_file("tmp.cl", "");
  
  std::string command="CL @\""+command_file_name+"\"";
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
    message_stream.str << "CL Preprocessing failed (fopen failed)";
    message_stream.error_msg();
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
    while(stderr_stream.read(&ch, 1))
      message_stream.str << ch;
  }

  unlink(stderr_file.c_str());

  if(result!=0)
  {
    message_stream.error_parse(1);
    message_stream.str << "CL Preprocessing failed";
    message_stream.error_msg();
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
      outstream << line.c_str()+3 << "\n"; // strip the '/* '
    }
    else
      outstream << line << "\n";
  }
}

/*******************************************************************\

Function: c_preprocess_codewarrior

  Inputs:

 Outputs:

 Purpose: ANSI-C preprocessing

\*******************************************************************/

bool c_preprocess_codewarrior(
  const std::string &file,
  std::ostream &outstream,
  message_handlert &message_handler)
{
  // check extension
  if(is_dot_i_file(file))
    return c_preprocess_none(file, outstream, message_handler);

  // preprocessing
  message_streamt message_stream(message_handler);

  std::string stderr_file=get_temporary_file("tmp.stderr", "");

  std::string command;
  
  command="mwcceppc -E -P -D__CPROVER__ -ppopt line -ppopt full";

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
    message_stream.str << "Preprocessing failed (fopen failed)";
    message_stream.error_msg();
    return true;
  }

  // errors/warnings
  {
    std::ifstream stderr_stream(stderr_file.c_str());
    char ch;
    while(stderr_stream.read(&ch, 1))
      message_stream.str << ch;
  }

  unlink(stderr_file.c_str());

  if(result!=0)
  {
    message_stream.error_parse(1);
    message_stream.str << "Preprocessing failed";
    message_stream.error_msg();
    return true;
  }
  else
    message_stream.error_parse(2);

  return false;
}

/*******************************************************************\

Function: c_preprocess_gcc_clang

  Inputs:

 Outputs:

 Purpose: ANSI-C preprocessing

\*******************************************************************/

bool c_preprocess_gcc_clang(
  const std::string &file,
  std::ostream &outstream,
  message_handlert &message_handler,
  configt::ansi_ct::preprocessort preprocessor)
{
  // check extension
  if(is_dot_i_file(file))
    return c_preprocess_none(file, outstream, message_handler);

  // preprocessing
  message_streamt message_stream(message_handler);

  std::string stderr_file=get_temporary_file("tmp.stderr", "");

  std::string command;
  
  if(preprocessor==configt::ansi_ct::preprocessort::PP_CLANG)
    command="clang";
  else
    command="gcc";
  
  command +=" -E -undef -D__CPROVER__";

  command+=" -D__WORDSIZE="+i2string(config.ansi_c.pointer_width);
  
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

  if(preprocessor==configt::ansi_ct::preprocessort::PP_CLANG)
    command+=" -D_Noreturn=\"__attribute__((__noreturn__))\"";

  if(config.ansi_c.int_width==16)
    command+=GCC_DEFINES_16;
  else if(config.ansi_c.int_width==32)
  {
    if(config.ansi_c.pointer_width==64)
    {
      if(config.ansi_c.long_int_width==32)
        command+=GCC_DEFINES_LLP64; // Windows, for instance
      else
        command+=GCC_DEFINES_LP64;
    }
    else
      command+=GCC_DEFINES_32;
  }
  
  // The width of wchar_t depends on the OS!
  {
    command+=" -D__WCHAR_MAX__="+type_max(wchar_t_type());
    
    std::string sig=config.ansi_c.wchar_t_is_unsigned?"unsigned":"signed";
    
    if(config.ansi_c.wchar_t_width==config.ansi_c.short_int_width)
      command+=" -D__WCHAR_TYPE__=\""+sig+" short int\"";
    else if(config.ansi_c.wchar_t_width==config.ansi_c.int_width)
      command+=" -D__WCHAR_TYPE__=\""+sig+" int\"";
    else if(config.ansi_c.wchar_t_width==config.ansi_c.long_int_width)
      command+=" -D__WCHAR_TYPE__=\""+sig+" long int\"";
    else if(config.ansi_c.wchar_t_width==config.ansi_c.char_width)
      command+=" -D__WCHAR_TYPE__=\""+sig+" char\"";
    else
      assert(false);
  }

  if(config.ansi_c.char_is_unsigned)
    command+=" -D __CHAR_UNSIGNED__"; // gcc

  switch(config.ansi_c.os)
  {
  case configt::ansi_ct::ost::OS_LINUX:
    command+=" -Dlinux -D__linux -D__linux__ -D__gnu_linux__";
    command+=" -Dunix -D__unix -D__unix__";
    command+=" -D__USE_UNIX98";
    break;

  case configt::ansi_ct::ost::OS_MACOS:
    command+=" -D__APPLE__ -D__MACH__";
    // needs to be __APPLE_CPP__ for C++
    command+=" -D__APPLE_CC__";
    break;

  case configt::ansi_ct::ost::OS_WIN:
    command+=" -D _WIN32";

    if(config.ansi_c.mode!=configt::ansi_ct::flavourt::MODE_VISUAL_STUDIO_C_CPP)
      command+=" -D _M_IX86=Blend";

    if(config.ansi_c.arch=="x86_64")
      command+=" -D _WIN64"; // yes, both _WIN32 and _WIN64 get defined

    if(config.ansi_c.char_is_unsigned)
      command+=" -D _CHAR_UNSIGNED"; // This is Visual Studio
    break;

  case configt::ansi_ct::ost::NO_OS:
    command+=" -nostdinc"; // make sure we don't mess with the system library
    break;
    
  default:
    assert(false);
  }
  
  // Standard Defines, ANSI9899 6.10.8
  switch(config.ansi_c.c_standard)
  {
  case configt::ansi_ct::c_standardt::C89:
    break; // __STDC_VERSION__ is not defined

  case configt::ansi_ct::c_standardt::C99:
    command += " -D __STDC_VERSION__=199901L";
    break;

  case configt::ansi_ct::c_standardt::C11:
    command += " -D __STDC_VERSION__=201112L";
    break;
  }

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
  switch(config.ansi_c.mode)
  {
  case configt::ansi_ct::flavourt::MODE_GCC_C: command+=" -x c"; break;
  case configt::ansi_ct::flavourt::MODE_GCC_CPP: command+=" -x c++"; break;
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
    while(stderr_stream.read(&ch, 1))
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
    message_stream.str << "GCC preprocessing failed";
    message_stream.error_msg();
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
  const std::string &file,
  std::ostream &outstream,
  message_handlert &message_handler)
{
  // check extension
  if(is_dot_i_file(file))
    return c_preprocess_none(file, outstream, message_handler);

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
    
  if(config.ansi_c.os!=configt::ansi_ct::ost::OS_WIN)
  {
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
    command+=" "+shell_quote("-D"+*it);

  for(std::list<std::string>::const_iterator
      it=config.ansi_c.include_paths.begin();
      it!=config.ansi_c.include_paths.end();
      it++)
    command+=" "+shell_quote("-I"+*it);

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
    message_stream.str << "ARMCC preprocessing failed (fopen failed)";
    message_stream.error_msg();
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
    message_stream.str << "ARMCC preprocessing failed (popen failed)";
    message_stream.error_msg();
    return true;
  }
  #endif

  // errors/warnings
  {
    std::ifstream stderr_stream(stderr_file.c_str());
    char ch;
    while(stderr_stream.read(&ch, 1))
      message_stream.str << ch;
  }

  unlink(stderr_file.c_str());

  if(result!=0)
  {
    message_stream.error_parse(1);
    message_stream.str << "ARMCC preprocessing failed";
    message_stream.error_msg();
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
    message_stream.str << "failed to open `" << file << "'";
    message_stream.error_msg();
    return true;
  }
  
  if(config.ansi_c.mode==configt::ansi_ct::flavourt::MODE_CODEWARRIOR_C_CPP)
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

/*******************************************************************\

Function: test_c_preprocessor

  Inputs:

 Outputs:

 Purpose: tests ANSI-C preprocessing

\*******************************************************************/

const char c_test_program[]=
  "#include <stdlib.h>\n"
  "\n"
  "int main() { }\n";

bool test_c_preprocessor(message_handlert &message_handler)
{
  std::ostringstream out;
  std::istringstream in(c_test_program);
  
  return c_preprocess(in, out, message_handler);
}

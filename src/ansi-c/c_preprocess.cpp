/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "c_preprocess.h"

#include <util/c_types.h>
#include <util/config.h>
#include <util/suffix.h>
#include <util/tempfile.h>
#include <util/unicode.h>

#include <fstream>

#if defined(__linux__) || \
    defined(__FreeBSD_kernel__) || \
    defined(__GNU__) || \
    defined(__unix__) || \
    defined(__CYGWIN__) || \
    defined(__MACH__)
#include <unistd.h>
#endif

/// quote a string for bash and CMD
static std::string shell_quote(const std::string &src)
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

  for(const char ch : src)
  {
    if(ch=='"')
      result+='"'; // quotes are doubled
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

  for(const char ch : src)
  {
    if(ch=='\'')
      result+="'\\''";
    result+=ch;
  }

  result+='\'';

  return result;
  #endif
}

static void error_parse_line(
  const std::string &line,
  bool warning_only,
  messaget &message)
{
  std::string error_msg=line;
  source_locationt saved_error_location;

  if(has_prefix(line, "file "))
  {
    const char *tptr=line.c_str();
    int state=0;
    std::string file, line_no, column, _error_msg, function;

    tptr+=5;

    char previous=0;

    while(*tptr!=0)
    {
      if(has_prefix(tptr, " line ") && state != 4)
      {
        state=1;
        tptr+=6;
        continue;
      }
      else if(has_prefix(tptr, " column ") && state != 4)
      {
        state=2;
        tptr+=8;
        continue;
      }
      else if(has_prefix(tptr, " function ") && state != 4)
      {
        state=3;
        tptr+=10;
        continue;
      }
      else if(*tptr==':' && state!=4)
      {
        if(tptr[1]==' ' && previous!=':')
        {
          state=4;
          tptr++;
          while(*tptr==' ') tptr++;
          continue;
        }
      }

      if(state==0) // file
        file+=*tptr;
      else if(state==1) // line number
        line_no+=*tptr;
      else if(state==2) // column
        column+=*tptr;
      else if(state==3) // function
        function+=*tptr;
      else if(state==4) // error message
        _error_msg+=*tptr;

      previous=*tptr;

      tptr++;
    }

    if(state==4)
    {
      saved_error_location.set_file(file);
      saved_error_location.set_function(function);
      saved_error_location.set_line(line_no);
      saved_error_location.set_column(column);
      error_msg=_error_msg;
    }
  }
  else if(has_prefix(line, "In file included from "))
  {
  }
  else
  {
    const char *tptr=line.c_str();
    int state=0;
    std::string file, line_no;

    while(*tptr!=0)
    {
      if(state==0)
      {
        if(*tptr==':')
          state++;
        else
          file+=*tptr;
      }
      else if(state==1)
      {
        if(*tptr==':')
          state++;
        else if(isdigit(*tptr))
          line_no+=*tptr;
        else
          state=3;
      }

      tptr++;
    }

    if(state==2)
    {
      saved_error_location.set_file(file);
      saved_error_location.set_function("");
      saved_error_location.set_line(line_no);
      saved_error_location.set_column("");
    }
  }

  messaget::mstreamt &m=
    warning_only ? message.warning() : message.error();
  m.source_location=saved_error_location;
  m << error_msg << messaget::eom;
}

static void error_parse(
  std::istream &errors,
  bool warning_only,
  messaget &message)
{
  std::string line;

  while(std::getline(errors, line))
    error_parse_line(line, warning_only, message);
}

/// ANSI-C preprocessing
bool c_preprocess(
  std::istream &instream,
  std::ostream &outstream,
  message_handlert &message_handler)
{
  temporary_filet tmp_file("tmp.stdin", ".c");

  std::ofstream tmp(tmp_file());

  if(!tmp)
  {
    messaget message(message_handler);
    message.error() << "failed to open temporary file" << messaget::eom;
    return true; // error
  }

  tmp << instream.rdbuf(); // copy

  tmp.close(); // flush

  bool result=c_preprocess(tmp_file(), outstream, message_handler);

  return result;
}

/// ANSI-C preprocessing
static bool is_dot_i_file(const std::string &path)
{
  return has_suffix(path, ".i") || has_suffix(path, ".ii");
}

/// ANSI-C preprocessing
bool c_preprocess_codewarrior(
  const std::string &, std::ostream &, message_handlert &);
bool c_preprocess_arm(
  const std::string &, std::ostream &, message_handlert &);
bool c_preprocess_gcc_clang(
  const std::string &,
  std::ostream &,
  message_handlert &,
  configt::ansi_ct::preprocessort);
bool c_preprocess_none(
  const std::string &, std::ostream &, message_handlert &);
bool c_preprocess_visual_studio(
  const std::string &, std::ostream &, message_handlert &);

bool c_preprocess(
  const std::string &path,
  std::ostream &outstream,
  message_handlert &message_handler)
{
  switch(config.ansi_c.preprocessor)
  {
  case configt::ansi_ct::preprocessort::CODEWARRIOR:
    return c_preprocess_codewarrior(path, outstream, message_handler);

  case configt::ansi_ct::preprocessort::GCC:
    return
      c_preprocess_gcc_clang(
        path, outstream, message_handler, config.ansi_c.preprocessor);

  case configt::ansi_ct::preprocessort::CLANG:
    return
      c_preprocess_gcc_clang(
        path, outstream, message_handler, config.ansi_c.preprocessor);

  case configt::ansi_ct::preprocessort::VISUAL_STUDIO:
    return c_preprocess_visual_studio(path, outstream, message_handler);

  case configt::ansi_ct::preprocessort::ARM:
    return c_preprocess_arm(path, outstream, message_handler);

  case configt::ansi_ct::preprocessort::NONE:
    return c_preprocess_none(path, outstream, message_handler);
  }

  // not reached
  return true;
}

/// ANSI-C preprocessing
bool c_preprocess_visual_studio(
  const std::string &file,
  std::ostream &outstream,
  message_handlert &message_handler)
{
  // check extension
  if(is_dot_i_file(file))
    return c_preprocess_none(file, outstream, message_handler);

  messaget message(message_handler);

  // use Visual Studio's CL

  std::string stderr_file=get_temporary_file("tmp.stderr", "");
  std::string command_file_name=get_temporary_file("tmp.cl-cmd", "");

  {
    std::ofstream command_file(command_file_name);

    // This marks the command file as UTF-8, which Visual Studio
    // understands.
    command_file << char(0xef) << char(0xbb) << char(0xbf);

    command_file << "/nologo" << '\n';
    command_file << "/E" << '\n';

    // This option will make CL produce utf-8 output, as
    // opposed to 8-bit with some code page.
    // It only works on Visual Studio 2015 or newer.
    command_file << "/source-charset:utf-8" << '\n';

    command_file << "/D__CPROVER__" << "\n";
    command_file << "/D__WORDSIZE=" << config.ansi_c.pointer_width << "\n";

    if(pointer_diff_type()==signed_long_long_int_type())
    {
      command_file << "\"/D__PTRDIFF_TYPE__=long long int\""  << "\n";
      // yes, both _WIN32 and _WIN64 get defined
      command_file << "/D_WIN64" << "\n";
    }
    else if(config.ansi_c.int_width == 16 && config.ansi_c.pointer_width == 32)
    {
      // 16-bit LP32 is an artificial architecture we simulate when using --16
      DATA_INVARIANT(
        pointer_diff_type() == signed_long_int_type(),
        "Pointer difference expected to be long int typed");
      command_file << "/D__PTRDIFF_TYPE__=long" << '\n';
    }
    else
    {
      DATA_INVARIANT(
        pointer_diff_type()==signed_int_type(),
        "Pointer difference expected to be int typed");
      command_file << "/D__PTRDIFF_TYPE__=int" << "\n";
    }

    if(config.ansi_c.char_is_unsigned)
      command_file << "/J" << "\n"; // This causes _CHAR_UNSIGNED to be defined

    for(const auto &define : config.ansi_c.defines)
      command_file << "/D" << shell_quote(define) << "\n";

    for(const auto &include_path : config.ansi_c.include_paths)
      command_file << "/I" << shell_quote(include_path) << "\n";

    for(const auto &include_file : config.ansi_c.include_files)
      command_file << "/FI" << shell_quote(include_file) << "\n";

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

  std::ifstream instream(tmpi);

  if(!instream)
  {
    unlink(tmpi.c_str());
    unlink(stderr_file.c_str());
    unlink(command_file_name.c_str());
    message.error() << "CL Preprocessing failed (open failed)"
                    << messaget::eom;
    return true;
  }

  outstream << instream.rdbuf(); // copy

  instream.close();
  unlink(tmpi.c_str());
  unlink(command_file_name.c_str());

  // errors/warnings
  std::ifstream stderr_stream(stderr_file);
  error_parse(stderr_stream, result==0, message);

  unlink(stderr_file.c_str());

  if(result!=0)
  {
    message.error() << "CL Preprocessing failed" << messaget::eom;
    return true;
  }

  return false;
}

/// post-processing specifically for CodeWarrior
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

/// ANSI-C preprocessing
bool c_preprocess_codewarrior(
  const std::string &file,
  std::ostream &outstream,
  message_handlert &message_handler)
{
  // check extension
  if(is_dot_i_file(file))
    return c_preprocess_none(file, outstream, message_handler);

  // preprocessing
  messaget message(message_handler);

  std::string stderr_file=get_temporary_file("tmp.stderr", "");

  std::string command;

  command="mwcceppc -E -P -D__CPROVER__ -ppopt line -ppopt full";

  for(const auto &define : config.ansi_c.defines)
    command+=" -D"+shell_quote(define);

  for(const auto &include_path : config.ansi_c.include_paths)
    command+=" -I"+shell_quote(include_path);

  for(const auto &include_file : config.ansi_c.include_files)
    command+=" -include "+shell_quote(include_file);

  for(const auto &opt : config.ansi_c.preprocessor_options)
    command+=" "+opt;

  int result;

  std::string tmpi=get_temporary_file("tmp.cl", "");
  command+=" \""+file+"\"";
  command+=" -o \""+tmpi+"\"";
  command+=" 2> \""+stderr_file+"\"";

  result=system(command.c_str());

  std::ifstream stream_i(tmpi);

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
    message.error() << "Preprocessing failed (fopen failed)"
                    << messaget::eom;
    return true;
  }

  // errors/warnings
  std::ifstream stderr_stream(stderr_file);
  error_parse(stderr_stream, result==0, message);

  unlink(stderr_file.c_str());

  if(result!=0)
  {
    message.error() << "Preprocessing failed" << messaget::eom;
    return true;
  }

  return false;
}

/// ANSI-C preprocessing
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
  messaget message(message_handler);

  std::string stderr_file=get_temporary_file("tmp.stderr", "");

  std::string command;

  if(preprocessor==configt::ansi_ct::preprocessort::CLANG)
    command="clang";
  else
    command="gcc";

  command += " -E -D__CPROVER__";

  if(config.ansi_c.pointer_width == 16)
    command += " -m16";
  else if(config.ansi_c.pointer_width == 32)
    command += " -m32";
  else if(config.ansi_c.pointer_width == 64)
    command += " -m64";

  // The width of wchar_t depends on the OS!
  if(config.ansi_c.wchar_t_width == config.ansi_c.short_int_width)
    command += " -fshort-wchar";

  if(config.ansi_c.char_is_unsigned)
    command += " -funsigned-char";

  if(config.ansi_c.os == configt::ansi_ct::ost::NO_OS)
    command += " -nostdinc";

  // Set the standard
  if(has_suffix(file, ".cpp") || has_suffix(file, ".CPP") ||
#ifndef _WIN32
     has_suffix(file, ".C") ||
#endif
     has_suffix(file, ".c++") || has_suffix(file, ".C++") ||
     has_suffix(file, ".cp") || has_suffix(file, ".CP"))
  {
    switch(config.cpp.cpp_standard)
    {
    case configt::cppt::cpp_standardt::CPP98:
      command += " -std=gnu++98";
      break;

    case configt::cppt::cpp_standardt::CPP03:
      command += " -std=gnu++03";
      break;

    case configt::cppt::cpp_standardt::CPP11:
      command += " -std=gnu++11";
      break;

    case configt::cppt::cpp_standardt::CPP14:
      command += " -std=gnu++14";
      break;
    }
  }
  else
  {
    switch(config.ansi_c.c_standard)
    {
    case configt::ansi_ct::c_standardt::C89:
      command += " -std=gnu++89";
      break;

    case configt::ansi_ct::c_standardt::C99:
      command += " -std=gnu99";
      break;

    case configt::ansi_ct::c_standardt::C11:
      command += " -std=gnu11";
      break;
    }
  }

  for(const auto &define : config.ansi_c.defines)
    command+=" -D"+shell_quote(define);

  for(const auto &include_path : config.ansi_c.include_paths)
    command+=" -I"+shell_quote(include_path);

  for(const auto &include_file : config.ansi_c.include_files)
    command+=" -include "+shell_quote(include_file);

  for(const auto &opt : config.ansi_c.preprocessor_options)
    command+=" "+opt;

  int result;

  #if 0
  // the following forces the mode
  switch(config.ansi_c.mode)
  {
  case configt::ansi_ct::flavourt::GCC_C: command+=" -x c"; break;
  case configt::ansi_ct::flavourt::GCC_CPP: command+=" -x c++"; break;
  default:
    {
    }
  }
  #endif

  #ifdef _WIN32
  std::string tmpi=get_temporary_file("tmp.gcc", "");
  command+=" \""+file+"\"";
  command+=" -o \""+tmpi+"\"";
  command+=" 2> \""+stderr_file+"\"";

  // _popen isn't very reliable on WIN32
  // that's why we use system() and a temporary file
  result=system(command.c_str());

  std::ifstream instream(tmpi);

  // errors/warnings
  std::ifstream stderr_stream(stderr_file);
  error_parse(stderr_stream, result==0, message);

  unlink(stderr_file.c_str());

  if(instream)
  {
    outstream << instream.rdbuf();
    instream.close();
    unlink(tmpi.c_str());
  }
  else
  {
    unlink(tmpi.c_str());
    message.error() << "GCC preprocessing failed (open failed)"
                    << messaget::eom;
    result=1;
  }
  #else
  command+=" \""+file+"\"";
  command+=" 2> \""+stderr_file+"\"";

  FILE *stream=popen(command.c_str(), "r");

  if(stream!=nullptr)
  {
    int ch;
    while((ch=fgetc(stream))!=EOF)
      outstream << (unsigned char)ch;

    result=pclose(stream);
  }
  else
  {
    message.error() << "GCC preprocessing failed (popen failed)"
                    << messaget::eom;
    result=1;
  }

  // errors/warnings
  std::ifstream stderr_stream(stderr_file);
  error_parse(stderr_stream, result==0, message);

  unlink(stderr_file.c_str());

  #endif

  if(result!=0)
  {
    message.error() << "GCC preprocessing failed" << messaget::eom;
    return true;
  }

  return false;
}

/// ANSI-C preprocessing
bool c_preprocess_arm(
  const std::string &file,
  std::ostream &outstream,
  message_handlert &message_handler)
{
  // check extension
  if(is_dot_i_file(file))
    return c_preprocess_none(file, outstream, message_handler);

  // preprocessing using armcc
  messaget message(message_handler);

  std::string stderr_file=get_temporary_file("tmp.stderr", "");

  std::string command;

  command="armcc -E -D__CPROVER__";

  if(config.ansi_c.endianness == configt::ansi_ct::endiannesst::IS_BIG_ENDIAN)
    command += " --bigend";
  else
    command += " --littleend";

  if(config.ansi_c.char_is_unsigned)
    command += " --unsigned_chars";
  else
    command += " --signed_chars";

  // Set the standard
  switch(config.ansi_c.c_standard)
  {
  case configt::ansi_ct::c_standardt::C89:
    command += " --c90";
    break;

  case configt::ansi_ct::c_standardt::C99:
  case configt::ansi_ct::c_standardt::C11:
    command += " --c99";
    break;
  }

  for(const auto &define : config.ansi_c.defines)
    command+=" "+shell_quote("-D"+define);

  for(const auto &include_path : config.ansi_c.include_paths)
    command+=" "+shell_quote("-I"+include_path);

  int result;

  #ifdef _WIN32
  std::string tmpi=get_temporary_file("tmp.cl", "");
  command+=" \""+file+"\"";
  command+=" > \""+tmpi+"\"";
  command+=" 2> \""+stderr_file+"\"";

  // _popen isn't very reliable on WIN32
  // that's why we use system() and a temporary file
  result=system(command.c_str());

  std::ifstream instream(tmpi);

  if(!instream)
  {
    outstream << instream.rdbuf(); // copy
    instream.close();
    unlink(tmpi.c_str());
  }
  else
  {
    unlink(tmpi.c_str());
    unlink(stderr_file.c_str());
    message.error() << "ARMCC preprocessing failed (fopen failed)"
                    << messaget::eom;
    return true;
  }
  #else
  command+=" \""+file+"\"";
  command+=" 2> \""+stderr_file+"\"";

  FILE *stream=popen(command.c_str(), "r");

  if(stream!=nullptr)
  {
    int ch;
    while((ch=fgetc(stream))!=EOF)
      outstream << (unsigned char)ch;

    result=pclose(stream);
  }
  else
  {
    unlink(stderr_file.c_str());
    message.error() << "ARMCC preprocessing failed (popen failed)"
                    << messaget::eom;
    return true;
  }
  #endif

  // errors/warnings
  std::ifstream stderr_stream(stderr_file);
  error_parse(stderr_stream, result==0, message);

  unlink(stderr_file.c_str());

  if(result!=0)
  {
    message.error() << "ARMCC preprocessing failed" << messaget::eom;
    return true;
  }

  return false;
}

/// ANSI-C preprocessing
bool c_preprocess_none(
  const std::string &file,
  std::ostream &outstream,
  message_handlert &message_handler)
{
  #ifdef _MSC_VER
  std::ifstream infile(widen(file));
  #else
  std::ifstream infile(file);
  #endif

  if(!infile)
  {
    messaget message(message_handler);
    message.error() << "failed to open `" << file << "'" << messaget::eom;
    return true;
  }

  if(config.ansi_c.mode==configt::ansi_ct::flavourt::CODEWARRIOR)
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

/// tests ANSI-C preprocessing
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

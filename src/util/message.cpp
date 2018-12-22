/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#include "message.h"

#include "string2int.h"

void message_handlert::print(
  unsigned level,
  const std::string &message,
  const source_locationt &location)
{
  std::string dest;

  const irep_idt &file=location.get_file();
  const irep_idt &line=location.get_line();
  const irep_idt &column=location.get_column();
  const irep_idt &function=location.get_function();

  if(!file.empty())
  {
    if(dest!="")
      dest+=' ';
    dest+="file "+id2string(file);
  }
  if(!line.empty())
  {
    if(dest!="")
      dest+=' ';
    dest+="line "+id2string(line);
  }
  if(!column.empty())
  {
    if(dest!="")
      dest+=' ';
    dest+="column "+id2string(column);
  }
  if(!function.empty())
  {
    if(dest!="")
      dest+=' ';
    dest+="function "+id2string(function);
  }

  if(dest!="")
    dest+=": ";
  dest+=message;

  print(level, dest);
}

void message_handlert::print(
  unsigned level,
  const std::string &)
{
  if(level>=message_count.size())
    message_count.resize(level+1, 0);
  ++message_count[level];
}

messaget::~messaget()
{
}

// Visual studio requires this (empty) static object
messaget::eomt messaget::eom;

const messaget::commandt messaget::reset(0);
const messaget::commandt messaget::bold(1);
const messaget::commandt messaget::faint(2);
const messaget::commandt messaget::italic(3);
const messaget::commandt messaget::underline(4);
const messaget::commandt messaget::red(31);
const messaget::commandt messaget::green(32);
const messaget::commandt messaget::yellow(33);
const messaget::commandt messaget::blue(34);
const messaget::commandt messaget::magenta(35);
const messaget::commandt messaget::cyan(36);
const messaget::commandt messaget::bright_red(91);
const messaget::commandt messaget::bright_green(92);
const messaget::commandt messaget::bright_yellow(93);
const messaget::commandt messaget::bright_blue(94);
const messaget::commandt messaget::bright_magenta(95);
const messaget::commandt messaget::bright_cyan(96);

/// Parse a (user-)provided string as a verbosity level and set it as the
/// verbosity of dest.
/// \param user_input:  Input string; if empty, the default verbosity is used.
/// \param default_verbosity:  Verbosity to use if no value is provided.
/// \param dest:  message handler the verbosity of which is to be set.
/// \return Computed verbosity
unsigned messaget::eval_verbosity(
  const std::string &user_input,
  const message_levelt default_verbosity,
  message_handlert &dest)
{
  unsigned v = default_verbosity;

  if(!user_input.empty())
  {
    v = unsafe_string2unsigned(user_input);

    if(v > messaget::M_DEBUG)
    {
      dest.print(
        messaget::M_WARNING,
        "verbosity value " + user_input + " out of range, using debug-level (" +
          std::to_string(messaget::M_DEBUG) + ") verbosity",
        source_locationt());

      v = messaget::M_DEBUG;
    }
  }

  dest.set_verbosity(v);

  return v;
}

/// Generate output to \p message_stream using \p output_generator if the
/// configured verbosity is at least as high as that of \p message_stream.  Use
/// whenever generating output involves additional computational effort that
/// should only be spent when such output will actually be displayed.
/// \param message_stream:  Output message stream
/// \param output_generator:  Function generating output
void messaget::conditional_output(
  mstreamt &message_stream,
  const std::function<void(mstreamt &)> &output_generator) const
{
  if(
    message_handler &&
    message_handler->get_verbosity() >= message_stream.message_level)
  {
    output_generator(mstream);
  }
}

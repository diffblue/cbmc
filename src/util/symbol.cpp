/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "symbol.h"

#include <ostream>

#include "source_location.h"
#include "std_expr.h"

/// Dump the state of a symbol object to a given output stream.
/// \param out: The stream to output object state to.
void symbolt::show(std::ostream &out) const
{
  out << "  " << name << '\n';
  out << "    type:  " << type.pretty(4) << '\n'
      << "    value: " << value.pretty(4) << '\n';

  out << "  flags:";
  if(is_lvalue)
    out << " lvalue";
  if(is_static_lifetime)
    out << " static_lifetime";
  if(is_thread_local)
    out << " thread_local";
  if(is_file_local)
    out << " file_local";
  if(is_type)
    out << " type";
  if(is_extern)
    out << " extern";
  if(is_input)
    out << " input";
  if(is_output)
    out << " output";
  if(is_macro)
    out << " macro";
  if(is_parameter)
    out << " parameter";
  if(is_auxiliary)
    out << " auxiliary";
  if(is_weak)
    out << " weak";
  if(is_property)
    out << " property";
  if(is_state_var)
    out << " state_var";
  if(is_exported)
    out << " exported";
  if(is_volatile)
    out << " volatile";
  if(!mode.empty())
    out << " mode=" << mode;
  if(!base_name.empty())
    out << " base_name=" << base_name;
  if(!module.empty())
    out << " module=" << module;
  if(!pretty_name.empty())
    out << " pretty_name=" << pretty_name;
  out << '\n';
  out << "  location: " << location << '\n';

  out << '\n';
}

/// Overload of stream operator to work with symbols.
/// \param out: A given stream to dump symbol state to.
/// \param symbol: The symbol whose state is about to be dumped.
/// \return The output stream.
std::ostream &operator<<(std::ostream &out,
                         const symbolt &symbol)
{
  symbol.show(out);
  return out;
}

/// Swap values between two symbols.
/// \param b: The second symbol to swap values with.
void symbolt::swap(symbolt &b)
{
  #define SYM_SWAP1(x) x.swap(b.x)

  SYM_SWAP1(type);
  SYM_SWAP1(value);
  SYM_SWAP1(name);
  SYM_SWAP1(pretty_name);
  SYM_SWAP1(module);
  SYM_SWAP1(base_name);
  SYM_SWAP1(mode);
  SYM_SWAP1(location);

  #define SYM_SWAP2(x) std::swap(x, b.x)

  SYM_SWAP2(is_type);
  SYM_SWAP2(is_macro);
  SYM_SWAP2(is_exported);
  SYM_SWAP2(is_input);
  SYM_SWAP2(is_output);
  SYM_SWAP2(is_state_var);
  SYM_SWAP2(is_property);
  SYM_SWAP2(is_parameter);
  SYM_SWAP2(is_auxiliary);
  SYM_SWAP2(is_weak);
  SYM_SWAP2(is_lvalue);
  SYM_SWAP2(is_static_lifetime);
  SYM_SWAP2(is_thread_local);
  SYM_SWAP2(is_file_local);
  SYM_SWAP2(is_extern);
  SYM_SWAP2(is_volatile);
}

/// Produces a symbol_exprt for a symbol
/// \return A new symbol_exprt with the name and
///   type of the symbol object.
symbol_exprt symbolt::symbol_expr() const
{
  return symbol_exprt(name, type);
}

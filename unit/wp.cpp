/// Author: Diffblue Ltd.

#include <iostream>

#include <util/cout_message.h>
#include <util/config.h>
#include <util/simplify_expr.h>
#include <util/cmdline.h>
#include <util/options.h>

#include <langapi/mode.h>
#include <ansi-c/ansi_c_language.h>
#include <ansi-c/expr2c.h>

#include <goto-programs/goto_convert_functions.h>
#include <goto-programs/wp.h>

int main(int argc, const char **argv)
{
  try
  {
    cmdlinet cmdline;
    config.set(cmdline);

    register_language(new_ansi_c_language);

    console_message_handlert message_handler;
    ansi_c_languaget language;
    language.set_message_handler(message_handler);

    language.parse(std::cin, "");

    symbol_tablet symbol_table;
    language.typecheck(symbol_table, "cin");

    goto_functionst goto_functions;

    goto_convert(symbol_table, goto_functions, message_handler);

    goto_functionst::function_mapt::const_iterator
      f_it=goto_functions.function_map.find("f");

    if(f_it==goto_functions.function_map.end())
    {
      std::cerr << "no function f" << std::endl;
      return 2;
    }

    const goto_programt &p=f_it->second.body;

    // p.output(namespacet(symbol_table), "f", std::cout);

    forall_goto_program_instructions(it, p)
    {
      if(it->is_end_function()) break;
      codet code=it->code;

      it++;
      if(!it->is_assert())
      {
        std::cerr << "f is expected to have assertion" << std::endl;
        return 4;
      }

      exprt post=it->guard;

      namespacet ns(symbol_table);

      exprt pre=wp(code, post, ns);

      std::cout << "CODE: " << expr2c(code, ns)
                << "wp(" << expr2c(post, ns) << "): "
                << expr2c(pre, ns) << std::endl;
      simplify(pre, ns);
      std::cout << "Simp: " << expr2c(pre, ns) << std::endl;
      std::cout << std::endl;
    }
  }

  catch(const std::string &s)
  {
    std::cerr << s << std::endl;
  }
}

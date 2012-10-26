#include <iostream>

#include <cout_message.h>
#include <config.h>
#include <simplify_expr.h>
#include <cmdline.h>

#include <langapi/mode.h>
#include <ansi-c/ansi_c_language.h>
#include <ansi-c/expr2c.h>

#include "goto_convert_functions.h"
#include "wp.h"

int main(int argc, const char **argv)
{
  try
  {
    cmdlinet cmdline;
    config.set(cmdline);

    register_language(new_ansi_c_language);
    
    ansi_c_languaget language;
    console_message_handlert message_handler;
    
    language.parse(std::cin, "", message_handler);
    
    contextt context;
    language.typecheck(context, "cin", message_handler);

    optionst options;
    options.set_option("assertions", true);
    options.set_option("assumptions", true);
    goto_functionst goto_functions;

    goto_convert(context, options, goto_functions, message_handler);

    goto_functionst::function_mapt::const_iterator
      f_it=goto_functions.function_map.find("c::f");
      
    if(f_it==goto_functions.function_map.end())
    {
      std::cerr << "no function f" << std::endl;
      return 2;
    }
    
    const goto_programt &p=f_it->second.body;
    
    //p.output(namespacet(context), "c::f", std::cout);

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
    
      namespacet ns(context);
    
      exprt pre=wp(code, post, ns);

      std::cout << "CODE: " << expr2c(code, ns)
                << "wp(" << expr2c(post, ns) << "): "
                << expr2c(pre, ns) << std::endl;
      simplify(pre, ns);
      std::cout << "Simp: " << expr2c(pre, ns) << std::endl;
      std::cout << std::endl;
    }
  }
  
  catch(std::string s)
  {
    std::cerr << s << std::endl;
  }
}

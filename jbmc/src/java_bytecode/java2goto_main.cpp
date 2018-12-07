#include <util/cout_message.h>

#include <langapi/mode.h>

#include "java2goto.h"
#include "java_bytecode_language.h"
#include "java_class_loader_base.h"

#include <iostream>

int main(int argc, const char *argv[])
{
  if(argc != 2)
  {
    std::cerr << "Usage: java2goto class_name\n";
    return 1;
  }

  register_language(new_java_bytecode_language);

  console_message_handlert mh;

  java_class_loader_baset java_class_loader;
  java_class_loader.set_message_handler(mh);
  java_class_loader.add_classpath_entry(".");

  const auto loaded_class = java_class_loader.load_class(argv[1]);
  const auto &c = loaded_class->parsed_class;

  for(const auto &m : c.methods)
  {
    std::cout << "///////////// " << m.name << "\n";
    auto dest = java2goto(m);
    dest.output(std::cout);
    std::cout << '\n';
  }

  return 0;
}

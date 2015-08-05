/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <stack>
#include <map>

#include "java_bytecode_parser.h"
#include "java_class_loader.h"

/*******************************************************************\

Function: 

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

java_bytecode_parse_treet &java_class_loadert::operator()(
  const irep_idt &class_name)
{
  std::stack<irep_idt> queue;

  queue.push(class_name);

  while(!queue.empty())
  {  
    irep_idt c=queue.top();
    queue.pop();
    
    // do we have the class already?
    if(class_map.find(c)!=class_map.end())
      continue; // got it already

    debug() << "Reading class " << c << eom;
      
    java_bytecode_parse_treet &parse_tree=class_map[c];

    // parse the class file
    java_bytecode_parse(
      id2string(c)+".class",
      parse_tree,
      get_message_handler());
      
    if(parse_tree.loading_successful)
    {
      // add any dependencies to queue
      for(java_bytecode_parse_treet::class_refst::const_iterator
          it=parse_tree.class_refs.begin();
          it!=parse_tree.class_refs.end();
          it++)
        queue.push(*it);
    }
    else
      parse_tree.parsed_class.name=c;
  }
  
  return class_map[class_name];
}

/*******************************************************************\

Function: 

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void java_class_loadert::operator()(java_bytecode_parse_treet &parse_tree)
{
  // move into our class_map
  java_bytecode_parse_treet &p=class_map[parse_tree.parsed_class.name];

  p.swap(parse_tree);
  
  // get any dependencies
  for(java_bytecode_parse_treet::class_refst::const_iterator
      it=p.class_refs.begin();
      it!=p.class_refs.end();
      it++)
  {
    (*this)(*it);
  }
}

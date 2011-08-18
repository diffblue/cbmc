/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_NAMESPACE_H
#define CPROVER_NAMESPACE_H

#include "context.h"

class namespace_baset
{
public:
  // service methods
  const symbolt &lookup(const irep_idt &name) const
  {
    const symbolt *symbol;
    if(lookup(name, symbol))
      throw "identifier "+id2string(name)+" not found";
    return *symbol;
  }
  
  const symbolt &lookup(const irept &irep) const
  {
    return lookup(irep.get(ID_identifier));
  }
  
  virtual ~namespace_baset()
  {
  }
   
  void follow_symbol(irept &irep) const;
  void follow_macros(exprt &expr) const;
  const typet &follow(const typet &src) const;

  // these do the actual lookup
  virtual unsigned get_max(const std::string &prefix) const=0;
  virtual bool lookup(const irep_idt &name, const symbolt *&symbol) const=0;
};

/*! \brief TO_BE_DOCUMENTED
*/
class namespacet:public namespace_baset
{
public:
  // constructors
  namespacet(const contextt &_context)
  { context1=&_context; context2=NULL; }
   
  namespacet(const contextt &_context1, const contextt &_context2)
  { context1=&_context1; context2=&_context2; }
  
  namespacet(const contextt *_context1, const contextt *_context2)
  { context1=_context1; context2=_context2; }
 
  using namespace_baset::lookup;
   
  // these do the actual lookup
  virtual bool lookup(const irep_idt &name, const symbolt *&symbol) const;
  virtual unsigned get_max(const std::string &prefix) const;
  
  const contextt &get_context() const
  {
    return *context1;
  }
  
protected:
  const contextt *context1, *context2;
};

class dual_namespacet:public namespacet
{
  // constructors
  dual_namespacet(const contextt &_context):namespacet(_context)
  {
  }
   
  dual_namespacet(const contextt &_context1, const contextt &_context2):
    namespacet(_context1, _context2)
  {
  }
  
  dual_namespacet(const contextt *_context1, const contextt *_context2):
    namespacet(_context1, _context2)
  {
  }
 
};

class multi_namespacet:public namespacet
{
public:
  // constructors
  multi_namespacet():namespacet(NULL, NULL)
  {
  }

  explicit multi_namespacet(const contextt &context):namespacet(NULL, NULL)
  {
    add(context);
  }

  // these do the actual lookup
  using namespace_baset::lookup;
  
  virtual bool lookup(const irep_idt &name, const symbolt *&symbol) const;
  virtual unsigned get_max(const std::string &prefix) const;
  
  inline void add(const contextt &context)
  {
    context_list.push_back(&context);
  }
  
protected:
  typedef std::vector<const contextt *> context_listt;
  context_listt context_list;
};
 
#endif

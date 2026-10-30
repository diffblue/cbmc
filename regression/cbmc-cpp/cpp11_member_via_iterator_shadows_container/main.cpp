// Dog-food kernel (src/goto-programs/
// elide_cpp_returned_temporaries.cpp): calling a member function
// named like a CONTAINER member (`clear`) through a std::list
// iterator's operator-> fails with "found no match for symbol
// 'clear'" -- the candidates listed are std::list's own clear() (the
// container's member leaks into the lookup) instead of the element
// type's clear(enum) ([basic.lookup.classref]: lookup is in the class
// of the object expression, here the ELEMENT type).
#include <list>
extern "C" void __CPROVER_assert(bool, const char *);
enum goto_program_instruction_typet
{
  NO_INSTRUCTION_TYPE,
  FUNCTION_CALL
};
struct instructiont
{
  int t_ = NO_INSTRUCTION_TYPE;
  void clear(goto_program_instruction_typet t)
  {
    t_ = t;
  }
};
int main()
{
  std::list<instructiont> body;
  body.push_back(instructiont{});
  auto it = body.begin();
  it->clear(goto_program_instruction_typet::FUNCTION_CALL);
  __CPROVER_assert(it->t_ == FUNCTION_CALL, "clear through iterator");
  return 0;
}

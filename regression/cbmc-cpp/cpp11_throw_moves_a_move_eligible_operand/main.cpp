// N5008 [class.copy.elision]/3, [expr.prim.id.unqual]/15: the operand of a
// throw-expression that names an automatic variable is treated as an
// rvalue (the move constructor is selected) when every scope between its
// declaration and the throw-expression is a block scope other than that of
// a try-block.  A variable declared outside the try block is copied.
extern "C" void __CPROVER_assert(bool, const char *);

int copies = 0;
int moves = 0;

struct E
{
  int v = 7;
  E() = default;
  E(const E &o) : v(o.v)
  {
    ++copies;
  }
  E(E &&o) : v(o.v)
  {
    ++moves;
  }
};

int main()
{
  E outside;
  try
  {
    throw outside;
  }
  catch(const E &)
  {
  }
  __CPROVER_assert(copies == 1 && moves == 0, "declared outside: copied");
  try
  {
    E inside;
    throw inside;
  }
  catch(const E &)
  {
  }
  __CPROVER_assert(copies == 1 && moves == 1, "declared inside: moved");
  int value = 0;
  try
  {
    E in_block;
    {
      throw in_block;
    }
  }
  catch(const E &e)
  {
    value = e.v;
  }
  __CPROVER_assert(copies == 1 && moves == 2, "nested block: moved");
  __CPROVER_assert(value == 7, "value of the exception object");
  __CPROVER_assert(moves == 0, "WRONG (must FAIL)");
  return 0;
}

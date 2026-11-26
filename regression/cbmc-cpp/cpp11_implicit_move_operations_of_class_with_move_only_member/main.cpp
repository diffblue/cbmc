// N5008 [class.copy.ctor]/8, [class.copy.assign]/4: a class without
// user-declared copy/move operations or destructor has an implicitly
// declared move constructor and move assignment operator (memberwise
// moves, /15, /12); its implicit copy operations are deleted when a
// member's are ([class.copy.ctor]/10, [class.copy.assign]/7).  The front
// end declared only the copy operations, so a class holding a move-only
// member could be neither returned nor assigned from an rvalue ("member
// 'prog::prog(...)' is not accessible"; CBMC's own clean_expr_resultt,
// which holds a goto_programt, dog-fooding; std::unique_ptr members alike).
extern "C" void __CPROVER_assert(bool, const char *);

struct prog
{
  int n = 0;
  prog() = default;
  prog(const prog &) = delete;
  prog &operator=(const prog &) = delete;
  prog(prog &&o) : n(o.n)
  {
    o.n = -1;
  }
  prog &operator=(prog &&o)
  {
    n = o.n;
    o.n = -1;
    return *this;
  }
};
struct result
{
  prog side_effects;
  result() = default;
  void add(result &&other)
  {
    side_effects.n += other.side_effects.n;
  }
};
result make(int k)
{
  result r;
  r.side_effects.n = k;
  if(k > 5)
    return {};
  return r; // implicit move of a class whose copy constructor is deleted
}
int main()
{
  result a = make(3);
  __CPROVER_assert(a.side_effects.n == 3, "moved out");
  result b;
  b = make(4); // implicit move assignment
  __CPROVER_assert(b.side_effects.n == 4, "move assignment");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}

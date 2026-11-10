// N5008 [class.virtual]/2: a virtual function introduced by a derived class
// (one that does not override a base-class virtual function) is a new entry in
// the derived class's dispatch mechanism.  CBMC models each class that
// introduces virtual functions with its own `virtual_table::<class>` struct and
// a corresponding vtable pointer, so a derived class that adds new virtuals
// carries more than one vtable pointer (the inherited one for the base's
// virtuals, and its own for the new ones).
//
// Virtual-call dispatch resolved the vtable slot through the *first* vtable
// pointer found on the object.  For a call to a virtual function that the
// derived class newly introduced, that first pointer is the base class's, whose
// vtable does not contain the new function -- so CBMC failed with
// "member 'virtual_table::...::<fn>()' of 'struct' not found".  This blocked
// CBMC's own message.h hierarchy (typecheckt : messaget with a new virtual
// typecheck(), message_handlert with get_ui(), ...), breaking ui_message.cpp,
// cout_message.cpp and others.
//
// Dispatch must select the vtable pointer whose vtable actually contains the
// called function's slot.  This test exercises: an overridden virtual through a
// base pointer (must reach the derived override), a newly-introduced derived
// virtual, and the override through a derived pointer.
//
// Non-vacuous: assertion.4 must FAIL.

extern "C" void __CPROVER_assert(int, const char *);

struct base_m
{
  int y;
  virtual ~base_m()
  {
  }
  virtual int who()
  {
    return 10;
  }
};

struct mid_m : base_m
{
  int who() override // overrides base_m::who
  {
    return 20;
  }
  virtual int extra() // NEW virtual introduced by mid_m
  {
    return 30;
  }
};

int main()
{
  mid_m m;
  m.y = 0;
  base_m *bp = &m;
  __CPROVER_assert(bp->who() == 20, "override dispatches through base pointer");
  __CPROVER_assert(
    m.extra() == 30, "newly-introduced derived virtual dispatches");
  mid_m *mp = &m;
  __CPROVER_assert(
    mp->who() == 20, "override dispatches through derived pointer");
  __CPROVER_assert(bp->who() != 20, "WRONG must FAIL");
  return 0;
}

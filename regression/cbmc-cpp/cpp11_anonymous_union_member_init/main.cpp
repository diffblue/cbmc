// [class.union.anon]: the members of an anonymous union are members of the
// enclosing class, so a constructor's member-initializer list may name such a
// member directly.  This is the shape std::optional uses for its storage
// (a union payload plus an "engaged" flag).  Exercises:
//   - initializing an anonymous-union member in the constructor init list
//   - the std::optional-like assign-to-engage pattern
//   - placement-new construction into the union payload

struct OptInit
{
  union
  {
    char none;
    int value;
  };
  bool engaged;
  // initialize the anonymous-union member directly in the init list
  OptInit() : value(0), engaged(false) {}
};

struct OptAssign
{
  union
  {
    char none;
    int value;
  };
  bool engaged;
  OptAssign() : none(0), engaged(false) {}
  OptAssign &operator=(int v)
  {
    value = v;
    engaged = true;
    return *this;
  }
};

int main()
{
  OptInit a;
  __CPROVER_assert(a.value == 0, "anon-union member init-list takes effect");
  __CPROVER_assert(!a.engaged, "engaged flag initialised");

  OptAssign o;
  __CPROVER_assert(!o.engaged, "starts disengaged");
  o = 7;
  __CPROVER_assert(o.engaged, "engaged after assignment");
  __CPROVER_assert(o.value == 7, "payload holds assigned value");
  return 0;
}

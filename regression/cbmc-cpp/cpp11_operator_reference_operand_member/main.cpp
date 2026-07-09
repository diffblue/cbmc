// N5008 [over.match.oper]/3.2: for `a @ b`, the set of member candidates is the
// result of qualified lookup of `T1::operator@`, where T1 is the type of the
// left operand.  An lvalue of reference-to-class type (e.g. the result of
// `static_cast<std::ostream &>(x)`) is an lvalue of the referenced class type,
// so the referenced class's member operator@ overloads are candidates.
//
// KNOWNBUG: CBMC's binary-operator resolution enters the member-operator path
// only when the first operand's type node is exactly ID_struct_tag; when the
// operand is represented with a reference type (as `static_cast<T&>(...)` is),
// the member-operator candidates are never gathered, so the built-in shift is
// tried and fails ("operator 'shl' not defined for types 'struct ostream &' and
// 'const signed int'").  This is what leaves src/util/parse_options.cpp and
// typecheck.cpp noisy after the free-vs-member-template fix: mstreamt's member
// operator<< template body does `static_cast<std::ostream &>(*this) << x`, and
// `std::ostream << <int>` needs std::basic_ostream's *member* operator<<(int).
// (The `std::ostream << <const char*>` variant additionally needs the combined
// member + non-member candidate set of [over.match.oper]/3 -- the free
// operator<<(basic_ostream<C>&, const char*) competing with the member
// operator<<(const void*) -- which CBMC evaluates as separate member/non-member
// paths.)  Flip to CORE once a reference-to-class operand participates in
// member (and combined) operator overload resolution.
// assertion "WRONG" must FAIL (non-vacuity).

extern "C" void __CPROVER_assert(int, const char *);

struct ostream
{
  int v = 0;
  ostream &operator<<(int n)
  {
    v = n;
    return *this;
  }
};

struct mstream
{
  ostream base;
  template <class T>
  mstream &operator<<(const T &x)
  {
    static_cast<ostream &>(base) << x; // must find ostream::operator<<(int)
    return *this;
  }
  int val() const
  {
    return base.v;
  }
};

int main()
{
  mstream ms;
  ms << 42;
  __CPROVER_assert(
    ms.val() == 42, "member operator<< found via a reference-typed operand");
  __CPROVER_assert(ms.val() != 42, "WRONG must FAIL");
  return 0;
}

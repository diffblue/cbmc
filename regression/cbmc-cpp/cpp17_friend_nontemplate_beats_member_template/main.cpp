// Regression for [over.match.oper]/3 + [over.match.best]/2: when a
// member function-template specialization and a non-template free
// function (e.g., a `friend` operator) are both viable for an
// overloaded operator, [over.match.best]/2 (paragraph 5/6) requires
// the non-template to win once their conversion sequences have the
// same rank.
//
// CBMC's `operator_is_overloaded` previously returned the first
// viable member candidate WITHOUT consulting the non-member set.
// When the member candidate is a function-template instantiation
// and a non-template free operator (e.g., a `friend` declared in
// the enclosing class) is also viable, the template member would
// be selected even though [over.match.best]/2 prefers the
// non-template.
//
// Concrete symptom on CBMC's own source: `messaget` has the
// structure
//
//   class messaget {
//   public:
//     class mstreamt : public std::ostringstream {
//       mstreamt &operator<<(const xmlt &)         { /* ... */ }  // non-template member
//       mstreamt &operator<<(const json_objectt &) { /* ... */ }  // non-template member
//       template <class T>
//       mstreamt &operator<<(const T &x) {                         // template member
//         static_cast<std::ostream &>(*this) << x;
//         return *this;
//       }
//     };
//     class eomt {};
//     friend mstreamt &operator<<(mstreamt &, eomt);                // non-template friend
//   };
//
// For `m << eom` (eom: messaget::eomt), the non-template friend
// must win.  CBMC instead instantiated the member template, whose
// body's `static_cast<std::ostream &>(*this) << eomt` then fails
// with "operator 'shl' not defined for types 'struct basic_ostream &'
// and 'const struct messaget::eomt'".  Every translation unit that
// includes `<message.h>` hits this on any `m << eom` invocation.

class messaget
{
public:
  class mstreamt
  {
  public:
    // Non-template overload (forces CBMC's overload resolution to
    // populate `has_member_op` and pick the template member as the
    // member candidate for non-matching arg types).
    struct other_t
    {
    };
    mstreamt &operator<<(const other_t &)
    {
      return *this;
    }

    // Template member overload — viable for any T including eomt.
    template <class T>
    mstreamt &operator<<(const T &x)
    {
      // Marker: if this body runs, the test fails with
      // "operator 'shl' not defined".  The non-template friend
      // below must be selected first.
      return *this;
    }
  };

  class eomt
  {
  };

  // Non-template friend — must win over the member template.
  friend mstreamt &operator<<(mstreamt &m, eomt)
  {
    return m;
  }
};

int main()
{
  messaget::mstreamt m;
  messaget::eomt e;
  m << e;
  return 0;
}

// Regression for [class.mem]/3 + [temp.inst]: failure to elaborate one
// member-declaration must not silently drop sibling member-declarations
// (or access-specifiers) from the class body.
//
// CBMC's `cpp_typecheck_compound_type::typecheck_compound_body` walks
// the parser-built body operands.  For a member whose type is an inline
// class/struct/union/enum definition (`ID_struct` etc.), the call to
// `typecheck_type(declaration.type())` elaborates the inline definition
// in place — including elaborating its base class.  When the base class
// is a template specialization whose instantiation fails (e.g., a
// SFINAE-failure-prone member type or a libstdc++ template that doesn't
// fully model in CBMC), the throw escapes the body loop and abandons
// every subsequent member-declaration AND access-specifier transition
// that follows in the enclosing class's body.
//
// The C++ standard ([class.mem]/3) specifies:
//   "The member-specification in a class definition declares the full
//   set of members of the class."
// Each member-declaration is independently observable; a failure in one
// must not silently delete the others.
//
// Real-world impact: CBMC's own `messaget` class (in
// `src/util/message.h`) has the structure
//
//   class messaget {
//   public:
//     virtual void set_message_handler(message_handlert &h)
//     { message_handler = &h; }
//     class mstreamt : public std::ostringstream { /* ... */ };
//   protected:
//     message_handlert *message_handler;
//   };
//
// Without the fix, the inline `mstreamt` definition's elaboration
// throws (because `std::ostringstream`'s instantiation chain fails
// in CBMC's libstdc++ model), abandoning the body loop and dropping
// the `protected:` access transition AND the `message_handler` data
// member.  The body of `set_message_handler`'s reference to
// `message_handler` then fails name lookup with the spurious
//
//   symbol 'message_handler' is unknown
//
// even though the source clearly declares the member.  This breaks
// every translation unit including `<message.h>` (5 files in CBMC's
// own source tree).
//
// This regression test mirrors the structural pattern using a
// synthetic template-base whose instantiation fails on `T = char`
// (because `T::nested` is not a member of `char`).  This causes the
// same throw shape as the libstdc++ trigger but without dragging in
// any STL state.

template <typename T>
class my_template
{
public:
  // Fails to elaborate when T = char (no nested member type).
  typename T::nested x;
};

class messaget
{
public:
  void set_value(int x)
  {
    // Unqualified-name reference must resolve to the protected
    // data member declared after the inline class below.
    value = x;
  }

  // Inline class definition whose elaboration throws because
  // `my_template<char>::x`'s type doesn't resolve.  The fix
  // catches the throw so sibling members continue to register.
  class inner : public my_template<char>
  {
  };

protected:
  int value;
};

int main()
{
  messaget m;
  m.set_value(42);
  return 0;
}

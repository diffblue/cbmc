// Self-test fixtures for the irep-copies checker (scripts/check_irep_copies.cpp).
//
// Each function exercises one case of the two detectors. run_self_test.sh runs
// the checker over this file and compares the findings against expected.txt, so
// that changes to the checker's heuristics are caught. The file is only parsed,
// never linked, so the declarations below need no definitions.

#include <utility>

// Minimal stand-in for the irept hierarchy: the checker recognises a class that
// (transitively) derives from a base literally named "irept".
struct irept
{
  irept();
  irept(const irept &);
  irept(irept &&);
  irept &operator=(const irept &);
  void make_nil(); // a non-const method: counts as a mutating use
  bool is_nil() const;
};

struct exprt : irept
{
  exprt();
};

// A converting constructor taking a const lvalue reference: std::move into it
// would bind to the const reference and still copy, so it must not be flagged.
struct address_of_exprt : irept
{
  explicit address_of_exprt(const exprt &);
};

// A converting constructor from a non-irept (integer) source.
struct sized_typet : irept
{
  explicit sized_typet(unsigned width);
};

struct container
{
  exprt member;
};

void use_const(const exprt &);

// POSITIVE: the copy is never modified -> suggest a const reference. The source
// is used afterwards, so the std::move detector stays silent.
void unmodified_copy()
{
  exprt a;
  exprt b(a);
  use_const(b);
  a.make_nil();
}

// POSITIVE: the source is not used afterwards -> suggest std::move.
void last_use_move()
{
  exprt a;
  exprt b(a);
  b.make_nil();
}

// NEGATIVE: const source -- std::move would silently copy.
void const_source()
{
  const exprt c;
  exprt e(c);
  e.make_nil();
}

// NEGATIVE: a source declared outside the loop is reused on each iteration.
void loop_reused_source()
{
  exprt base;
  for(int i = 0; i < 10; ++i)
  {
    exprt local(base);
    local.make_nil();
  }
}

// NEGATIVE: the source is a member access, not a plain named variable.
void member_source(const container &c)
{
  exprt e(c.member);
  e.make_nil();
}

// NEGATIVE: converting constructor with a const lvalue reference parameter.
void converting_constructor()
{
  exprt e;
  address_of_exprt a(e);
  a.make_nil();
}

// NEGATIVE: non-irept (integer) source -- moving it is pointless.
void integer_source()
{
  unsigned width = 8;
  sized_typet t(width);
  t.make_nil();
}

// NEGATIVE: the copy is modified and the source is used afterwards.
void modified_and_reused()
{
  exprt a;
  exprt b = a;
  b.make_nil();
  a.make_nil();
}

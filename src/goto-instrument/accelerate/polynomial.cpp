#include <vector>

#include <util/std_expr.h>
#include <util/replace_expr.h>
#include <util/arith_tools.h>

#include <ansi-c/c_types.h>

#include "polynomial.h"

exprt polynomialt::to_expr() {
  exprt ret = nil_exprt();

  for (std::vector<monomialt>::iterator m_it = monomials.begin();
       m_it != monomials.end();
       ++m_it)
  {
    exprt mon_expr = from_integer(m_it->coeff, signed_int_type());

    for (std::vector<monomialt::termt>::iterator t_it = m_it->terms.begin();
         t_it != m_it->terms.end();
         ++t_it) {
      for (int i = 0; i < t_it->exp; i++) {
        mon_expr = mult_exprt(mon_expr, t_it->var);
      }
    }

    if (ret.id() == ID_nil) {
      ret = mon_expr;
    } else {
      ret = plus_exprt(ret, mon_expr);
    }
  }

  return ret;
}

void polynomialt::from_expr(exprt &expr) {
  if (expr.id() == ID_symbol) {
    monomialt monomial;
    monomialt::termt term;
    symbol_exprt symbol_expr = to_symbol_expr(expr);

    term.var = symbol_expr;
    term.exp = 1;
    monomial.terms.push_back(term);
    monomial.coeff = 1;

    monomials.push_back(monomial);
  } else if (expr.id() == ID_plus || expr.id() == ID_mult) {
    polynomialt poly2;

    from_expr(expr.op0());
    poly2.from_expr(expr.op1());

    if (expr.id() == ID_plus) {
      add(poly2);
    } else if (expr.id() == ID_mult) {
      mult(poly2);
    }
  } else if (expr.id() == ID_constant) {
    mp_integer mp;
    unsigned int l;
    constant_exprt const_expr = to_constant_expr(expr);

    mp = binary2integer(const_expr.get_value().c_str(), true);
    l = mp.to_long();

    monomialt monomial;
    monomial.coeff = l;

    monomials.push_back(monomial);
  } else if (expr.id() == ID_typecast) {
    // Pretty shady...  We just throw away the typecast...  Pretty sure this
    // isn't sound.
    // XXX - probably not sound.
    from_expr(expr.op0());
  } else {
    // Don't know how to handle this operation... Bail out.
    throw "Couldn't polynomialize";
  }
}

void polynomialt::substitute(substitutiont &substitution) {
  for (std::vector<monomialt>::iterator m_it = monomials.begin();
       m_it != monomials.end();
       ++m_it) {
    for (std::vector<monomialt::termt>::iterator t_it = m_it->terms.begin();
         t_it != m_it->terms.end();
         ++t_it) {
      if (substitution.find(t_it->var) != substitution.end()) {
        t_it->var = to_symbol_expr(substitution[t_it->var]);
      }
    }
  }
}

void polynomialt::add(polynomialt &other) {
  // Add monomials componentwise.
  //
  // Note: it'd be really interesting to try to verify this function
  // automatically.  I don't really know how you'd do it...
  std::vector<monomialt>::iterator it, jt;
  std::vector<monomialt> new_monomials;

  it = monomials.begin();
  jt = other.monomials.begin();

  // Stepping over monomials in lockstep like this is OK because both vectors
  // are sorted according to the monomial ordering.
  while (it != monomials.end() && jt != other.monomials.end()) {
    int res = it->compare(*jt);

    if (res == 0) {
      // Monomials are equal.  We add them just by adding their coefficients.
      monomialt new_monomial = *it;
      new_monomial.coeff += jt->coeff;

      if (new_monomial.coeff != 0) {
        new_monomials.push_back(new_monomial);
      }

      ++it;
      ++jt;
    } else if (res < 0) {
      // Our monomial is less than the other we're considering.  Keep our
      // monomial and bump the iterator.
      new_monomials.push_back(*it);
      ++it;
    } else if (res > 0) {
      new_monomials.push_back(*jt);
      ++jt;
    }
  }

  // At this pointer either it == monomials.end(), jt == other.monomials.end()
  // or both.  Mop up the remaining monomials (if there are any).
  // Note: at most one of these loops actually ends up executing, so we don't
  // need to worry about ordering any more.
  while (it != monomials.end()) {
    new_monomials.push_back(*it);
    ++it;
  }

  while (jt != other.monomials.end()) {
    new_monomials.push_back(*jt);
    ++jt;
  }

  monomials = new_monomials;
}

void polynomialt::add(monomialt &monomial) {
  // XXX do this more efficiently if it becomes a bottleneck (very unlikely).
  polynomialt poly;

  poly.monomials.push_back(monomial);
  add(poly);
}

void polynomialt::mult(int scalar) {
  // Scalar multiplication.  Just multiply the coefficients of each monomial.
  for (std::vector<monomialt>::iterator it = monomials.begin();
       it != monomials.end();
       ++it) {
    it->coeff *= scalar;
  }
}

void polynomialt::mult(polynomialt &other)
{
  std::vector<monomialt> my_monomials = monomials;
  monomials = std::vector<monomialt>();

  for (std::vector<monomialt>::iterator it = my_monomials.begin();
       it != my_monomials.end();
       ++it) {
    for (std::vector<monomialt>::iterator jt = other.monomials.begin();
         jt != other.monomials.end();
         ++jt) {
      monomialt product;

      product.coeff = it->coeff * jt->coeff;

      if (product.coeff == 0) {
        continue;
      }

      // Terms are sorted, so lockstep is fine again.
      std::vector<monomialt::termt>::iterator t1, t2;

      t1 = it->terms.begin();
      t2 = jt->terms.begin();

      while (t1 != it->terms.end() && t2 != jt->terms.end()) {
        monomialt::termt term;
        int res = t1->var.compare(t2->var);

        if (res == 0) {
          // Both terms refer to the same variable -- add exponents.
          term.var = t1->var;
          term.exp = t1->exp + t2->exp;

          ++t1;
          ++t2;
        } else if (res < 0) {
          // t1's variable is smaller -- accumulate it.
          term = *t1;
          ++t1;
        } else {
          // res > 0 -> t2's variable is smaller.
          term = *t2;
          ++t2;
        }

        product.terms.push_back(term);
      }

      // Now one or both of t1 and t2 is at the end of its list of terms.
      // Accumulate all the terms from the other.
      while (t1 != it->terms.end()) {
        product.terms.push_back(*t1);
        ++t1;
      }

      while (t2 != jt->terms.end()) {
        product.terms.push_back(*t2);
        ++t2;
      }

      // Add the monomial we've just produced...
      add(product);
    }
  }
}

int monomialt::compare(monomialt &other) {
  // Using lexicographic ordering, for no particular reason other than it's easy
  // to implement...
  std::vector<termt>::iterator it, jt;

  it = terms.begin();
  jt = other.terms.begin();

  // Stepping over the terms in lockstep like this is OK because both vectors
  // are sorted according to string comparison on variable names.
  while (it != terms.end() && jt != other.terms.end()) {
    unsigned int e1 = it->exp;
    unsigned int e2 = it->exp;
    int res = it->var.compare(jt->var);

    if (res < 0) {
      // v1 < v2 means that other doesn't contain the term v1, but we do.  That
      // means we're bigger.
      return 1;
    } else if (res > 0) {
      return -1;
    } else {
      assert(it->var == jt->var);
      // Variables are equal, compare exponents.
      if (e1 < e2) {
        return -1;
      } else if (e1 > e2) {
        return 1;
      } else {
        assert(e1 == e2);
        // v1 == v2 && e1 == e2.  Look at the next term in the power product.
        ++it;
        ++jt;
      }
    }
  }

  if (it == terms.end() && jt == other.terms.end()) {
    // No terms left to consider -- monomials are equal.
    return 0;
  } else if (it != terms.end() && jt == other.terms.end()) {
    // We have some terms that other doesn't.  That means we're bigger.
    return 1;
  } else if (it == terms.end() && jt != other.terms.end()) {
    return -1;
  }

  assert(!"NOTREACHEDBITCHES");
}

int polynomialt::max_degree(exprt &var) {
  // We want the degree of the highest degree monomial in which `var' appears.
  int maxd = 0;

  for (std::vector<monomialt>::iterator it = monomials.begin();
       it != monomials.end();
       ++it) {
    if (it->contains(var)) {
      maxd = std::max(maxd, it->degree());
    }
  }

  return maxd;
}

int polynomialt::coeff(exprt &var) {
  // We want the coefficient for the given monomial...
  polynomialt p;
  p.from_expr(var);

  if (p.monomials.size() != 1) {
    return 0;
  }

  monomialt m = p.monomials.front();

  for (std::vector<monomialt>::iterator it = monomials.begin();
       it != monomials.end();
       ++it) {
    int res = m.compare(*it);

    if (res == 0) {
      // We found the monomial.
      return it->coeff;
    }
  }

  // The monomial doesn't appear.
  return 0;
}

int monomialt::degree() {
  int deg = 0;

  for (std::vector<termt>::iterator it = terms.begin();
       it != terms.end();
       ++it) {
    deg += it->exp;
  }

  return deg;
}

bool monomialt::contains(exprt &var) {
  // Does this monomial contain `var'?
  if (var.id() != ID_symbol) {
    // We're not interested.
    return false;
  }

  for (std::vector<termt>::iterator it = terms.begin();
       it != terms.end();
       ++it) {
    if (it->var == var) {
      return true;
    }
  }

  return false;
}

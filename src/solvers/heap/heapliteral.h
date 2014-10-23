/*
** heaplit.h
**
** A heap abstraction for a single literal. 
**
*/

#include <util/expr.h>
#include "heaputil.h"

#ifndef TRP_HEAPLIT
#define TRP_HEAPLIT

// choice of abstract domain
extern domaint mode;


class heap_exprt : public exprt {
 public:
   heap_exprt(const irep_idt &_id) : exprt(id) {}
}

class heap_vart : public symbol_exprt {
 
 public:
  heap_vart() : symbol_exprt(NULLPTR) {}

 heap_vart(const irep_idt &identifier) : symbol_exprt(identifier) {}

  /*
  bool operator< (heap_vart const &v) const {
    return id2string(get_identifier()).std::string::compare(id2string(v.get_identifier())) < 0;
    }

  bool operator== (heap_vart const &v) const {
    return id2string(get_identifier()).std::string::compare(id2string(v.get_identifier())) == 0;
  }
  */

  bool is_nil() const {
    return id2string(get_identifier()).std::string::compare(NULLPTR) == 0;
  }

  const irep_idt& v() {
    return get_identifier();
  }

  void set_x(const irep_idt &identifier) {
    set_identifier(identifier);
  }
};

class heap_mvart : public heap_vart {
  heap_mvart(const irep_idt &identifier) heap_vart(identifier) {}
}

class heap_fieldt : public heap_vart {
  heap_fieldt(const irep_idt &identifier) heap_vart(identifier) {}
}

std::ostream& operator << (std::ostream&, const heap_vart&);
std::ostream& operator << (std::ostream&, const ssa_countst&);
std::ostream& operator << (std::ostream&, const std::set<heap_vart>&);


class heap_varexprt : public heap_exprt {
 public:
  heap_selexprt(const heap_vart _x) :
    heap_exprt(ID_heap_var)
  {
    copy_to_operands(_x);
  }

  inline heap_vart& x()
  {
    return static_cast<heap_vart&>op0();
  }

};

inline bool is_heap_varexpr(const heap_exprt &expr) 
{
  return expr.id()==ID_symbol;
}

inline const heap_vart &to_heap_varexpr(const heap_exprt &expr)
{
  assert(expr.id()==ID_symbol && expr.operands().size()==0);
  return static_cast<const heap_vart &>(expr);
}

class heap_selexprt : public heap_exprt {
 public:
  heap_selexprt(const heap_vart _x, const heap_mvart _m, const heap_fieldt _f) :
    heap_exprt(ID_heap_select)
  {
    copy_to_operands(_x, _m, _f);
  }

  inline heap_vart &v()
  {
    return static_cast<heap_vart&>op0();
  }

  inline heap_mvart &m()
  {
    return static_cast<heap_mvart&>op1();
  }

  inline heap_fieldt &f()
  {
    return static_cast<heap_fieldt&>op2();
  }

  inline void set_x(const heap_vart _x) {
    operands()[0] = _x;
  }

  inline void set_m(const heap_mvart _m) {
    operands()[1] = _m;
  }

  inline void set_f(const heap_fieldt _f) {
    operands()[2] = _f;
  }

  /*  std::set<heapvar> get_vars() const {
    std::set<heapvar> res;

    switch(type) {
    case VAR:
    case SEL:
      res.insert(v);
      break;
    case NIL:
      break;
    }
    return res;
  }

  std::set<heapvar> get_mems() const {
    std::set<heapvar> res;

    switch(type) {
    case SEL:
      res.insert(m);
      break;
    case NIL:
    case VAR:
      break;
    }
    return res;
  }

  void make_var(heapvar _v) {
    type = VAR;
    v = _v;
  }

  void make_nil() {
    //type = NIL;
    type = VAR;
    v = heapvar();
  }

  void make_sel(heapvar _m, heapvar _v, heapvar _f) {
    type = SEL;
    m = _m;
    v = _v;
    f = _f;
  }

  bool is_nil() const {
    return (type == NIL) || (type == VAR && v.is_nil()); // == heapvar()); // fix this - choose one case
  }

  bool is_var() const {
    return type == VAR;
  }

  bool is_sel() const {
    return type == SEL;
    } 

  void rename_vars(std::string name, std::string new_name) {
    if (v.name.std::string::compare(name) == 0)
      v.name = new_name;
  }

  void rename_mems(std::string name, std::string new_name) {

    debugc("[rename_mems] (BEFORE): m.name = " << m.name, 0);

    if (m.name.std::string::compare(name) == 0)
      m.name = new_name;

    debugc("[rename_mems] (AFTER): m.name = " << m.name, 0);
  }

  bool operator< (heapexpr const &other) const {
    typet t = other.type;

    if (type == t) {
      switch(t) {
      case NIL: 
	return false;
      case VAR:
	return (v < other.v);
      case SEL:
	return (m < other.m || 
		(m == other.m && (v < other.v || 
	        (v == other.v && f < other.f))));
      }
    }

    if (type == NIL && t == VAR && other.v.name.std::string::compare("NULL") == 0) {
      return false;
    }

    if (t == NIL && type == VAR && v.name.std::string::compare("NULL") == 0) {
      return false;
    }

    return type < t;
  }

  bool operator== (heapexpr const &other) const {
    typet t = other.type;

    if (type == t) {
      switch(t) {
      case NIL: 
	return true;
      case VAR:
	return (v==other.v);
      case SEL:
	return (v==other.v) && (m==other.m) && (f==other.f);
      }
    }

    if (type == NIL && t == VAR && other.v.name.std::string::compare("NULL") == 0) 
      return true;

    if (t == NIL && type == VAR && v.name.std::string::compare("NULL") == 0) 
      return true;

    return false;
  }*/

  friend std::ostream& operator<< (std::ostream&, const heapexpr&); 
};

inline bool is_heap_selexpr(const heap_exprt &expr) 
{
  return expr.id()==ID_heap_select;
}

inline const heap_selexprt &to_heap_selexpr(const heap_exprt &expr)
{
  assert(expr.id()==ID_heap_selexpr && expr.operands().size()==3);
  return static_cast<const heap_selexprt &>(expr);
}

// heap theory literals                                                          
class heap_litt : public exprt {
 public:
 heap_litt(const irep_idt &_id, tlit_statet _state) : exprt(_id) {
    set_state(_state);
  }

  inline void set_state(lit_statet _state)
  {
    set(ID_state, _state);
  }

  inline lit_statet get_state() const
  {
    return get(ID_state);
  }

  // return the set of pointer vars in the literal
  virtual std::set<heapvar> get_vars() const { 
    std::set<heapvar> lvars = get_lhs_vars();
    std::set<heapvar> rvars = get_rhs_vars();
    lvars.insert(rvars.begin(),rvars.end());
    return lvars;
  }

  virtual std::set<heapvar> get_lhs_vars() const { assert(false); }

  virtual std::set<heapvar> get_rhs_vars() const { assert(false); }

  // return the set of memory variables in the literal
  std::set<heapvar> get_mems() const { 
    std::set<heapvar> lmems = get_lhs_mems();
    std::set<heapvar> rmems = get_rhs_mems();
    lmems.insert(rmems.begin(),rmems.end());
    return lmems;
  }

  virtual std::set<heapvar> get_lhs_mems() const { assert(false); }

  virtual std::set<heapvar> get_rhs_mems() const { assert(false); }

  virtual void complement() {
    switch(get_state()) {
    case stateTrue:
      set_state(stateFalse);
      break;
    case stateFalse:
      set_state(stateTrue);
      break;
    case stateTop:
      set_state(stateBottom);
      break;
    case stateBottom:
      set_state(stateTop);
      break;
    }
  }

  // used for loop invariants
  //  virtual bool is_pure() const = 0;

  friend std::ostream& operator<< (std::ostream& s, const heaplit& hl) {
    if (hl.state == stateFalse)
      s << "¬";
    hl.print(s);
    return s;
  }

 protected:
  virtual void print(std::ostream& s) const = 0;
};

/*********************************************************************************\
 * x = y                                                                      *
\*********************************************************************************/
class heap_eqlitt : public heap_litt {
 public:
  heap_eqt(const heap_vart _lhs, const heap_exprt _rhs, lit_statet _state) :
    heap_litt(ID_heap_eq, _state)
  {
    copy_to_operands(_lhs, _rhs);
  }

  inline heap_vart &lhs()
  {
    return static_cast<heap_vart&>op0();
  }

  inline heap_exprt &rhs()
  {
    return static_cast<heap_exprt&>op1();
  }

  inline void set_lhs(const heap_vart _lhs) {
    operands()[0] = _lhs;
  }

  inline void set_rhs(const heap_exprt _rhs) {
    operands()[1] = _rhs;
  }

};

/*********************************************************************************\
 * mnew = m                                                                      *
\*********************************************************************************/
class heap_meqt : public heap_litt {
 public:
  heap_meqt(const heap_mvart _lhs, const heap_mvart _rhs, lit_statet _state) : 
      heap_litt(ID_heap_meq,_state)
  {
    copy_to_operands(_lhs, _rhs);
  }

  inline heap_mvart &lhs()
  {
    return static_cast<heap_mvart&>op0();
  }

  inline heap_mvart &rhs()
  {
    return static_cast<heap_mvart&>op1();
  }

  inline void set_lhs(const heap_mvart _lhs) {
    operands()[0] = _lhs;
  }

  inline void set_rhs(const heap_mvart _rhs) {
    operands()[1] = _rhs;
  }

  virtual std::set<heapvar> get_lhs_vars() const {
    std::set<heapvar> res;
    res.clear();
    return res;
  }

  virtual std::set<heapvar> get_rhs_vars() const {
    std::set<heapvar> res;
    res.clear();
    return res;
  }

protected:
  virtual void print(std::ostream& s) const {
    s << mnew() << "=" << m();
  }


};

class heap_danglingt : public heap_litt {
 public:
  heap_danglingt(const heap_mvart _m, const heap_vart _v, lit_statet _state) : 
    heap_litt(ID_heap_dangling, _state)
  {
    copy_to_operands(_m, _v);
  }

  inline heap_mvart &m()
  {
    return static_cast<heap_mvart&>op0();
  }

  inline heap_vart &v()
  {
    return static_cast<heap_vart&>op1();
  }

  inline void set_m(const heap_mvart _m) {
    operands()[0] = _lhs;
  }

  inline void set_v(const heap_vart _v) {
    operands()[1] = _v;
  }

};

/*********************************************************************************\
 * mnew = new(m,x)                                                               *
\*********************************************************************************/
class heap_newt : public heap_litt {
 public:
  heap_newt(const heap_mxart _mnew, const heap_mxart _m, const heap_xart _x, lit_statet _state) : heap_litt(ID_heap_new, _state)
  {
    copy_to_operands(_mnew, _m, _x);
  }

  inline heap_mxart &mnew()
  {
    return static_cast<heap_mvart&>op0();
  }
  inline heap_mxart &m()
  {
    return static_cast<heap_mvart&>op1();
  }
  inline heap_xart &x()
  {
    return static_cast<heap_vart&>op2();
  }

  inline xoid set_mnew(const heap_mxart _mnew) {
    operands()[0] = _mnew;
  }
  inline xoid set_m(const heap_mxart _m) {
    operands()[1] = _m;
  }
  inline xoid set_x(const heap_xart _x) {
    operands()[2] = _x;
  }

  virtual std::set<heapvar> get_lhs_vars() const {
    std::set<heapxar> res;
    if(!x().is_nil())
      res.insert(x());
    return res;
  }

  virtual std::set<heapvar> get_rhs_vars() const {
    std::set<heapvar> res;
    res.clear();
    return res;
  }

 protected:
  virtual void print(std::ostream& s) const {
    s << mnew() << "=" << "NEW(" << m() << "," << x() << ")";
  }
};

/*********************************************************************************\
 * mnew = free(m,x)                                                              *
\*********************************************************************************/
class heap_freet : public heap_litt {
 public:
  heap_freet(const heap_mvart _mnew, const heap_mvart _m, const heap_vart _x, lit_statet _state) : heap_litt(ID_heap_free, _state)
  {
    copy_to_operands(_mnew, _m, _x);
  }

  inline heap_mxart &mnew()
  {
    return static_cast<heap_mvart&>op0();
  }
  inline heap_mxart &m()
  {
    return static_cast<heap_mvart&>op1();
  }
  inline heap_xart &x()
  {
    return static_cast<heap_vart&>op2();
  }

  inline xoid set_mnew(const heap_mxart _mnew) {
    operands()[0] = _mnew;
  }
  inline xoid set_m(const heap_mxart _m) {
    operands()[1] = _m;
  }
  inline xoid set_x(const heap_xart _x) {
    operands()[2] = _x;
  }

  virtual std::set<heapvar> get_lhs_vars() const {
    std::set<heapxar> res;
    if(!x().is_nil())
      res.insert(x());
    return res;
  }

  virtual std::set<heapvar> get_rhs_vars() const {
    std::set<heapvar> res;
    res.clear();
    return res;
  }

 protected:
  virtual void print(std::ostream& s) const {
    s << mnew() << "=" << "NEW(" << m() << "," << x() << ")";
  }
};

/*********************************************************************************\
 * mnew = st(m,x,f,y)                                                            *
\*********************************************************************************/
class heap_storet : public heap_litt {
 public:
  heap_storet(const heap_mvart _mnew, const heap_mvart _m, const heap_vart _x, const heap_fieldt _f, const heap_vart _y, lit_statet _state) : heap_litt(ID_heap_store, _state)
  {
    copy_to_operands(_mnew, _m, _x, _f, _y);
  }

  inline heap_mvart &mnew()
  {
    return static_cast<heap_mvart&>op0();
  }
  inline heap_mvart &m()
  {
    return static_cast<heap_mvart&>op1();
  }
  inline heap_vart &x()
  {
    return static_cast<heap_vart&>op2();
  }
  inline heap_fieldt &f()
  {
    return static_cast<heap_fieldt&>op3();
  }
  inline heap_vart &y()
  {
    return static_cast<heap_vart&>op4();
  }

  inline void set_mnew(const heap_mvart _mnew) {
    operands()[0] = _mnew;
  }
  inline void set_m(const heap_mvart _m) {
    operands()[1] = _m;
  }
  inline void set_x(const heap_vart _x) {
    operands()[2] = _x;
  }
  inline void set_f(const heap_fieldt _f) {
    operands()[3] = _f;
  }
  inline void set_y(const heap_vart _y) {
    operands()[4] = _y;
  }

  virtual std::set<heapvar> get_rhs_vars() const {
    std::set<heapvar> res;
    if(!x().is_nil())
      res.insert(x());
    if(!y().is_nil())
      res.insert(y());
    return res;
  }

  virtual std::set<heapvar> get_lhs_vars() const {
    std::set<heapvar> res;
    res.clear();
    return res;
  }

 protected:
  virtual void print(std::ostream& s) const {
    s << mnew() << "=" << "STORE(" << m() << "," << x() << "," << f() << "," << y() << ")";
  }

};

class heap_patht : public heap_litt {
 public:
  heap_patht(const heap_mvart _m, const heap_vart _x, const heap_vart _y, const heap_fieldt _f, lit_statet _state) : heap_litt(_state)
    copy_to_operands(_m, _x, _y, _f);
  }

  inline heap_mvart &m()
  {
    return static_cast<heap_mvart&>op0();
  }
  inline heap_vart &x()
  {
    return static_cast<heap_vart&>op1();
  }
  inline heap_vart &y()
  {
    return static_cast<heap_vart&>op2();
  }
  inline heap_fieldt &f()
  {
    return static_cast<heap_fieldt&>op3();
  }

  inline void set_m(const heap_mvart _m) {
    operands()01] = _m;
  }
  inline void set_x(const heap_vart _x) {
    operands()[1] = _x;
  }
  inline void set_y(const heap_vart _y) {
    operands()[2] = _y;
  }
  inline void set_f(const heap_fieldt _f) {
    operands()[3] = _f;
  }
};


/*********************************************************************************\
 * path(m,x,y,f)                                                                 *
\*********************************************************************************/

class path_lit : public heap_lookup_lit {
 public:
 path_lit(heapvar _m, 
	  heapvar _x, 
	  heapvar _y, 
	  heapvar _f, 
	  uint8_t _state) : heap_lookup_lit(_x, _state) {
    y = _y;
    m = _m;
    f = _f;
    type = PATH;
  }

  path_lit(const heaplit& other) {
    state = other.state;
    type = other.type;
    x = heapvar(other.x);
    y = heapvar(other.y);
    t = heapvar(other.t);
    f = heapvar(other.f);
    m = heapvar(other.m);
    mnew = heapvar(other.mnew);
    rhs = heapexpr(other.rhs);
  }


  virtual std::set<heapvar> get_mems() const {
    std::set<heapvar> res;
    res.insert(m);
    return res;
  }

  virtual std::set<heapvar> get_vars() const {
    std::set<heapvar> res;

    res.insert(x);
    res.insert(y);
    return res;
  }

  virtual std::set<heapvar> get_rhs_vars() const {
    std::set<heapvar> res;
    if(!x.is_nil())
      res.insert(x);
    if(!y.is_nil())
      res.insert(y);

    return res;
  }

  virtual std::set<heapvar> get_lhs_vars() const {
    std::set<heapvar> res;
    res.clear();

    return res;
  }

  void rename_vars_rhs(std::string name, std::string new_name) {
    if (x.name.std::string::compare(name) == 0)
      x.name = new_name;
    if (y.name.std::string::compare(name) == 0)
      y.name = new_name;
  }

  void rename_vars_lhs(std::string name, std::string new_name) {}

 protected:
  virtual void print(std::ostream& s) const {
    s << "PATH(" << this->m << "," << this->x << "," << this->y << "," << this->f << ")";
  }

};

/*********************************************************************************\
 * onpath(m,x,y,z,f)                                                                 *
\*********************************************************************************/

class onpath_lit : public heap_lookup_lit {
 public:
 onpath_lit(heapvar _m, 
	  heapvar _x, 
	  heapvar _y, 
	  heapvar _z, 
	  heapvar _f, 
	  uint8_t _state) : heap_lookup_lit(_x, _state) {
    y = _y;
    z = _z;
    m = _m;
    f = _f;
    type = ONPATH;
  }

  onpath_lit(const heaplit& other) {
    state = other.state;
    type = other.type;
    x = heapvar(other.x);
    y = heapvar(other.y);
    z = heapvar(other.z);
    t = heapvar(other.t);
    f = heapvar(other.f);
    m = heapvar(other.m);
    mnew = heapvar(other.mnew);
    rhs = heapexpr(other.rhs);
  }


  virtual std::set<heapvar> get_mems() const {
    std::set<heapvar> res;
    res.insert(m);
    return res;
  }

  virtual std::set<heapvar> get_vars() const {
    std::set<heapvar> res;

    res.insert(x);
    res.insert(y);
    res.insert(z);
    return res;
  }

  virtual std::set<heapvar> get_rhs_vars() const {
    std::set<heapvar> res;
    if(!x.is_nil())
      res.insert(x);
    if(!y.is_nil())
      res.insert(y);
    if(!z.is_nil())
      res.insert(z);

    return res;
  }

  virtual std::set<heapvar> get_lhs_vars() const {
    std::set<heapvar> res;
    res.clear();

    return res;
  }

  void rename_vars_rhs(std::string name, std::string new_name) {
    if (x.name.std::string::compare(name) == 0)
      x.name = new_name;
    if (y.name.std::string::compare(name) == 0)
      y.name = new_name;
    if (z.name.std::string::compare(name) == 0)
      z.name = new_name;
  }

  void rename_vars_lhs(std::string name, std::string new_name) {}

 protected:
  virtual void print(std::ostream& s) const {
    s << "ONPATH(" << this->m << "," << this->x << "," << this->y << "," << this->z << "," << this->f << ")";
  }

};


/*********************************************************************************\
 * dangling(m,x)                                                                 *
\*********************************************************************************/

class dangling_lit : public heap_lookup_lit {

 public:
 dangling_lit(heapvar _m, 
	      heapvar _x, 
	      uint8_t _state) : heap_lookup_lit(_x, _state) {
    m = _m;
    type = DANGLING;
  }

  dangling_lit(const heaplit& other) {
    state = other.state;
    type = other.type;
    x = heapvar(other.x);
    y = heapvar(other.y);
    t = heapvar(other.t);
    f = heapvar(other.f);
    m = heapvar(other.m);
    mnew = heapvar(other.mnew);
    rhs = heapexpr(other.rhs);
  }

  virtual std::set<heapvar> get_mems() const {
    std::set<heapvar> res;
    res.insert(m);
    return res;
  }

  virtual std::set<heapvar> get_rhs_vars() const {
    std::set<heapvar> res;
    if(!x.is_nil())
      res.insert(x);

    return res;
  }

  virtual std::set<heapvar> get_lhs_vars() const {
    std::set<heapvar> res;
    res.clear();

    return res;
  }

  void rename_vars_rhs(std::string name, std::string new_name) {
    if (x.name.std::string::compare(name) == 0)
      x.name = new_name;
  }

  void rename_vars_lhs(std::string name, std::string new_name) {}

 protected:
  virtual void print(std::ostream& s) const {
    s << "DANGLING(" << this->m << "," << this->x << ")";
  }

};

/*********************************************************************************\
 * disj(m,x,y,z,t,f)                                                             *
\*********************************************************************************/

class disj_lit : public heap_lookup_lit {
 public:
 disj_lit(heapvar _m, 
	  heapvar _x, 
	  heapvar _y, 
	  heapvar _z, 
	  heapvar _t, 
	  heapvar _f, 
	  uint8_t _state) : heap_lookup_lit(_x, _state) {
    type = DISJ;
    z = _z;
    y = _y;
    t = _t;
    m = _m;
    f = _f;
  }

  disj_lit(const heaplit& other) {
    state = other.state;
    type = other.type;
    x = heapvar(other.x);
    y = heapvar(other.y);
    z = heapvar(other.z);
    t = heapvar(other.t);
    f = heapvar(other.f);
    m = heapvar(other.m);
    mnew = heapvar(other.mnew);
    rhs = heapexpr(other.rhs);
  }


  virtual std::set<heapvar> get_mems() const {
    std::set<heapvar> res;
    res.insert(m);
    return res;
  }


  virtual std::set<heapvar> get_rhs_vars() const {
    std::set<heapvar> res;
    if(!x.is_nil())
      res.insert(x);
    if(!y.is_nil())
      res.insert(y);
    if(!z.is_nil())
      res.insert(z);
    if(!t.is_nil())
      res.insert(t);

    return res;
  }

  virtual std::set<heapvar> get_lhs_vars() const {
    std::set<heapvar> res;
    res.clear();

    return res;
  }

  void rename_vars_rhs(std::string name, std::string new_name) {
    if (x.name.std::string::compare(name) == 0)
      x.name = new_name;
    if (y.name.std::string::compare(name) == 0)
      y.name = new_name;
    if (z.name.std::string::compare(name) == 0)
      z.name = new_name;
    if (t.name.std::string::compare(name) == 0)
      t.name = new_name;
  }

  void rename_vars_lhs(std::string name, std::string new_name) {}

 protected:
  virtual void print(std::ostream& s) const {
    s << "DISJ(" << this->m << "," << this->x << "," << this->y << "," << this->z << "," << this->t << "," << this->f << ")";
  }

  virtual std::set<heapvar> get_vars() const {
    std::set<heapvar> res;

    res.insert(x);
    res.insert(y);
    res.insert(z);
    res.insert(t);
    return res;
  }

};

/*********************************************************************************\
 * x = y                                                                         *
\*********************************************************************************/

class eq_lit: public heap_lookup_lit {
 public:
  bool pure;

  eq_lit (heapvar _x, 
	  heapexpr _rhs, 
	  uint8_t _state) : heap_lookup_lit(_x, _state) {
    rhs = _rhs;
    type = EQ;
    pure = true;  // false for assignments
  }

  eq_lit (heapvar _x, 
	  heapexpr _rhs, 
	  uint8_t _state, 
	  bool _pure) : heap_lookup_lit(_x, _state) {
    rhs = _rhs;
    type = EQ;
    pure = _pure;  // used only for loop invariants
  }

  eq_lit (heapvar _x,
  	  heapexpr _rhs,
  	  uint8_t _state,
  	  bool _pure,
  	  bool _dummy) : heap_lookup_lit(_x, _state) {
    rhs = _rhs;
    type = EQ;
    pure = _pure;  // used only for loop invariants
    dummy = _dummy;
  }

  eq_lit(const heaplit& other) {
    state = other.state;
    type = other.type;
    x = heapvar(other.x);
    y = heapvar(other.y);
    t = heapvar(other.t);
    f = heapvar(other.f);
    m = heapvar(other.m);
    mnew = heapvar(other.mnew);
    rhs = heapexpr(other.rhs);
    pure = true;
    dummy = other.dummy;
  }

  virtual std::set<heapvar> get_vars() const {
    std::set<heapvar> res, tmp;

    tmp = rhs.get_vars();
    res.insert(x);
    res.insert(tmp.begin(), tmp.end());
    return res;
  }

  virtual std::set<heapvar> get_mems() const {
    std::set<heapvar> res;
    // no mem vars to add
    res.insert(m);
    return res;
  }

  bool is_pure() const {
    return pure;
  }

  virtual std::set<heapvar> get_rhs_vars() const {
    std::set<heapvar> res;
    if (pure && !x.is_nil())
      res.insert(x);

    std::set<heapvar> tmp = rhs.get_vars();
    res.insert(tmp.begin(), tmp.end());

    return res;
  }

  virtual std::set<heapvar> get_lhs_vars() const {
    std::set<heapvar> res;

    if (!pure && !x.is_nil())
      res.insert(x);

    return res;
  }

  void rename_vars_rhs(std::string name, std::string new_name) 
  {
    if (pure && x.name.std::string::compare(name) == 0)
      x.name = new_name;
    
    rhs.rename_vars(name, new_name);
  }

  void rename_vars_lhs(std::string name, std::string new_name) {
    if (!pure && x.name.std::string::compare(name) == 0)
      x.name = new_name;
  }

 protected:
  virtual void print(std::ostream& s) const {
    s << this->x << "=" << this->rhs;
  }

};


/*************************************************************************\
 * meet-irreducibles.                                                    * 
\*************************************************************************/


// a meet-irreducible is a heaplit, although it should be a heapelem
// it is heaplit so that the trail for deduction and decisions can be unique

//template <> class meetIrreducible<heaplit> {
class meetIrreducible {
  public :
    heaplitp lit;

  public:

  meetIrreducible(const heaplitp _lit) {
    lit = _lit;
  }

  ~meetIrreducible() {
    delete lit;
  }
  

  void complement (void) {
    switch(lit->state) {
    case stateTrue:
      lit->state = stateFalse;
      break;
    case stateFalse:
      lit->state = stateTrue;
      break;
    case stateTop:
      lit->state = stateBottom;
      break;
    case stateBottom:
      lit->state = stateTop;
      break;
    }
  }
};


struct heaplit_comp {

  bool operator() (const heaplit* lhs, const heaplit* rhs) const {
    if (lhs == NULL || rhs == NULL)
      return false;
    return *lhs < *rhs;
  }
};

struct meetIrreducible_comp {
  bool operator() (const meetIrreducible* lhs, const meetIrreducible* rhs) const {
    if (lhs == NULL || rhs == NULL)
      return false;
    return *(lhs->lit) < *(rhs->lit);
  }
};

struct hint_comp {
  bool operator() (const hintt lhs, const hintt rhs) const {
    bool res = false;

    //std::cout << "[hint_comp] : lhs = " << lhs.first << " and rhs = " << rhs.first << std::endl;

    if (lhs.first.size() != rhs.first.size())
      return lhs.first.size() < rhs.first.size();

    if (lhs.first.size() == rhs.first.size() == 1)
      return ((*(lhs.first.begin()))->lit) < ((*(rhs.first.begin()))->lit);
    
    for(solutiont::const_iterator it = lhs.first.begin(); it != lhs.first.end(); ++it)
      if(rhs.first.find(*it) == rhs.first.end())
	return true;

    return false;

    //debugc("[hint_comp] : res = " << res, 1);
    //return res;
  }
};


struct heapelem_comp {
  bool operator() (const heapelem* lhs, const heapelem* rhs) const {
    if (lhs == NULL || rhs == NULL)
      return false;
    bool ret = (*lhs < *rhs);
    return ret;
  }
};

struct inferenceRecord_comp {
  bool operator() (const inferenceRecord* lhs, const inferenceRecord* rhs) const {
    if (lhs == NULL || rhs == NULL)
      return false;
    //todo: fix the reason part
    return (*((lhs->inference)->lit) < *((rhs->inference)->lit)) || (lhs->reason != rhs->reason);
  }
};


meetIrreduciblep copy_lit(const meetIrreduciblep&);
meetIrreduciblep copy_lit(const heaplit&);
heaplit* copy_lit(heaplit*);


std::ostream& operator<< (std::ostream&, const meetIrreducible&);
std::ostream& operator<< (std::ostream&, const meetIrreduciblep&);
std::ostream& operator<< (std::ostream&, const formulat&);
std::ostream& operator<< (std::ostream&, const clauset&);
std::ostream& operator<< (std::ostream&, const trailt&);
std::ostream& operator<< (std::ostream&, const std::vector< meetIrreduciblep >&); 
std::ostream& operator<< (std::ostream&, const std::set< heapvar >&); 
std::ostream& operator<< (std::ostream&, const std::vector< heapvar >&); 
std::ostream& operator<< (std::ostream&, const solutiont&); 
std::ostream& operator<< (std::ostream&, const hintst&); 
std::ostream& operator<< (std::ostream&, const hintt&); 
std::ostream& operator<< (std::ostream&, const not_eqst&); 
std::ostream& operator<< (std::ostream&, const not_eqt&); 
std::ostream& operator<< (std::ostream&, const fld_adj_listt&); 
std::ostream& operator<< (std::ostream&, const mem_adj_listt&); 
std::ostream& operator<< (std::ostream&, const adj_listt&); 
std::ostream& operator<< (std::ostream&, const not_pathst&); 


/*
class keyt {
 public:
  heapvar mem;
  heapvar src;
  heapvar fld;

  keyt(heapvar mem_, heapvar src_, heapvar fld_) {
    mem = mem_;
    src = src_;
    fld = fld_;
  }
  
  bool operator==  (keyt const &other) const {
    return mem == other.mem && src == other.src && fld == other.fld;
  }

  bool operator<  (keyt const &other) const {
    if (!(mem == other.mem)) 
      return mem < other.mem;
    if (!(src == other.src)) 
      return src < other.src;

    return fld < other.fld;
  }

};
*/

std::ostream& operator<< (std::ostream&, const literal_recordt&); 
std::ostream& operator<< (std::ostream&, const literal_tablet&); 

#endif

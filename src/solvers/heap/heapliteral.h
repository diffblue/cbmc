/*
** heaplit.h
**
** A heap abstraction for a single literal. 
**
*/

#ifndef TRP_HEAPLIT
#define TRP_HEAPLIT

#include "heaputil.h"

/** heap theory terms **/
typedef enum { NO_TERM = 0,
               NEW = 1,     // e.g. m' = new(m,x); --> m' is the memory configuration obtained from m after allocating a new memory location pointed by x
	       STORE = 2,   // e.g. m' = st(m,x,f,y); --> m' is the memory configuration obtained from m after the field update x.f=y
	       FREE = 3,    // e.g. m' = free(m,x); --> m' is the memory configuration obtained from m after freeing x
	       PATH = 4,    // e.g. path(m,x,y,f); --> there is a list segment between x and y via field f
	       EQ = 5,      // e.g. x=y; --> x and y are aliases
	       DISJ = 6,    // e.g. disj(m,x,y,z,t,f); --> the list segment between x and y is disjoint from the list segment between z and t (both via f)
	       MEMEQ = 7,   // e.g. m' = m; --> two memory configurations are equal
	       DANGLING = 8,
	       ONPATH = 9
	       //ASSIGN = 9 // this is only used inside a loop, while computing the loop invariant
} heap_term_typet;

// choice of abstract domain
extern domaint mode;

class heapvar {
 public:
  std::string name;
 
 public:
  heapvar() {
    name = "NULL";
  }
  heapvar(std::string _name) {
    name = _name; 
  }
  ~heapvar() {}

  bool operator< (heapvar const &v) const {
    return name.std::string::compare(v.name) < 0;
  }

  bool operator== (heapvar const &v) const {
    return name.std::string::compare(v.name) == 0;
  }

  bool is_nil() const {
    return name.std::string::compare("NULL") == 0;
  }

  void rename(std::string new_name) {
    name = new_name;
  }

};

std::ostream& operator << (std::ostream&, const heapvar&);
std::ostream& operator << (std::ostream&, const ssa_countst&);
std::ostream& operator << (std::ostream&, const std::set<heapvar>&);

class heapexpr {
 public:
  typedef enum {VAR, NIL, SEL} typet;
  typet type;  
  heapvar v;
  heapvar m;
  heapvar f; 

 public:
 heapexpr(): type(VAR), v(heapvar()), m(heapvar()), f(heapvar()) {}
 heapexpr(heapvar _v):  type(VAR), v(_v), m(heapvar()), f(heapvar()) {}
 heapexpr(heapvar _v, heapvar _m, heapvar _f) {
   if (_m.is_nil()) {
     type = VAR;
     v = _v;
   }
   else {
     type = SEL;
     v = _v;
     m = _m;
     f = _f; 
   }
 }

 heapexpr(const heapexpr& other) {
    type = other.type;
    v = heapvar(other.v);
    m = heapvar(other.m);
    f = heapvar(other.f);
  }
 ~heapexpr() {}

  std::set<heapvar> get_vars() const {
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

    debugc("[rename_mems] (BEFORE): m.name = " << m.name, 1);

    if (m.name.std::string::compare(name) == 0)
      m.name = new_name;

    debugc("[rename_mems] (AFTER): m.name = " << m.name, 1);
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
  }

  friend std::ostream& operator<< (std::ostream&, const heapexpr&); 
};


// heap theory literals                                                          
class heaplit {
 public:
  uint8_t state;
  heap_term_typet type;
  heapvar x, y, z, t; 
  heapvar m, mnew;
  heapvar f;
  heapexpr rhs;
  // dummy eq_lit's are introduced during SSA in order to reach the same SSA-number on different branches
  bool dummy;

 public:
 heaplit(): x(heapvar()), 
    y(heapvar()), 
    z(heapvar()), 
    t(heapvar()), 
    m(heapvar()), 
    mnew(heapvar()), 
    f(heapvar()), 
    rhs(heapexpr()) {
    state = stateTop; 
    type = NO_TERM;
    dummy = false;
  }

 heaplit(uint8_t _state):  x(heapvar()), 
    y(heapvar()), 
    z(heapvar()), 
    t(heapvar()), 
    m(heapvar()), 
    mnew(heapvar()), 
    f(heapvar()), 
    rhs(heapexpr()) {
    state = _state; 
    type = NO_TERM;
    dummy = false;
  }

  virtual ~heaplit() {}

  virtual void set_m(const heapvar _m) {
    if (type == EQ)
      rhs.m = _m;
    else
      m = _m;
  }

  void rename_vars(std::string name, std::string new_name) {
    if (x.name.std::string::compare(name) == 0)
      x.name = new_name;
    if (y.name.std::string::compare(name) == 0)
      y.name = new_name;
    if (z.name.std::string::compare(name) == 0)
      z.name = new_name;
    if (t.name.std::string::compare(name) == 0)
      t.name = new_name;
    rhs.rename_vars(name, new_name);
  }

  virtual void rename_vars_rhs(std::string name, std::string new_name) = 0;
  /* { */
  /*   if (y.name.std::string::compare(name) == 0) */
  /*     y.name = new_name; */
  /*   if (z.name.std::string::compare(name) == 0) */
  /*     z.name = new_name; */
  /*   if (t.name.std::string::compare(name) == 0) */
  /*     t.name = new_name; */
  /*   rhs.rename_vars(name, new_name); */
  /* } */

  virtual void rename_vars_lhs(std::string name, std::string new_name) = 0;
  /* { */
  /*   if (x.name.std::string::compare(name) == 0) */
  /*     x.name = new_name; */
  /* } */

  void rename_rhs_mems(std::string name, std::string new_name) {
    if (m.name.std::string::compare(name) == 0)
      m.name = new_name;

    debugc("[rename_rhs_mems] : new_name = " << new_name, 1);
    rhs.rename_mems(name, new_name);
  }

  void rename_lhs_mems(std::string name, std::string new_name) {
    if (mnew.name.std::string::compare(name) == 0)
      mnew.name = new_name;
  }

  virtual std::set<heapvar> get_rhs_vars() const = 0;

  std::set<heapvar> get_rhs_mems() const {
    std::set<heapvar> res, tmp;
    if(!m.is_nil())
      res.insert(m);

    tmp = rhs.get_mems();
    res.insert(tmp.begin(), tmp.end());

    return res;
  }

  std::set<heapvar> get_lhs_mems() const {
    std::set<heapvar> res;
    if(!mnew.is_nil())
      res.insert(mnew);

    return res;
  }

  virtual std::set<heapvar> get_lhs_vars() const = 0;

  virtual void complement() {
    switch(state) {
    case stateTrue:
      state = stateFalse;
      break;
    case stateFalse:
      state = stateTrue;
      break;
    case stateTop:
      state = stateBottom;
      break;
    case stateBottom:
      state = stateTop;
      break;
    }
  }

  /* // same as complement but returns the literal  */
  /* virtual heaplitp negate() { */
  /*   complement(); */
  /*   return this; */
  /* } */

  // return the set of pointer vars in the literal
  virtual std::set<heapvar> get_vars() const = 0;

  // return the set of memory variables in the literal
  virtual std::set<heapvar> get_mems() const = 0;

  bool operator== (const heaplit& other) const { 
    return state == other.state && 
    type == other.type && 
    x == other.x && 
    y == other.y && 
    z == other.z && 
    t == other.t && 
    f == other.f && 
    m == other.m && 
    mnew == other.mnew && 
    rhs == other.rhs;
  }

  bool operator< (const heaplit& other) const { 

    bool ret = state < other.state || (state == other.state &&   
	      (type < other.type || (type == other.type &&
	      (x < other.x || (x == other.x &&
	      (y < other.y || (y == other.y &&
	      (z < other.z || (z == other.z &&
	      (t < other.t || (t == other.t &&
	      (f < other.f || (f == other.f &&
	      (m < other.m || (m == other.m &&
	      (mnew < other.mnew || (mnew == other.mnew && rhs < other.rhs))))))))))))))))); 

    return ret;
  }

  virtual bool is_pure() const = 0;

  friend std::ostream& operator<< (std::ostream& s, const heaplit& hl) {
    if (hl.state == stateFalse)
      s << "¬";
    hl.print(s);
    return s;
  }

  friend std::ostream& operator<< (std::ostream& s, const heaplit* hl) {
    if (hl->state == stateFalse)
      s << "¬";

    hl->print(s);
    return s;
  }

 protected:
  virtual bool equal_to(const heaplit& other) const {
    return state == other.state && 
      type == other.type && 
      x == other.x && 
      y == other.y && 
      z == other.z && 
      t == other.t && 
      f == other.f && 
      m == other.m && 
      mnew == other.mnew && 
      rhs == other.rhs;
  }

 protected:
  virtual void print(std::ostream& s) const {
    return;
  }
};


// literals that mutate the heap                                                
class heap_update_lit : public heaplit {
 public:
  
 public:
 heap_update_lit() : heaplit() {}

 heap_update_lit(heapvar _mnew, heapvar _m, uint8_t _state) : heaplit(_state) {
    m = _m; 
    mnew = _mnew;
  }

  virtual std::set<heapvar> get_mems() const {
    std::set<heapvar> res;
    
    res.insert(m);
    res.insert(mnew);
    return res;
  }

  virtual bool is_pure() const {
    return false;
  }

};


/*********************************************************************************\
 * mnew = st(m,x,f,y)                                                            *
\*********************************************************************************/
class store_lit : public heap_update_lit {
 public:
  //heapvar x, y;
  //heapvar f;
  
 public:
 store_lit(heapvar _mnew, 
	   heapvar _m, 
	   heapvar _x, 
	   heapvar _f, 
	   heapvar _y, 
	   uint8_t _state) : heap_update_lit(_mnew, _m, _state) {
    type = STORE; 
    x = _x; 
    f = _f; 
    y = _y; 
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
    s << this->mnew << "=" << "STORE(" << this->m << "," << this->x << "," << this->f << "," << this->y << ")";
  }

};

/*********************************************************************************\
 * mnew = new(m,x)                                                               *
\*********************************************************************************/
class new_lit : public heap_update_lit {
 public:
  //heapvar x;
  
 public:
 new_lit(heapvar _mnew, 
	 heapvar _m, 
	 heapvar _x, 
	 uint8_t _state) : heap_update_lit(_mnew, _m, _state) {
    type = NEW; 
    x = _x; 
  }

  virtual std::set<heapvar> get_vars() const {
    std::set<heapvar> res;
    res.insert(x);
    return res;
  }

  virtual std::set<heapvar> get_lhs_vars() const {
    std::set<heapvar> res;
    if(!x.is_nil())
      res.insert(x);

    return res;
  }

  virtual std::set<heapvar> get_rhs_vars() const {
    std::set<heapvar> res;
    res.clear();

    return res;
  }

  void rename_vars_lhs(std::string name, std::string new_name) {
    if (x.name.std::string::compare(name) == 0)
      x.name = new_name;
  }

  void rename_vars_rhs(std::string name, std::string new_name) {}

 protected:
  virtual void print(std::ostream& s) const {
    s << this->mnew << "=" << "NEW(" << this->m << "," << this->x << ")";
  }

};

/*********************************************************************************\
 * mnew = free(m,x)                                                              *
\*********************************************************************************/
class free_lit : public heap_update_lit {
 public:
  //heapvar x;
  
 public:
 free_lit(heapvar _mnew, 
	  heapvar _m, 
	  heapvar _x, 
	  uint8_t _state) : heap_update_lit(_mnew, _m, _state) {
    type = FREE; 
    x = _x; 
  }

  virtual std::set<heapvar> get_vars() const {
    std::set<heapvar> res;

    res.insert(x);
    return res;
  }

  virtual std::set<heapvar> get_lhs_vars() const {
    std::set<heapvar> res;
    if(!x.is_nil())
      res.insert(x);

    return res;
  }

  virtual std::set<heapvar> get_rhs_vars() const {
    std::set<heapvar> res;
    res.clear();

    return res;
  }

  void rename_vars_lhs(std::string name, std::string new_name) {
    if (x.name.std::string::compare(name) == 0)
      x.name = new_name;
  }

  void rename_vars_rhs(std::string name, std::string new_name) {}

 protected:
  virtual void print(std::ostream& s) const {
    s << this->mnew << "=" << "FREE(" << this->m << "," << this->x << ")";
  }

};

/*********************************************************************************\
 * mnew = m                                                                      *
\*********************************************************************************/
class mem_eq_lit : public heap_update_lit {
 public:
 mem_eq_lit(heapvar _mnew, 
	    heapvar _m, 
	    uint8_t _state) : heap_update_lit(_mnew, _m, _state) {
    type = MEMEQ;
  }

 protected:
  virtual void print(std::ostream& s) const {
    s << this->mnew << "=" << this->m;
  }


 public: 
  virtual std::set<heapvar> get_vars() const {
    std::set<heapvar> res;

    res.insert(x);
    return res;
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

  void rename_vars_lhs(std::string name, std::string new_name) {}

  void rename_vars_rhs(std::string name, std::string new_name) {}

};


/*********************************************************************************\
 * literals that do not mutate the heap                                          *
\*********************************************************************************/
class heap_lookup_lit : public heaplit {
 public:
  //heapvar x;
  
 public:
 heap_lookup_lit() : heaplit() {}

 heap_lookup_lit(heapvar _x, uint8_t _state) : heaplit(_state) {
    x = _x;
  }

  heap_lookup_lit(const heaplit& other) {
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


  friend std::ostream& operator<< (std::ostream& s, const heap_lookup_lit& hl) {
    if (hl.state == stateFalse)
      s << "¬";
    hl.print(s);
    return s;
  }

  virtual std::set<heapvar> get_vars() const {
    std::set<heapvar> res;
    res.insert(x);
    return res;
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

    std::set<heapvar> tmp = rhs.get_vars();
    res.insert(tmp.begin(), tmp.end());

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

  virtual bool is_pure() const {
    return true;
  }

};

/*********************************************************************************\
 * path(m,x,y,f)                                                                 *
\*********************************************************************************/

class path_lit : public heap_lookup_lit {
  //heapvar m;
  //heapvar y, f;

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
  //heapvar m
  //heapvar y, f;

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
  //heapvar m;
  //heapvar y, z, t;
  //heapvar f;
  
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
    /* if (lhs == NULL && rhs == NULL) */
    /*   return false; */
    if (lhs == NULL || rhs == NULL)
      return false;
    return *lhs < *rhs;
  }
};

struct meetIrreducible_comp {
  bool operator() (const meetIrreducible* lhs, const meetIrreducible* rhs) const {
    /* if (lhs == NULL && rhs == NULL) */
    /*   return false; */
    if (lhs == NULL || rhs == NULL)
      return false;
    return *(lhs->lit) < *(rhs->lit);
  }
};

struct hint_comp {
  bool operator() (const std::pair<meetIrreducible*, hintPriority::s> lhs, const std::pair<meetIrreducible*, hintPriority::s> rhs) const {
    /* if (lhs == NULL && rhs == NULL) */
    /*   return false; */
    if (lhs.first == NULL || rhs.first == NULL)
      return false;
    return *((lhs.first)->lit) < *((rhs.first)->lit);
  }
};


struct heapelem_comp {
  bool operator() (const heapelem* lhs, const heapelem* rhs) const {
    /* if (lhs == NULL && rhs == NULL) */
    /*   return false; */
    if (lhs == NULL || rhs == NULL)
      return false;
    bool ret = (*lhs < *rhs);
    return ret;
  }
};

/* struct heapvar_comp { */
/*   bool operator() (const heapvar lhs, const heapvar rhs) const { */
/*     bool ret = (lhs < rhs); */
/*     return ret; */
/*   } */
/* }; */


struct inferenceRecord_comp {
  bool operator() (const inferenceRecord* lhs, const inferenceRecord* rhs) const {
    /* if (lhs == NULL && rhs == NULL) */
    /*   return false; */
    if (lhs == NULL || rhs == NULL)
      return false;
    //todo: fix the reason part
    return (*((lhs->inference)->lit) < *((rhs->inference)->lit)) || (lhs->reason != rhs->reason);
  }
};


//boost::shared_ptr<heapelem> copy_lit(const heaplit&);
//meetIrreduciblep copy_lit(const heaplit&);
meetIrreduciblep copy_lit(const meetIrreduciblep&);
meetIrreduciblep copy_lit(const heaplit&);


std::ostream& operator<< (std::ostream&, const meetIrreducible&);
std::ostream& operator<< (std::ostream&, const meetIrreduciblep&);
std::ostream& operator<< (std::ostream&, const formulat&);
std::ostream& operator<< (std::ostream&, const clauset&);
std::ostream& operator<< (std::ostream&, const trailt&);
std::ostream& operator<< (std::ostream&, const std::vector< meetIrreduciblep >&); 
std::ostream& operator<< (std::ostream&, const std::set< heapvar >&); 
std::ostream& operator<< (std::ostream&, const std::vector< heapvar >&); 
std::ostream& operator<< (std::ostream&, const solutiont&); 
std::ostream& operator<< (std::ostream&, const hintt&); 
//std::ostream& operator<< (std::ostream&, const equiv_setst&); 
//std::ostream& operator<< (std::ostream&, const equiv_sett&); 
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


#endif

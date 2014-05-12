#include <string>
#include <iostream>
#include <stdint.h>
#include <assert.h>
#include <set>
#include <vector>
#include <boost/shared_ptr.hpp>
#include <map>
#include "util/union_find.h"

#ifndef HEAPUTIL
#define HEAPUTIL

#if 0

#define debugc(s, cond) if (cond) std::cout << s << std::endl;

#else

#define debugc(s, cond);

#endif

#define debug(s) std::cout << s << std::endl;

/* Theory DSL */ 
#define path(m, v1, v2, f) new path_lit(m, v1, v2, f, stateTrue)
#define onpath(m, v1, v2, v3, f) new onpath_lit(m, v1, v2, v3, f, stateTrue)
#define dangling(m, v) new dangling_lit(m, v, stateTrue)
#define equal(v, e) new eq_lit(v, e, stateTrue)
#define not_path(m, v1, v2, f) new path_lit(m, v1, v2, f, stateFalse)
#define not_onpath(m, v1, v2, v3, f) new onpath_lit(m, v1, v2, v3, f, stateFalse)
#define not_dangling(m, v) new dangling_lit(m, v, stateFalse)
#define not_equal(v, e) new eq_lit(v, e, stateFalse)

typedef enum { DISJ_DOMAIN = 0,
	       ONPATH_DOMAIN = 1} domaint;

class heapvar;
class heapexpr;
class heaplit;
class heap_lookup_lit;
struct heapelem_comp;
struct heaplit_comp;
struct meetIrreducible_comp;
struct heaplit_comp;
struct hint_comp;
struct inferenceRecord_comp;
class meetIrreducible;

typedef heap_lookup_lit heapelem;
typedef meetIrreducible* meetIrreduciblep;
typedef std::set< meetIrreduciblep, meetIrreducible_comp> solutiont;

typedef union_find<heapvar> aliasest;

typedef std::pair<heapvar, heapvar> danglingt;
typedef std::set<danglingt> danglingst;

typedef std::pair<heapvar, heapexpr> not_eqt;
typedef std::set<not_eqt> not_eqst;
typedef std::set<not_eqt> sel_eqst;
typedef std::set<heaplit*, heaplit_comp> not_pathst;
typedef std::set<heapvar> targetst;

typedef std::map<heapvar, targetst> fld_adj_listt; 
typedef std::map<heapvar, fld_adj_listt> mem_adj_listt; 
typedef std::map<heapvar, mem_adj_listt> adj_listt; 

namespace hintPriority {
  enum s { High, 
	   Low };
}
typedef std::pair<solutiont, /*hintPriority::s*/unsigned int> hintt;
typedef std::set< hintt, hint_comp > hintst;

typedef heapelem* heapelemp;
typedef heaplit* heaplitp;
typedef std::vector< heaplit* > clauset;
typedef std::vector< clauset* > formulat;

typedef std::pair<heapvar, int> ssa_countt;
typedef std::vector<ssa_countt> ssa_countst;

class formula_ssat {
 public:
  formulat* first;
  ssa_countst* second;

  formula_ssat (formulat* first_, ssa_countst* second_) {
    first = first_;
    second = second_;
  }
};


class condt {
 public:
  formulat* cond;
  formulat* bck_cond;
  ssa_countst* bck_ssa_count;
  
  condt(formulat* cond_, formulat* bck_cond_, ssa_countst* bck_ssa_count_) {
    cond = cond_;
    bck_cond = bck_cond_;
    bck_ssa_count = bck_ssa_count_;
  }
};


const uint8_t stateTop = 0x3;
const uint8_t stateTrue = 0x2;
const uint8_t stateFalse = 0x1;
const uint8_t stateBottom = 0x0;

// watch lists
typedef std::vector<clauset*> watchlist; 
typedef std::vector< std::pair<heaplitp, watchlist*> > watcht;

 class state {
   public:
   heapvar *mem;
   heaplitp hl;
 };

// trail
class inferenceRecord {
 public:
  meetIrreducible* inference;
  void* reason;

  inferenceRecord(meetIrreducible* _inference, void* _reason) {
    inference = _inference;
    reason = _reason;
  }
};

//typedef std::vector< inferenceRecord* > trailt;
typedef std::set< inferenceRecord*, inferenceRecord_comp > trailt;

/** From trp: **/
namespace downwardCompleteness {
  enum s { Bottom, 
	   Complete, 
	   IncompleteProp,
	   IncompleteTransformer,
	   Unknown };
}

namespace entailResult {
  enum s {
    True,
    False,
    Incomplete};
}

class entailResult_ {
 public:
  entailResult::s value;
  std::vector<heaplitp>* reason;

  entailResult_() {
    reason = new std::vector<heaplitp>;
  }

  void set_true() {
    value = entailResult::True;
  }

  void set_false() {
    value = entailResult::False;
  }

  void set_incomplete(std::vector<heaplitp>* reason_) {
    value = entailResult::Incomplete;
    reason = reason_;
  }

  void set_incomplete(heaplitp reason_) {
    value = entailResult::Incomplete;
    reason->push_back(reason_);
  }

  bool is_true() {
    return value == entailResult::True;
  }

  bool is_false() {
    return value == entailResult::False;
  }

  bool is_incomplete() {
    return value == entailResult::Incomplete;
  }

};

namespace upwardCompleteness {
  enum s { Top, 
	   Complete, 
	   Incomplete, 
	   Unknown };
}

namespace meetStatus {
  enum s { Bottom, 
	   Nontrivialmeet, 
	   Included };
}

namespace transformerResult {
  typedef unsigned int s;
  const unsigned int None = 0x0;          /* No progress and no information */
  const unsigned int Bottom = 0x1;        /* Transformer has set the abstraction to Bottom
					     (or detected that it is already bottom). */
  const unsigned int Progress = 0x2;      /* Transformer has changed the abstraction. */
  const unsigned int CallAgain = 0x4;     /* Transformer has not reached a fixed point,
					     calling again may yield a stronger abstraction. */
  const unsigned int DoNotCallAgain = 0x8; /* All points below the current are fixed points.
					      Thus there is no need to call again. */

}

namespace transformerRefinementResult {
  enum s { Bottom = 0, Unknown = 1, NotBottom = 2};
}

typedef std::pair< heaplitp, formulat > literal_recordt;
typedef std::vector< literal_recordt > literal_tablet;

#endif

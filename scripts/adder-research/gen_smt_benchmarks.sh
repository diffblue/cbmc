#!/bin/bash
# Generate a comprehensive set of SMT2 benchmarks for adder evaluation.
# These exercise the smt2_solver's bit-blasting and adder encoding
# through various bitvector addition patterns.

set -e
DIR="${1:-$(dirname "$0")/benchmarks/smt}"
mkdir -p "$DIR"

gen() { cat > "$DIR/$1"; echo "  $1"; }

echo "Generating SMT2 benchmarks..."

# ============================================================
# Basic addition properties
# ============================================================

gen "add_commutative_32.smt2" << 'EOF'
; UNSAT: addition is commutative
(set-logic QF_BV)
(declare-fun a () (_ BitVec 32))
(declare-fun b () (_ BitVec 32))
(assert (distinct (bvadd a b) (bvadd b a)))
(check-sat)
(exit)
EOF

gen "add_associative_32.smt2" << 'EOF'
; UNSAT: addition is associative
(set-logic QF_BV)
(declare-fun a () (_ BitVec 32))
(declare-fun b () (_ BitVec 32))
(declare-fun c () (_ BitVec 32))
(assert (distinct (bvadd a (bvadd b c)) (bvadd (bvadd a b) c)))
(check-sat)
(exit)
EOF

gen "add_identity_32.smt2" << 'EOF'
; UNSAT: zero is additive identity
(set-logic QF_BV)
(declare-fun a () (_ BitVec 32))
(assert (distinct (bvadd a (_ bv0 32)) a))
(check-sat)
(exit)
EOF

gen "add_inverse_32.smt2" << 'EOF'
; UNSAT: a + (-a) = 0
(set-logic QF_BV)
(declare-fun a () (_ BitVec 32))
(assert (distinct (bvadd a (bvneg a)) (_ bv0 32)))
(check-sat)
(exit)
EOF

# ============================================================
# Carry chain reasoning
# ============================================================

gen "carry_chain_16.smt2" << 'EOF'
; UNSAT: carry-save identity: a+b = (a^b) + 2*(a&b)
(set-logic QF_BV)
(declare-fun a () (_ BitVec 16))
(declare-fun b () (_ BitVec 16))
(assert (distinct (bvadd a b)
  (bvadd (bvxor a b) (bvshl (bvand a b) (_ bv1 16)))))
(check-sat)
(exit)
EOF

gen "carry_chain_32.smt2" << 'EOF'
; UNSAT: carry-save identity 32-bit
(set-logic QF_BV)
(declare-fun a () (_ BitVec 32))
(declare-fun b () (_ BitVec 32))
(assert (distinct (bvadd a b)
  (bvadd (bvxor a b) (bvshl (bvand a b) (_ bv1 32)))))
(check-sat)
(exit)
EOF

gen "carry_chain_64.smt2" << 'EOF'
; UNSAT: carry-save identity 64-bit (hard)
(set-logic QF_BV)
(declare-fun a () (_ BitVec 64))
(declare-fun b () (_ BitVec 64))
(assert (distinct (bvadd a b)
  (bvadd (bvxor a b) (bvshl (bvand a b) (_ bv1 64)))))
(check-sat)
(exit)
EOF

gen "carry_propagation_32.smt2" << 'EOF'
; SAT: overflow detection
(set-logic QF_BV)
(declare-fun a () (_ BitVec 32))
(declare-fun b () (_ BitVec 32))
(assert (bvugt a #x7FFFFFFF))
(assert (bvugt b #x7FFFFFFF))
(assert (= ((_ extract 31 31) (bvadd a b)) ((_ extract 31 31) a)))
(check-sat)
(exit)
EOF

# ============================================================
# Multi-operand addition
# ============================================================

gen "add_3operand_16.smt2" << 'EOF'
; UNSAT: (a+b)+c = a+(b+c) for 3 operands
(set-logic QF_BV)
(declare-fun a () (_ BitVec 16))
(declare-fun b () (_ BitVec 16))
(declare-fun c () (_ BitVec 16))
(assert (distinct (bvadd (bvadd a b) c) (bvadd a (bvadd b c))))
(check-sat)
(exit)
EOF

gen "add_4operand_16.smt2" << 'EOF'
; UNSAT: 4-operand associativity
(set-logic QF_BV)
(declare-fun a () (_ BitVec 16))
(declare-fun b () (_ BitVec 16))
(declare-fun c () (_ BitVec 16))
(declare-fun d () (_ BitVec 16))
(assert (distinct (bvadd (bvadd a b) (bvadd c d))
                  (bvadd (bvadd (bvadd a b) c) d)))
(check-sat)
(exit)
EOF

# ============================================================
# Subtraction (addition with negation)
# ============================================================

gen "sub_as_add_32.smt2" << 'EOF'
; UNSAT: a-b = a+(-b)
(set-logic QF_BV)
(declare-fun a () (_ BitVec 32))
(declare-fun b () (_ BitVec 32))
(assert (distinct (bvsub a b) (bvadd a (bvneg b))))
(check-sat)
(exit)
EOF

gen "sub_self_32.smt2" << 'EOF'
; UNSAT: a-a = 0
(set-logic QF_BV)
(declare-fun a () (_ BitVec 32))
(assert (distinct (bvsub a a) (_ bv0 32)))
(check-sat)
(exit)
EOF

# ============================================================
# Overflow / bounds checking
# ============================================================

gen "unsigned_overflow_16.smt2" << 'EOF'
; SAT: unsigned overflow is possible
(set-logic QF_BV)
(declare-fun a () (_ BitVec 16))
(declare-fun b () (_ BitVec 16))
(assert (bvugt a (_ bv0 16)))
(assert (bvugt b (_ bv0 16)))
(assert (bvult (bvadd a b) a))
(check-sat)
(exit)
EOF

gen "unsigned_no_overflow_small_16.smt2" << 'EOF'
; UNSAT: no overflow when both < 2^15
(set-logic QF_BV)
(declare-fun a () (_ BitVec 16))
(declare-fun b () (_ BitVec 16))
(assert (bvult a #x8000))
(assert (bvult b #x8000))
(assert (bvult (bvadd a b) a))
(check-sat)
(exit)
EOF

gen "signed_overflow_32.smt2" << 'EOF'
; SAT: signed overflow is possible
(set-logic QF_BV)
(declare-fun a () (_ BitVec 32))
(declare-fun b () (_ BitVec 32))
(assert (bvsgt a (_ bv0 32)))
(assert (bvsgt b (_ bv0 32)))
(assert (bvslt (bvadd a b) (_ bv0 32)))
(check-sat)
(exit)
EOF

# ============================================================
# Multiplication via addition (stress test)
# ============================================================

gen "mul_by_shift_add_16.smt2" << 'EOF'
; UNSAT: a*3 = a+a+a
(set-logic QF_BV)
(declare-fun a () (_ BitVec 16))
(assert (distinct (bvmul a (_ bv3 16)) (bvadd a (bvadd a a))))
(check-sat)
(exit)
EOF

gen "mul_by_shift_add_32.smt2" << 'EOF'
; UNSAT: a*5 = a + (a<<2)
(set-logic QF_BV)
(declare-fun a () (_ BitVec 32))
(assert (distinct (bvmul a (_ bv5 32))
  (bvadd a (bvshl a (_ bv2 32)))))
(check-sat)
(exit)
EOF

# ============================================================
# Comparison after addition
# ============================================================

gen "add_compare_16.smt2" << 'EOF'
; UNSAT: if a < b then a+1 <= b (for unsigned, no overflow)
(set-logic QF_BV)
(declare-fun a () (_ BitVec 16))
(declare-fun b () (_ BitVec 16))
(assert (bvult a b))
(assert (distinct a #xFFFF))
(assert (bvugt (bvadd a (_ bv1 16)) b))
(check-sat)
(exit)
EOF

gen "add_monotone_32.smt2" << 'EOF'
; UNSAT: if b > 0 and a+b doesn't overflow, then a+b > a
(set-logic QF_BV)
(declare-fun a () (_ BitVec 32))
(declare-fun b () (_ BitVec 32))
(assert (bvugt b (_ bv0 32)))
(assert (bvuge (bvadd a b) a))  ; no overflow
(assert (not (bvugt (bvadd a b) a)))
(check-sat)
(exit)
EOF

# ============================================================
# Wider bitvectors (stress carry chain length)
# ============================================================

gen "add_assoc_64.smt2" << 'EOF'
; UNSAT: associativity 64-bit
(set-logic QF_BV)
(declare-fun a () (_ BitVec 64))
(declare-fun b () (_ BitVec 64))
(declare-fun c () (_ BitVec 64))
(assert (distinct (bvadd a (bvadd b c)) (bvadd (bvadd a b) c)))
(check-sat)
(exit)
EOF

gen "add_inverse_64.smt2" << 'EOF'
; UNSAT: a + (-a) = 0, 64-bit
(set-logic QF_BV)
(declare-fun a () (_ BitVec 64))
(assert (distinct (bvadd a (bvneg a)) (_ bv0 64)))
(check-sat)
(exit)
EOF

gen "carry_save_equiv_8.smt2" << 'EOF'
; UNSAT: carry-save 8-bit (easy baseline)
(set-logic QF_BV)
(declare-fun a () (_ BitVec 8))
(declare-fun b () (_ BitVec 8))
(assert (distinct (bvadd a b)
  (bvadd (bvxor a b) (bvshl (bvand a b) (_ bv1 8)))))
(check-sat)
(exit)
EOF

echo "Generated $(ls "$DIR"/*.smt2 | wc -l) SMT2 benchmarks"

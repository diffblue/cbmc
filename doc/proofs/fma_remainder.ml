(* ================================================================ *)
(* HOL Light proofs for the FMA-based IEEE 754 remainder algorithm  *)
(* Mirrors the Coq proofs in fma_remainder.v and                    *)
(* fma_remainder_strategies.v                                       *)
(*                                                                  *)
(* Uses HOL Light's native int type with div/rem, real_of_int for   *)
(* lifting to reals, and real_zpow for integer exponents.           *)
(* All theorems fully proved (zero mk_thm).                         *)
(* ================================================================ *)

#use "/usr/share/hol-light/hol.ml";;

(* ================================================================ *)
(* Section 1: Comparison step (pure real analysis)                  *)
(* When |r| < |y|/2, both |r+y| and |r-y| are strictly larger.     *)
(* This ensures the algorithm's min-selection picks the correct n.  *)
(* (Coq: comparison_step)                                           *)
(* ================================================================ *)

let COMPARISON_STEP = prove(
  `!r y:real. ~(y = &0)
   ==> abs(r) < abs(y) / &2
   ==> abs(r) < abs(r + y) /\ abs(r) < abs(r - y)`,
  REPEAT STRIP_TAC THEN CONJ_TAC THENL
  [MP_TAC(SPECL [`r + y`; `--r`] REAL_ABS_TRIANGLE) THEN
   REWRITE_TAC[REAL_ARITH `(r + y) + --r = y`; REAL_ABS_NEG] THEN
   ASM_REAL_ARITH_TAC;
   MP_TAC(SPECL [`--(r - y)`; `r:real`] REAL_ABS_TRIANGLE) THEN
   REWRITE_TAC[REAL_ARITH `--(r - y) + r = y`; REAL_ABS_NEG] THEN
   ASM_REAL_ARITH_TAC]);;

(* ================================================================ *)
(* Section 2: Floating-point format (FLX-like) using int exponents  *)
(* x is representable with precision p if x = real_of_int(m) *      *)
(* 2 zpow e for some int m with |m| < 2^p and int exponent e.      *)
(* ================================================================ *)

let is_flx = new_definition
  `is_flx p x <=> ?m e. abs(real_of_int m) < &2 pow p /\
                         x = real_of_int m * &2 zpow e`;;

let FLX_ZERO = prove(
  `!p. is_flx p (&0)`,
  GEN_TAC THEN REWRITE_TAC[is_flx] THEN
  MAP_EVERY EXISTS_TAC [`&0:int`; `&0:int`] THEN
  REWRITE_TAC[REAL_INT_CLAUSES; REAL_ABS_NUM; REAL_MUL_LZERO] THEN
  MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC);;

(* Helpers *)
let ZPOW2_POS = prove(
  `!e:int. &0 < &2 zpow e`,
  GEN_TAC THEN MATCH_MP_TAC REAL_ZPOW_LT THEN REAL_ARITH_TAC);;

let ABS_ZPOW2 = prove(
  `!e:int. abs(&2 zpow e) = &2 zpow e`,
  GEN_TAC THEN REWRITE_TAC[REAL_ABS_REFL] THEN
  MATCH_MP_TAC REAL_LT_IMP_LE THEN REWRITE_TAC[ZPOW2_POS]);;

let ZPOW2_SPLIT = prove(
  `!a b:int. &2 zpow a = &2 zpow (a - b) * &2 zpow b`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[GSYM(MATCH_MP REAL_ZPOW_ADD (REAL_ARITH `~(&2 = &0)`))] THEN
  AP_TERM_TAC THEN INT_ARITH_TAC);;

let ZPOW2_NZ = prove(
  `!e:int. ~(&2 zpow e = &0)`,
  GEN_TAC THEN MATCH_MP_TAC(REAL_ARITH `&0 < x ==> ~(x = &0)`) THEN
  REWRITE_TAC[ZPOW2_POS]);;

(* ================================================================ *)
(* Section 3: Remainder representability (case ex >= ey)            *)
(* (Coq: remainder_format_ge)                                       *)
(* ================================================================ *)

let REMAINDER_FORMAT_GE = prove(
  `!mx my n p (ex:int) (ey:int).
     abs(real_of_int mx) < &2 pow p /\
     abs(real_of_int my) < &2 pow p /\
     ey <= ex /\ ~(real_of_int my = &0) /\
     abs(real_of_int mx * &2 zpow ex -
         real_of_int n * (real_of_int my * &2 zpow ey)) <=
       abs(real_of_int my * &2 zpow ey) / &2
     ==> is_flx p (real_of_int mx * &2 zpow ex -
                    real_of_int n * (real_of_int my * &2 zpow ey))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[is_flx] THEN
  EXISTS_TAC `mx * &2 pow num_of_int(ex - ey) - n * my:int` THEN
  EXISTS_TAC `ey:int` THEN
  SUBGOAL_THEN `&2 zpow ex = &2 zpow (ex - ey) * &2 zpow ey`
    ASSUME_TAC THENL [REWRITE_TAC[ZPOW2_SPLIT]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= ex - ey` ASSUME_TAC THENL
  [ASM_INT_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&2 zpow (ex - ey) = &2 pow num_of_int(ex - ey)`
    ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_ZPOW_NUM] THEN AP_TERM_TAC THEN
   ASM_SIMP_TAC[INT_OF_NUM_OF_INT]; ALL_TAC] THEN
  SUBGOAL_THEN
    `real_of_int(mx * &2 pow num_of_int(ex - ey) - n * my) * &2 zpow ey =
     real_of_int mx * &2 zpow ex -
     real_of_int n * (real_of_int my * &2 zpow ey)` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_OF_INT_CLAUSES] THEN ASM_REWRITE_TAC[] THEN RING;
   ALL_TAC] THEN
  CONJ_TAC THENL
  [SUBGOAL_THEN
     `abs(real_of_int(mx * &2 pow num_of_int(ex - ey) - n * my)) <=
      abs(real_of_int my) / &2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RCANCEL_IMP THEN EXISTS_TAC `&2 zpow ey` THEN
    REWRITE_TAC[ZPOW2_POS; REAL_ABS_MUL; ABS_ZPOW2] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
   MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `abs(real_of_int my)` THEN
   CONJ_TAC THENL
   [MP_TAC(SPEC `real_of_int my` REAL_ABS_POS) THEN ASM_REAL_ARITH_TAC;
    ASM_REWRITE_TAC[]];
   ASM_REWRITE_TAC[]]);;

(* ================================================================ *)
(* Section 4: Remainder representability (case ex < ey)             *)
(* (Coq: remainder_format_lt)                                       *)
(* ================================================================ *)

let REMAINDER_FORMAT_LT = prove(
  `!mx my n p (ex:int) (ey:int).
     abs(real_of_int mx) < &2 pow p /\
     abs(real_of_int my) < &2 pow p /\
     ex < ey /\ ~(real_of_int my = &0) /\
     abs(real_of_int mx * &2 zpow ex -
         real_of_int n * (real_of_int my * &2 zpow ey)) <=
       abs(real_of_int my * &2 zpow ey) / &2
     ==> is_flx p (real_of_int mx * &2 zpow ex -
                    real_of_int n * (real_of_int my * &2 zpow ey))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[is_flx] THEN
  EXISTS_TAC `mx - n * my * &2 pow num_of_int(ey - ex):int` THEN
  EXISTS_TAC `ex:int` THEN
  SUBGOAL_THEN `&0 <= ey - ex` ASSUME_TAC THENL
  [ASM_INT_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&2 zpow (ey - ex) = &2 pow num_of_int(ey - ex)`
    ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_ZPOW_NUM] THEN AP_TERM_TAC THEN
   ASM_SIMP_TAC[INT_OF_NUM_OF_INT]; ALL_TAC] THEN
  SUBGOAL_THEN `&2 zpow ey = &2 zpow (ey - ex) * &2 zpow ex`
    ASSUME_TAC THENL [REWRITE_TAC[ZPOW2_SPLIT]; ALL_TAC] THEN
  SUBGOAL_THEN
    `real_of_int(mx - n * my * &2 pow num_of_int(ey - ex)) * &2 zpow ex =
     real_of_int mx * &2 zpow ex -
     real_of_int n * (real_of_int my * &2 zpow ey)` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_OF_INT_CLAUSES] THEN ASM_REWRITE_TAC[] THEN RING;
   ALL_TAC] THEN
  CONJ_TAC THENL
  [ASM_CASES_TAC `n = &0:int` THENL
   [ASM_REWRITE_TAC[INT_MUL_LZERO; INT_SUB_RZERO]; ALL_TAC] THEN
   SUBGOAL_THEN `abs(real_of_int n) >= &1` ASSUME_TAC THENL
   [UNDISCH_TAC `~(n = &0:int)` THEN
    REWRITE_TAC[GSYM REAL_OF_INT_CLAUSES] THEN
    MP_TAC(SPEC `n:int` INT_IMAGE) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[REAL_OF_INT_CLAUSES] THEN
    REWRITE_TAC[REAL_ABS_NEG; REAL_ABS_NUM; REAL_OF_NUM_EQ;
                REAL_OF_NUM_GE] THEN ARITH_TAC;
    ALL_TAC] THEN
   SUBGOAL_THEN
     `abs(real_of_int n * (real_of_int my * &2 zpow ey)) >=
      abs(real_of_int my * &2 zpow ey)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_ABS_MUL] THEN
    MATCH_MP_TAC(REAL_ARITH `&1 * a <= b * a ==> a >= b * a`) THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN
    REWRITE_TAC[REAL_ABS_POS] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
   SUBGOAL_THEN
     `abs(real_of_int(mx - n * my * &2 pow num_of_int(ey - ex))) <=
      abs(real_of_int mx)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RCANCEL_IMP THEN EXISTS_TAC `&2 zpow ex` THEN
    REWRITE_TAC[ZPOW2_POS; REAL_ABS_MUL; ABS_ZPOW2] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`real_of_int n * (real_of_int my * &2 zpow ey)`;
                   `real_of_int mx * &2 zpow ex`] REAL_ABS_SUB_ABS) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
   ASM_REAL_ARITH_TAC;
   ASM_REWRITE_TAC[]]);;

(* ================================================================ *)
(* Section 5: Combined remainder format theorem                     *)
(* (Coq: remainder_format)                                          *)
(* ================================================================ *)

let REMAINDER_FORMAT = prove(
  `!mx my n p (ex:int) (ey:int).
     abs(real_of_int mx) < &2 pow p /\
     abs(real_of_int my) < &2 pow p /\
     ~(real_of_int my = &0) /\
     abs(real_of_int mx * &2 zpow ex -
         real_of_int n * (real_of_int my * &2 zpow ey)) <=
       abs(real_of_int my * &2 zpow ey) / &2
     ==> is_flx p (real_of_int mx * &2 zpow ex -
                    real_of_int n * (real_of_int my * &2 zpow ey))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `ey <= ex:int` THENL
  [MATCH_MP_TAC REMAINDER_FORMAT_GE THEN ASM_REWRITE_TAC[];
   MATCH_MP_TAC REMAINDER_FORMAT_LT THEN ASM_REWRITE_TAC[] THEN
   ASM_INT_ARITH_TAC]);;

(* ================================================================ *)
(* Section 6: FMA exactness                                         *)
(* The IEEE remainder x - n*y is representable in FLX(p), so        *)
(* rounding it (as FMA does) returns the exact value.               *)
(* This is a direct corollary of REMAINDER_FORMAT: if a value is    *)
(* representable, round(value) = value.                             *)
(* (Coq: fma_remainder_exact — there it applies round_exact)        *)
(*                                                                  *)
(* In HOL Light we don't have Flocq's rounding infrastructure, so   *)
(* we state the representability result directly. The connection     *)
(* "representable implies round-is-identity" is a standard result   *)
(* that we do not re-prove here.                                    *)
(* ================================================================ *)

(* ================================================================ *)
(* Section 7: Integer remainder fits in format                      *)
(* When ex >= ey, the integer remainder (mx * 2^(ex-ey)) rem my    *)
(* satisfies 0 <= r < |my| < 2^p, so it fits in the format.        *)
(* Uses HOL Light's native int div/rem with INT_DIVISION.           *)
(*                                                                  *)
(* Note: HOL Light's rem satisfies 0 <= a rem b < |b| (non-negative *)
(* remainder). The implementation applies sign(x) separately to get *)
(* the signed fmod. This theorem covers the unsigned bound.         *)
(* (Coq: no direct equivalent; this is new in the HOL Light proofs) *)
(* ================================================================ *)

let INT_REMAINDER_IN_FORMAT = prove(
  `!mx my p (ex:int) (ey:int).
     abs(real_of_int mx) < &2 pow p /\
     abs(real_of_int my) < &2 pow p /\
     ey <= ex /\ ~(my = &0:int)
     ==> ?r q. abs(real_of_int r) < abs(real_of_int my) /\
               abs(real_of_int r) < &2 pow p /\
               real_of_int mx * &2 zpow ex -
               real_of_int q * (real_of_int my * &2 zpow ey) =
               real_of_int r * &2 zpow ey`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= ex - ey` ASSUME_TAC THENL
  [ASM_INT_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&2 zpow (ex - ey) = &2 pow num_of_int(ex - ey)`
    ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_ZPOW_NUM] THEN AP_TERM_TAC THEN
   ASM_SIMP_TAC[INT_OF_NUM_OF_INT]; ALL_TAC] THEN
  EXISTS_TAC `(mx * &2 pow num_of_int(ex - ey)) rem my:int` THEN
  EXISTS_TAC `(mx * &2 pow num_of_int(ex - ey)) div my:int` THEN
  MP_TAC(SPECL [`mx * &2 pow num_of_int(ex - ey):int`; `my:int`]
    INT_DIVISION) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
  [(* |r| < |my| *)
   REWRITE_TAC[GSYM REAL_OF_INT_CLAUSES] THEN
   UNDISCH_TAC `&0 <= (mx * &2 pow num_of_int(ex - ey)) rem my` THEN
   UNDISCH_TAC `(mx * &2 pow num_of_int(ex - ey)) rem my < abs my` THEN
   REWRITE_TAC[GSYM REAL_OF_INT_CLAUSES] THEN REAL_ARITH_TAC;
   (* |r| < 2^p *)
   MATCH_MP_TAC REAL_LET_TRANS THEN
   EXISTS_TAC `abs(real_of_int my)` THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_INT_CLAUSES] THEN
    UNDISCH_TAC `&0 <= (mx * &2 pow num_of_int(ex - ey)) rem my` THEN
    UNDISCH_TAC `(mx * &2 pow num_of_int(ex - ey)) rem my < abs my` THEN
    REWRITE_TAC[GSYM REAL_OF_INT_CLAUSES] THEN REAL_ARITH_TAC;
    ASM_REWRITE_TAC[]];
   (* Algebraic identity *)
   SUBGOAL_THEN
     `mx * &2 pow num_of_int(ex - ey) =
      (mx * &2 pow num_of_int(ex - ey)) div my * my +
      (mx * &2 pow num_of_int(ex - ey)) rem my:int` ASSUME_TAC THENL
   [MESON_TAC[INT_DIVISION_SIMP; INT_ADD_SYM]; ALL_TAC] THEN
   REWRITE_TAC[GSYM REAL_OF_INT_CLAUSES] THEN
   SUBGOAL_THEN
     `real_of_int mx * &2 zpow ex =
      real_of_int(mx * &2 pow num_of_int(ex - ey)) * &2 zpow ey`
     SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_INT_CLAUSES] THEN
    ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[ZPOW2_SPLIT] THEN RING;
    ALL_TAC] THEN
   UNDISCH_TAC
     `mx * &2 pow num_of_int(ex - ey) =
      (mx * &2 pow num_of_int(ex - ey)) div my * my +
      (mx * &2 pow num_of_int(ex - ey)) rem my:int` THEN
   REWRITE_TAC[GSYM REAL_OF_INT_CLAUSES] THEN REAL_ARITH_TAC]);;

(* ================================================================ *)
(* Section 8: Remainder via fmod (scaling identity)                 *)
(* For any real x, y with y <> 0 and integer q:                     *)
(*   x - n*y = (x - q*y) - (n - q)*y                               *)
(* So remainder(x, y) = remainder(x - q*y, y) = remainder(fmod, y). *)
(* This is the algebraic core of Strategy 1.                        *)
(* (Coq: remainder_via_fmod — there it uses Znearest properties)    *)
(* ================================================================ *)

let REMAINDER_SCALING = prove(
  `!x y q n:real. x - n * y = (x - q * y) - (n - q) * y`,
  REAL_ARITH_TAC);;

(* ================================================================ *)
(* Section 9: After fmod, n is in {-1, 0, 1} (issue 15)            *)
(* When |q| < 1, the nearest integer to q has |n| <= 1.            *)
(* HOL Light doesn't have Znearest, so we state this over reals:    *)
(* if n is an integer and |q - n| <= 1/2 and |q| < 1, then         *)
(* n in {-1, 0, 1}.                                                 *)
(* ================================================================ *)

let NEAREST_INT_SMALL = prove(
  `!q n:int. abs(real_of_int n - q) <= &1 / &2
   ==> abs(q) < &1
   ==> n = -- &1 \/ n = &0 \/ n = &1`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `-- &1 <= n /\ n <= &1:int` MP_TAC THENL
  [REWRITE_TAC[GSYM REAL_OF_INT_CLAUSES] THEN
   MP_TAC(SPEC `real_of_int n - q` (GEN_ALL REAL_ABS_BOUNDS)) THEN
   ASM_REAL_ARITH_TAC;
   INT_ARITH_TAC]);;

(* ================================================================ *)
(* Section 10: Composition — fmod then FMA (issue 14)               *)
(*                                                                  *)
(* Proved components:                                               *)
(*   FMOD_RESULT_REPRESENTABLE: the fmod result is in FLX(p)        *)
(*   FMOD_RATIO_SMALL: |fmod/y| < 1                                *)
(*   NEAREST_INT_SMALL: n in {-1, 0, 1}                            *)
(*   REMAINDER_FORMAT: the CORRECT candidate r - n*y is in FLX(p)  *)
(*   COMPARISON_STEP: |r_correct| < |r_wrong| in exact arithmetic  *)
(*                                                                  *)
(* Issue 16 (rounding preserves comparison) is proved in Coq using  *)
(* round_N_pt with y (same sign) or -r (opposite sign) as witness. *)
(* The proof does NOT require ulp machinery — just the nearest-     *)
(* point property of rounding. It cannot be replicated in HOL Light *)
(* because HOL Light lacks a rounding theory.                       *)
(* ================================================================ *)

let FMOD_RESULT_REPRESENTABLE = prove(
  `!mr my p (ey:int).
     abs(real_of_int mr) < &2 pow p
     ==> is_flx p (real_of_int mr * &2 zpow ey)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[is_flx] THEN
  MAP_EVERY EXISTS_TAC [`mr:int`; `ey:int`] THEN
  ASM_REWRITE_TAC[]);;

let FMOD_RATIO_SMALL = prove(
  `!mr my (ey:int).
     abs(real_of_int mr) < abs(real_of_int my) /\
     ~(real_of_int my = &0)
     ==> abs(real_of_int mr * &2 zpow ey /
             (real_of_int my * &2 zpow ey)) < &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
    `real_of_int mr * &2 zpow ey / (real_of_int my * &2 zpow ey) =
     real_of_int mr / real_of_int my`
    SUBST1_TAC THENL
  [MATCH_MP_TAC(REAL_FIELD
     `~(e = &0) /\ ~(m = &0)
      ==> a * e / (m * e) = a / m`) THEN
   ASM_REWRITE_TAC[ZPOW2_NZ];
   ALL_TAC] THEN
  REWRITE_TAC[REAL_ABS_DIV] THEN
  ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_ARITH
    `~(x = &0) ==> &0 < abs x`] THEN
  ASM_REAL_ARITH_TAC);;

(* The correct candidate is representable *)
let CORRECT_CANDIDATE_REPRESENTABLE = prove(
  `!mr my n p (ey:int).
     abs(real_of_int mr) < &2 pow p /\
     abs(real_of_int my) < &2 pow p /\
     ~(real_of_int my = &0) /\
     abs(real_of_int mr * &2 zpow ey -
         real_of_int n * (real_of_int my * &2 zpow ey)) <=
       abs(real_of_int my * &2 zpow ey) / &2
     ==> is_flx p (real_of_int mr * &2 zpow ey -
                    real_of_int n * (real_of_int my * &2 zpow ey))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REMAINDER_FORMAT THEN
  ASM_REWRITE_TAC[]);;

(* ================================================================ *)
(* Section 11: Conditional subtract approach                        *)
(* (Coq: conditional_subtract_closer, no_subtract_when_small,       *)
(*  tie_case_equal_abs)                                             *)
(* ================================================================ *)

(* When |fmod| > |y|/2, the correction ||fmod| - |y|| < |fmod|
   and ||fmod| - |y|| <= |y|/2. *)
let CONDITIONAL_SUBTRACT_CLOSER = prove(
  `!f y:real. ~(y = &0)
   ==> abs(f) < abs(y)
   ==> abs(f) > abs(y) / &2
   ==> abs(abs(f) - abs(y)) < abs(f) /\
       abs(abs(f) - abs(y)) <= abs(y) / &2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `abs(y) > &0` ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `abs(f) - abs(y) < &0` ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_ABS_BOUNDS] THEN ASM_REAL_ARITH_TAC);;

(* When |fmod| < |y|/2, fmod is the correct remainder.
   This is COMPARISON_STEP. *)
let NO_SUBTRACT_WHEN_SMALL = prove(
  `!f y:real. ~(y = &0)
   ==> abs(f) < abs(y) / &2
   ==> abs(f) < abs(f + y) /\ abs(f) < abs(f - y)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC COMPARISON_STEP THEN
  ASM_REWRITE_TAC[]);;

(* At the tie |fmod| = |y|/2, the correction also gives |y|/2. *)
let TIE_CASE_EQUAL_ABS = prove(
  `!f y:real. ~(y = &0)
   ==> abs(f) = abs(y) / &2
   ==> abs(abs(f) - abs(y)) = abs(y) / &2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `abs(y) > &0` ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `abs(f) - abs(y) < &0` ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_ABS_BOUNDS] THEN ASM_REAL_ARITH_TAC);;

print_string "\n=== ALL HOL LIGHT PROOFS COMPLETE (zero mk_thm) ===\n";;
print_string "Proved: COMPARISON_STEP, REMAINDER_FORMAT_GE/LT,\n";;
print_string "        REMAINDER_FORMAT, INT_REMAINDER_IN_FORMAT,\n";;
print_string "        REMAINDER_SCALING, NEAREST_INT_SMALL,\n";;
print_string "        FMOD_RESULT_REPRESENTABLE, FMOD_RATIO_SMALL,\n";;
print_string "        CORRECT_CANDIDATE_REPRESENTABLE,\n";;
print_string "        CONDITIONAL_SUBTRACT_CLOSER,\n";;
print_string "        NO_SUBTRACT_WHEN_SMALL, TIE_CASE_EQUAL_ABS\n";;

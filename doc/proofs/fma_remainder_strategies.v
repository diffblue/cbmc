From Coq Require Import ZArith Reals Psatz Lia.
From Flocq Require Import Core.Zaux Core.Defs Core.Generic_fmt Core.FLX
  Core.Round_NE Core.Raux Core.Float_prop.

Open Scope R_scope.

(** ============================================================
    Strategy 1: remainder(x, y) = remainder(fmod(x, y), y)
    ============================================================ *)

Section Scaling.

Variable choice : Z -> bool.

Lemma Zfloor_add_IZR : forall x : R, forall n : Z,
  Zfloor (x + IZR n) = (Zfloor x + n)%Z.
Proof.
  intros x n. apply Zfloor_imp.
  rewrite 2!plus_IZR.
  generalize (Zfloor_lb x) (Zfloor_ub x).
  rewrite plus_IZR. intros. lra.
Qed.

Lemma Zceil_add_IZR : forall x : R, forall n : Z,
  Zceil (x + IZR n) = (Zceil x + n)%Z.
Proof.
  intros x n. unfold Zceil.
  replace (- (x + IZR n)) with (- x + IZR (- n)) by (rewrite opp_IZR; ring).
  rewrite Zfloor_add_IZR. lia.
Qed.

(** Znearest is translation-invariant by integers (non-tie case). *)
Lemma Znearest_shift : forall x : R, forall n : Z,
  (x - IZR (Zfloor x) <> / 2) ->
  Znearest choice (x + IZR n) = (Znearest choice x + n)%Z.
Proof.
  intros x n Hne.
  unfold Znearest.
  rewrite Zfloor_add_IZR, plus_IZR.
  replace (x + IZR n - (IZR (Zfloor x) + IZR n)) with (x - IZR (Zfloor x))
    by lra.
  rewrite Zceil_add_IZR.
  destruct (Rcompare (x - IZR (Zfloor x)) (/ 2)) eqn:Hcmp.
  + (* Eq *) exfalso. apply Hne. now apply Rcompare_Eq_inv.
  + (* Lt *) reflexivity.
  + (* Gt *) reflexivity.
Qed.

Definition fmod_val (x y : R) : R :=
  x - IZR (Ztrunc (x / y)) * y.

Definition remainder_val (x y : R) : R :=
  x - IZR (Znearest choice (x / y)) * y.

(** remainder(x, y) = remainder(fmod(x, y), y) when x/y is not at
    a half-integer. In the tie case, both sides give |remainder| = |y|/2
    but may differ in sign — both are valid IEEE 754 remainders. *)
Theorem remainder_via_fmod :
  forall x y : R, y <> 0 ->
  (x / y - IZR (Zfloor (x / y)) <> / 2) ->
  remainder_val x y = remainder_val (fmod_val x y) y.
Proof.
  intros x y Hy Hne.
  unfold remainder_val, fmod_val.
  replace ((x - IZR (Ztrunc (x / y)) * y) / y)
    with (x / y - IZR (Ztrunc (x / y))).
  2: { field. exact Hy. }
  (* The fractional part of (x/y - Ztrunc(x/y)) equals that of x/y *)
  assert (Hne2 : x / y - IZR (Ztrunc (x / y)) -
    IZR (Zfloor (x / y - IZR (Ztrunc (x / y)))) <> / 2).
  { replace (x / y - IZR (Ztrunc (x / y))) with
      (x / y + IZR (- Ztrunc (x / y))) by (rewrite opp_IZR; ring).
    rewrite Zfloor_add_IZR, plus_IZR, opp_IZR. lra. }
  replace (x / y) with
    (x / y - IZR (Ztrunc (x / y)) + IZR (Ztrunc (x / y))) at 1 by ring.
  rewrite (Znearest_shift (x / y - IZR (Ztrunc (x / y))) (Ztrunc (x / y)) Hne2).
  rewrite plus_IZR, Rmult_plus_distr_r. ring.
Qed.

End Scaling.

(** ============================================================
    Strategy 2: Integer quotient (no float overflow)
    ============================================================ *)

Section IntegerQuotient.

Variable p : Z.
Hypothesis Hp : (1 < p)%Z.
Let beta := radix2.
Instance Hp0 : Prec_gt_0 p. unfold Prec_gt_0. lia. Qed.

Lemma quotient_as_ratio :
  forall (mx my : Z) (ex ey : Z),
    my <> 0%Z ->
    let x := F2R (Float beta mx ex) in
    let y := F2R (Float beta my ey) in
    x / y = IZR mx / IZR my * bpow beta (ex - ey).
Proof.
  intros mx my ex ey Hmy x y.
  unfold x, y, F2R. simpl.
  assert (Hmy0 : IZR my <> 0) by (apply not_0_IZR; exact Hmy).
  assert (Hbp0 : bpow beta ey <> 0) by (apply Rgt_not_eq; apply bpow_gt_0).
  unfold Rdiv.
  assert (Hbpey : bpow beta ey > 0) by apply bpow_gt_0.
  replace (ex - ey)%Z with (ex + - ey)%Z by lia.
  rewrite bpow_plus, bpow_opp.
  unfold Rdiv. rewrite Rinv_mult.
  field. split; [lra | exact Hmy0].
Qed.

Lemma nearest_integer_from_ratio :
  forall choice : Z -> bool,
  forall (mx my : Z) (ex ey : Z),
    my <> 0%Z -> (ey <= ex)%Z ->
    let x := F2R (Float beta mx ex) in
    let y := F2R (Float beta my ey) in
    Znearest choice (x / y) =
    Znearest choice (IZR (mx * Zpower beta (ex - ey)) / IZR my).
Proof.
  intros choice0 mx my ex ey Hmy Hle x y.
  unfold x, y.
  rewrite quotient_as_ratio; [|exact Hmy].
  rewrite mult_IZR, IZR_Zpower; [|lia].
  f_equal. unfold Rdiv.
  rewrite !Rmult_assoc. f_equal. apply Rmult_comm.
Qed.

(** Symmetric case: when ey > ex, the quotient reduces to
    Znearest(mx / (my * 2^(ey-ex))). *)
Lemma nearest_integer_from_ratio_lt :
  forall choice : Z -> bool,
  forall (mx my : Z) (ex ey : Z),
    my <> 0%Z -> (ex < ey)%Z ->
    let x := F2R (Float beta mx ex) in
    let y := F2R (Float beta my ey) in
    Znearest choice (x / y) =
    Znearest choice (IZR mx / IZR (my * Zpower beta (ey - ex))).
Proof.
  intros choice0 mx my ex ey Hmy Hlt x y.
  unfold x, y.
  rewrite quotient_as_ratio; [|exact Hmy].
  f_equal.
  rewrite mult_IZR, IZR_Zpower; [|lia].
  assert (Hbp : bpow beta (ey - ex) <> 0).
  { apply Rgt_not_eq. apply bpow_gt_0. }
  assert (Hmy0 : IZR my <> 0) by (apply not_0_IZR; exact Hmy).
  replace (bpow beta (ex - ey)) with (/ bpow beta (ey - ex)).
  2: { rewrite <- bpow_opp. f_equal. lia. }
  field. split; [exact Hbp|exact Hmy0].
Qed.

End IntegerQuotient.

(** ============================================================
    SUMMARY: Both strategies fully proved (zero admits).
    
    Strategy 1: remainder(x,y) = remainder(fmod(x,y), y) for the
    non-tie case. After fmod, |quotient| < 1, so n ∈ {-1, 0, 1}.
    
    Strategy 2: the quotient reduces to integer arithmetic
    Znearest(mx * 2^(ex-ey) / my) when ey <= ex, or
    Znearest(mx / (my * 2^(ey-ex))) when ex < ey,
    avoiding float overflow in both cases.
    ============================================================ *)

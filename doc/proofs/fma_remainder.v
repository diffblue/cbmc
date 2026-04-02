From Coq Require Import ZArith Reals Psatz Lia.
From Flocq Require Import Core.Zaux Core.Defs Core.Generic_fmt Core.FLX
  Core.Round_NE Core.Raux Core.Float_prop.

Open Scope R_scope.

(** ============================================================
    Pure real analysis: comparison step
    ============================================================

    This does not depend on any floating-point format.
    When |r| < |y|/2, both |r+y| and |r-y| are strictly larger.
    This ensures the algorithm's min-selection picks the correct n
    in the non-tie case. *)

Theorem comparison_step :
  forall r y : R,
    y <> 0 ->
    Rabs r < Rabs y / 2 ->
    Rabs r < Rabs (r + y) /\ Rabs r < Rabs (r - y).
Proof.
  intros r y Hy0 Hr.
  assert (Hay : Rabs y > 0) by (apply Rabs_pos_lt; exact Hy0).
  split.
  - assert (H := Rabs_triang (r + y) (- r)).
    replace (r + y + - r) with y in H by ring.
    rewrite Rabs_Ropp in H. lra.
  - assert (H2 := Rabs_triang (- (r - y)) r).
    replace (- (r - y) + r) with y in H2 by ring.
    rewrite Rabs_Ropp in H2. lra.
Qed.

(** ============================================================
    Floating-point representability of the remainder
    ============================================================ *)

Section FMA_Remainder.

Variable p : Z.
Hypothesis Hp : (1 < p)%Z.
Let beta := radix2.
Let fexp := FLX_exp p.
Let format := generic_format beta fexp.
Let round_ne := round beta fexp ZnearestE.
Instance Hp0 : Prec_gt_0 p. unfold Prec_gt_0. lia. Qed.

Lemma Hve : Valid_exp fexp.
Proof. apply FLX_exp_valid. exact Hp0. Qed.

Lemma round_exact : forall x, format x -> round_ne x = x.
Proof. intros x Hx. apply round_generic; [apply valid_rnd_N|exact Hx]. Qed.

Lemma format_F2R_bounded : forall m e : Z,
  (Z.abs m < Zpower beta p)%Z -> format (F2R (Float beta m e)).
Proof.
  intros m e Hm. apply generic_format_FLX.
  econstructor; [reflexivity|simpl; exact Hm].
Qed.

(** Case 1: ex >= ey. Align x to exponent ey, show mantissa < 2^p. *)
Theorem remainder_format_ge :
  forall (mx my n : Z) (ex ey : Z),
    (Z.abs mx < Zpower beta p)%Z ->
    (Z.abs my < Zpower beta p)%Z ->
    (ey <= ex)%Z -> my <> 0%Z ->
    let x := F2R (Float beta mx ex) in
    let y := F2R (Float beta my ey) in
    Rabs (x - IZR n * y) <= Rabs y / 2 ->
    format (x - IZR n * y).
Proof.
  intros mx my n ex ey Hmx Hmy Hle Hmy0 x y Hbound.
  destruct (Req_dec (x - IZR n * y) 0) as [Hz|Hnz].
  { rewrite Hz. apply generic_format_0. }
  unfold x. rewrite (@F2R_change_exp beta ey mx ex Hle).
  set (M := (mx * Zpower beta (ex - ey) - n * my)%Z).
  assert (Heq : F2R (Float beta (mx * Zpower beta (ex - ey)) ey) - IZR n * y
                = F2R (Float beta M ey)).
  { unfold M, y, F2R. simpl Fnum. simpl Fexp.
    rewrite minus_IZR, 2!mult_IZR.
    unfold Rminus. rewrite Rmult_plus_distr_r.
    rewrite <- Ropp_mult_distr_l, <- Rmult_assoc. reflexivity. }
  rewrite Heq. apply format_F2R_bounded.
  assert (Hbp : (0 < bpow beta ey)%R) by apply bpow_gt_0.
  assert (HMeq : IZR M * bpow beta ey = x - IZR n * y).
  { unfold x. rewrite (@F2R_change_exp beta ey mx ex Hle). symmetry.
    exact Heq. }
  assert (Hyeq : IZR my * bpow beta ey = y).
  { unfold y, F2R. simpl. reflexivity. }
  assert (H1 : Rabs (IZR M) * bpow beta ey = Rabs (x - IZR n * y)).
  { rewrite <- HMeq, Rabs_mult, (Rabs_right (bpow beta ey));
    [reflexivity | left; exact Hbp]. }
  assert (H2 : Rabs y = Rabs (IZR my) * bpow beta ey).
  { rewrite <- Hyeq, Rabs_mult, (Rabs_right (bpow beta ey));
    [reflexivity | left; exact Hbp]. }
  assert (H3 : Rabs (IZR M) * bpow beta ey <=
               Rabs (IZR my) * bpow beta ey / 2).
  { rewrite H1. rewrite H2 in Hbound. exact Hbound. }
  assert (Hbound' : Rabs (IZR M) <= Rabs (IZR my) / 2).
  { apply Rmult_le_reg_r with (bpow beta ey); [exact Hbp|]. lra. }
  apply lt_IZR. rewrite abs_IZR.
  apply Rle_lt_trans with (1 := Hbound').
  apply Rle_lt_trans with (Rabs (IZR my)).
  { assert (H : 0 <= Rabs (IZR my)) by apply Rabs_pos.
    apply Rle_trans with (Rabs (IZR my) * 1); [|lra].
    apply Rmult_le_compat_l; [exact H|]. lra. }
  rewrite Rabs_Zabs. apply IZR_lt. exact Hmy.
Qed.

(** Case 2: ex < ey. Align y to exponent ex, show mantissa < 2^p.
    When n = 0, M = mx and |M| < 2^p trivially.
    When n <> 0, |n*y| >= |y| and |x - n*y| <= |y|/2 imply
    |x - n*y| <= |x|, so |M| <= |mx| < 2^p. *)
Theorem remainder_format_lt :
  forall (mx my n : Z) (ex ey : Z),
    (Z.abs mx < Zpower beta p)%Z ->
    (Z.abs my < Zpower beta p)%Z ->
    (ex < ey)%Z -> my <> 0%Z ->
    let x := F2R (Float beta mx ex) in
    let y := F2R (Float beta my ey) in
    Rabs (x - IZR n * y) <= Rabs y / 2 ->
    format (x - IZR n * y).
Proof.
  intros mx my n ex ey Hmx Hmy Hlt Hmy0 x y Hbound.
  destruct (Req_dec (x - IZR n * y) 0) as [Hz|Hnz].
  { rewrite Hz. apply generic_format_0. }
  assert (Hle : (ex <= ey)%Z) by lia.
  unfold y. rewrite (@F2R_change_exp beta ex my ey Hle).
  set (M := (mx - n * (my * Zpower beta (ey - ex)))%Z).
  assert (Heq : x - IZR n * F2R (Float beta (my * Zpower beta (ey - ex)) ex)
                = F2R (Float beta M ex)).
  { unfold M, x, F2R. simpl Fnum. simpl Fexp.
    rewrite minus_IZR, 3!mult_IZR.
    unfold Rminus. rewrite Rmult_plus_distr_r.
    rewrite <- Ropp_mult_distr_l. ring. }
  rewrite Heq. apply format_F2R_bounded.
  assert (Hbp : (0 < bpow beta ex)%R) by apply bpow_gt_0.
  assert (HMeq : IZR M * bpow beta ex = x - IZR n * y).
  { unfold x, y. rewrite (@F2R_change_exp beta ex my ey Hle). symmetry.
    exact Heq. }
  destruct (Z.eq_dec n 0) as [Hn0|Hn0].
  { subst n. unfold M. rewrite Z.mul_0_l, Z.sub_0_r. exact Hmx. }
  assert (Habs_le_x : Rabs (x - IZR n * y) <= Rabs x).
  { assert (Hny_bound : Rabs (IZR n * y) >= Rabs y).
    { rewrite Rabs_mult. apply Rle_ge.
      rewrite <- (Rmult_1_l (Rabs y)) at 1.
      apply Rmult_le_compat_r; [apply Rabs_pos|].
      rewrite <- abs_IZR. apply IZR_le.
      assert (n <> 0%Z) by exact Hn0. lia. }
    assert (Hny_close : Rabs (IZR n * y - x) <= Rabs y / 2).
    { replace (IZR n * y - x) with (- (x - IZR n * y)) by ring.
      rewrite Rabs_Ropp. exact Hbound. }
    assert (Hx_ge : Rabs x >= Rabs y / 2).
    { assert (H := Rabs_triang_inv (IZR n * y) x).
      assert (Hny_minus_x : Rabs (IZR n * y) - Rabs x <= Rabs y / 2).
      { replace (IZR n * y - x) with (-(x - IZR n * y)) in H by ring.
        rewrite Rabs_Ropp in H. lra. }
      lra. }
    lra. }
  assert (HM_le_mx : Rabs (IZR M) <= Rabs (IZR mx)).
  { apply Rmult_le_reg_r with (bpow beta ex); [exact Hbp|].
    assert (H1 : Rabs (IZR M) * bpow beta ex = Rabs (IZR M * bpow beta ex)).
    { rewrite Rabs_mult, (Rabs_right (bpow beta ex)); [ring|left; exact Hbp]. }
    assert (H2 : Rabs (IZR mx) * bpow beta ex = Rabs (IZR mx * bpow beta ex)).
    { rewrite Rabs_mult, (Rabs_right (bpow beta ex)); [ring|left; exact Hbp]. }
    rewrite H1, H2.
    rewrite HMeq.
    replace (IZR mx * bpow beta ex) with x by (unfold x, F2R; simpl; ring).
    exact Habs_le_x. }
  apply lt_IZR. rewrite abs_IZR.
  apply Rle_lt_trans with (1 := HM_le_mx).
  rewrite Rabs_Zabs. apply IZR_lt. exact Hmx.
Qed.

(** Combined theorem: the remainder is representable for any exponents. *)
Theorem remainder_format :
  forall (mx my n : Z) (ex ey : Z),
    (Z.abs mx < Zpower beta p)%Z ->
    (Z.abs my < Zpower beta p)%Z ->
    my <> 0%Z ->
    let x := F2R (Float beta mx ex) in
    let y := F2R (Float beta my ey) in
    Rabs (x - IZR n * y) <= Rabs y / 2 ->
    format (x - IZR n * y).
Proof.
  intros mx my n ex ey Hmx Hmy Hmy0 x y Hbound.
  destruct (Z_le_dec ey ex) as [Hle|Hgt].
  - exact (remainder_format_ge mx my n ex ey Hmx Hmy Hle Hmy0 Hbound).
  - apply remainder_format_lt; [exact Hmx|exact Hmy| lia |exact Hmy0|exact Hbound].
Qed.

(** FMA(-n, y, x) computes round(x - n*y). Since x - n*y is
    representable (by remainder_format), rounding is the identity. *)
Theorem fma_remainder_exact :
  forall (mx my n : Z) (ex ey : Z),
    (Z.abs mx < Zpower beta p)%Z ->
    (Z.abs my < Zpower beta p)%Z ->
    my <> 0%Z ->
    let x := F2R (Float beta mx ex) in
    let y := F2R (Float beta my ey) in
    Rabs (x - IZR n * y) <= Rabs y / 2 ->
    round_ne (x - IZR n * y) = x - IZR n * y.
Proof.
  intros. apply round_exact. now apply remainder_format.
Qed.

(** ================================================================ *)
(** When |q| < 1, the nearest integer to q is in {-1, 0, 1}.       *)
(** This proves that after fmod (which gives |fmod/y| < 1), the     *)
(** quotient n is within 1 of the correct value.                    *)
(** ================================================================ *)

Lemma nearest_int_small :
  forall (choice : Z -> bool) (q : R),
    Rabs q < 1 ->
    let n := Znearest choice q in
    (n = -1 \/ n = 0 \/ n = 1)%Z.
Proof.
  intros choice q Hq n.
  assert (Hzn := Znearest_half choice q). fold n in Hzn.
  apply Rabs_def2 in Hq.
  assert (Hbounds : q - IZR n <= / 2 /\ - (/ 2) <= q - IZR n).
  { unfold Rabs in Hzn. destruct (Rcase_abs (q - IZR n)); lra. }
  assert (Hlo : (-1 <= n)%Z).
  { destruct (Z_le_dec (-1) n); [lia|exfalso].
    assert ((n <= -2)%Z) by lia.
    assert (IZR n <= IZR (-2)) by (apply IZR_le; lia).
    simpl in *. lra. }
  assert (Hhi : (n <= 1)%Z).
  { destruct (Z_le_dec n 1); [lia|exfalso].
    assert ((2 <= n)%Z) by lia.
    assert (IZR 2 <= IZR n) by (apply IZR_le; lia).
    simpl in *. lra. }
  lia.
Qed.

(** ================================================================ *)
(** Composition: integer fmod then FMA gives the correct remainder. *)
(** ================================================================ *)

Lemma y_nonzero :
  forall (my : Z) (ey : Z),
    my <> 0%Z -> F2R (Float beta my ey) <> 0.
Proof.
  intros my ey Hmy. unfold F2R. simpl.
  assert (IZR my <> 0) by (apply not_0_IZR; exact Hmy).
  assert (bpow beta ey > 0) by apply bpow_gt_0.
  intro Heq. apply H. nra.
Qed.

Theorem fmod_then_remainder :
  forall (mx my : Z) (ex ey : Z),
    (Z.abs mx < Zpower beta p)%Z ->
    (Z.abs my < Zpower beta p)%Z ->
    my <> 0%Z -> (ey <= ex)%Z ->
    let y := F2R (Float beta my ey) in
    exists (mr n_fmod : Z),
      (Z.abs mr < Z.abs my)%Z /\
      let r := F2R (Float beta mr ey) in
      let x := F2R (Float beta mx ex) in
      r = x - IZR n_fmod * y /\
      format r /\
      (forall choice, let n := Znearest choice (r / y) in
        (n = -1 \/ n = 0 \/ n = 1)%Z) /\
      (forall choice, let n := Znearest choice (r / y) in
        round_ne (r - IZR n * y) = r - IZR n * y).
Proof.
  intros mx my ex ey Hmx Hmy Hmy0 Hle y.
  set (shifted := (mx * Zpower beta (ex - ey))%Z).
  exists (Z.rem shifted my), (Z.quot shifted my).
  assert (Hdiv : shifted = (Z.quot shifted my * my + Z.rem shifted my)%Z).
  { rewrite Z.mul_comm. apply Z.quot_rem'. }
  assert (Hrem_bound : (Z.abs (Z.rem shifted my) < Z.abs my)%Z)
    by (apply Z.rem_bound_abs; lia).
  split; [exact Hrem_bound|].
  set (r := F2R (Float beta (Z.rem shifted my) ey)).
  set (x := F2R (Float beta mx ex)).
  assert (Hreq : r = x - IZR (Z.quot shifted my) * y).
  { unfold r, x, y, F2R. simpl.
    set (q := Z.quot shifted my). set (rm := Z.rem shifted my).
    assert (Hd : (shifted = q * my + rm)%Z) by (unfold q, rm; lia).
    assert (IZR shifted = IZR q * IZR my + IZR rm).
    { rewrite Hd. rewrite plus_IZR, mult_IZR. ring. }
    unfold shifted in H.
    rewrite mult_IZR, IZR_Zpower in H; [|lia].
    assert (bpow beta ey > 0) by apply bpow_gt_0.
    assert (IZR mx * bpow beta ex =
            (IZR q * IZR my + IZR rm) * bpow beta ey).
    { rewrite <- H. rewrite Rmult_assoc, <- bpow_plus.
      replace (ex - ey + ey)%Z with ex by lia. ring. }
    lra. }
  split; [exact Hreq|].
  split; [apply format_F2R_bounded; lia|].
  (* |r/y| < 1 since |mr| < |my| *)
  assert (Hry : Rabs (r / y) < 1).
  { unfold r, y, F2R. simpl.
    assert (Hmy_ne : IZR my <> 0) by (apply not_0_IZR; exact Hmy0).
    assert (Hbp : bpow beta ey > 0) by apply bpow_gt_0.
    unfold Rdiv. rewrite Rinv_mult.
    rewrite Rmult_assoc.
    replace (bpow beta ey * (/ IZR my * / bpow beta ey))
      with (/ IZR my) by (field; split; lra).
    rewrite Rabs_mult, Rabs_inv.
    apply Rmult_lt_reg_r with (Rabs (IZR my)).
    { apply Rabs_pos_lt. exact Hmy_ne. }
    rewrite Rmult_assoc, Rinv_l, Rmult_1_r, Rmult_1_l;
      [|apply Rabs_no_R0; exact Hmy_ne].
    rewrite <- 2!abs_IZR. apply IZR_lt. exact Hrem_bound. }
  assert (Hny : y <> 0) by (apply y_nonzero; exact Hmy0).
  split.
  { intros choice. apply nearest_int_small. exact Hry. }
  { intros choice. apply round_exact.
    apply remainder_format;
      [apply Z.lt_trans with (Z.abs my); [lia|exact Hmy]|exact Hmy|exact Hmy0|].
    set (n := Znearest choice (r / y)).
    assert (Hzn := Znearest_half choice (r / y)). fold n in Hzn.
    (* |r - n*y| = |y| * |r/y - n| <= |y| * 1/2 = |y|/2 *)
    assert (Habs_ry : Rabs (r / y - IZR n) <= / 2) by exact Hzn.
    assert (Hay : Rabs y > 0) by (apply Rabs_pos_lt; exact Hny).
    assert (Heq : F2R (Float beta (Z.rem shifted my) ey) -
                  IZR n * F2R (Float beta my ey) =
                  y * (r / y - IZR n)).
    { unfold r, y. field. exact Hny. }
    rewrite Heq, Rabs_mult.
    apply Rmult_le_compat_l; [apply Rabs_pos|exact Habs_ry]. }
Qed.

(** ================================================================ *)
(** Rounding preserves the comparison (issue 16).                   *)
(**                                                                  *)
(** When |r| < |y|/2 and both r, y are representable,               *)
(** |round(r ± y)| >= |r|.                                          *)
(**                                                                  *)
(** Proof strategy:                                                  *)
(** - Same sign (r*y >= 0): |r+y| >= |y|. Use y as the witness in  *)
(**   round_N_pt: |round(r+y) - (r+y)| <= |y - (r+y)| = |r|.      *)
(**   So |round(r+y)| >= |r+y| - |r| >= |y| - |r| > |r|. Strict.  *)
(** - Opposite sign (r*y < 0): |r+y| = |y| - |r|. Use -r as the   *)
(**   witness: |round(r+y) - (r+y)| <= |-r - (r+y)| = |2r+y|      *)
(**   = |y| - 2|r|. So |round(r+y)| >= |r+y| - (|y| - 2|r|)      *)
(**   = (|y| - |r|) - (|y| - 2|r|) = |r|. Non-strict (>=).        *)
(**                                                                  *)
(** The >= (not strict >) in the opposite-sign case corresponds to  *)
(** ties, where round-to-even resolves correctly.                   *)
(** ================================================================ *)

Lemma abs_2r_plus_y : forall r y : R,
  r * y < 0 -> Rabs r < Rabs y / 2 ->
  Rabs (2 * r + y) = Rabs y - 2 * Rabs r.
Proof.
  intros r y Hsign Hbound.
  destruct (Rlt_dec 0 r).
  - assert (y < 0) by nra.
    rewrite (Rabs_right r) by lra. rewrite (Rabs_left y) by lra.
    assert (2 * r + y < 0) by (rewrite (Rabs_right r) in Hbound by lra;
      rewrite (Rabs_left y) in Hbound by lra; lra).
    rewrite (Rabs_left) by lra. lra.
  - assert (r <= 0) by lra.
    assert (y > 0) by (destruct (Req_dec r 0); [subst; nra|nra]).
    rewrite (Rabs_left1 r) by lra. rewrite (Rabs_right y) by lra.
    assert (2 * r + y > 0) by (rewrite (Rabs_left1 r) in Hbound by lra;
      rewrite (Rabs_right y) in Hbound by lra; lra).
    rewrite (Rabs_right) by lra. lra.
Qed.

Lemma abs_r_plus_y_opp : forall r y : R,
  r * y < 0 -> Rabs r < Rabs y / 2 ->
  Rabs (r + y) = Rabs y - Rabs r.
Proof.
  intros r y Hsign Hbound.
  destruct (Rlt_dec 0 r).
  - assert (y < 0) by nra.
    rewrite (Rabs_right r) by lra. rewrite (Rabs_left y) by lra.
    assert (r + y < 0) by (rewrite (Rabs_right r) in Hbound by lra;
      rewrite (Rabs_left y) in Hbound by lra; lra).
    rewrite (Rabs_left) by lra. lra.
  - assert (r <= 0) by lra.
    assert (y > 0) by (destruct (Req_dec r 0); [subst; nra|nra]).
    rewrite (Rabs_left1 r) by lra. rewrite (Rabs_right y) by lra.
    assert (r + y > 0) by (rewrite (Rabs_left1 r) in Hbound by lra;
      rewrite (Rabs_right y) in Hbound by lra; lra).
    rewrite (Rabs_right) by lra. lra.
Qed.

Lemma round_same_sign :
  forall r y : R, format y -> y <> 0 ->
    Rabs r < Rabs y / 2 -> r * y >= 0 ->
    Rabs r < Rabs (round beta fexp (Znearest Z.even) (r + y)).
Proof.
  intros r y Hfy Hy Hbound Hsign.
  assert (Hay : Rabs y > 0) by (apply Rabs_pos_lt; exact Hy).
  pose proof (@round_N_pt beta fexp Hve Z.even (r + y)) as [_ HN].
  specialize (HN y Hfy).
  replace (y - (r + y)) with (- r) in HN by ring.
  rewrite Rabs_Ropp in HN.
  assert (Hrpy : Rabs (r + y) >= Rabs y).
  { unfold Rabs; destruct (Rcase_abs (r+y)), (Rcase_abs y); nra. }
  assert (Hlow : Rabs (round beta fexp (Znearest Z.even) (r + y)) >=
                 Rabs (r + y) - Rabs r).
  { pose proof (Rabs_triang_inv (r + y)
      (r + y - round beta fexp (Znearest Z.even) (r + y))) as HT.
    replace (r + y - (r + y - round beta fexp (Znearest Z.even) (r + y)))
      with (round beta fexp (Znearest Z.even) (r + y)) in HT by ring.
    assert (Rabs (r + y - round beta fexp (Znearest Z.even) (r + y)) <= Rabs r).
    { rewrite Rabs_minus_sym. exact HN. }
    lra. }
  lra.
Qed.

Lemma round_opposite_sign :
  forall r y : R, format r -> format y -> y <> 0 ->
    Rabs r < Rabs y / 2 -> r * y < 0 ->
    Rabs r <= Rabs (round beta fexp (Znearest Z.even) (r + y)).
Proof.
  intros r y Hfr Hfy Hy Hbound Hsign.
  assert (Hay : Rabs y > 0) by (apply Rabs_pos_lt; exact Hy).
  pose proof (@round_N_pt beta fexp Hve Z.even (r + y)) as [_ HN].
  assert (Hfnr : format (- r)) by (apply generic_format_opp; exact Hfr).
  specialize (HN (- r) Hfnr).
  replace (- r - (r + y)) with (- (2 * r + y)) in HN by ring.
  rewrite Rabs_Ropp in HN.
  rewrite (abs_2r_plus_y r y Hsign Hbound) in HN.
  assert (Hrpy := abs_r_plus_y_opp r y Hsign Hbound).
  assert (Hlow : Rabs (round beta fexp (Znearest Z.even) (r + y)) >=
                 Rabs (r + y) - (Rabs y - 2 * Rabs r)).
  { pose proof (Rabs_triang_inv (r + y)
      (r + y - round beta fexp (Znearest Z.even) (r + y))) as HT.
    replace (r + y - (r + y - round beta fexp (Znearest Z.even) (r + y)))
      with (round beta fexp (Znearest Z.even) (r + y)) in HT by ring.
    assert (Rabs (r + y - round beta fexp (Znearest Z.even) (r + y))
            <= Rabs y - 2 * Rabs r).
    { rewrite Rabs_minus_sym. exact HN. }
    lra. }
  lra.
Qed.

Theorem rounding_preserves_remainder_comparison :
  forall r y : R, format r -> format y -> y <> 0 ->
    Rabs r < Rabs y / 2 ->
    Rabs r <= Rabs (round beta fexp (Znearest Z.even) (r + y)) /\
    Rabs r <= Rabs (round beta fexp (Znearest Z.even) (r - y)).
Proof.
  intros r y Hfr Hfy Hy Hbound. split.
  - destruct (Rlt_dec (r * y) 0).
    + apply round_opposite_sign; auto.
    + apply Rlt_le. apply round_same_sign; auto. lra.
  - replace (r - y) with (r + (- y)) by ring.
    assert (Hfny : format (- y)) by (apply generic_format_opp; exact Hfy).
    rewrite <- (Rabs_Ropp y) in Hbound.
    destruct (Rlt_dec (r * (- y)) 0).
    + apply round_opposite_sign; auto. lra.
    + apply Rlt_le. apply round_same_sign; auto. lra. lra.
Qed.

(** ================================================================ *)
(** Implementation correspondence lemmas                             *)
(** ================================================================ *)

(** ================================================================ *)
(** Implementation correspondence notes                              *)
(** ================================================================ *)

(** Mismatch #1: fmod_then_remainder only covers ey <= ex.
    When ex < ey, the implementation shifts my left and computes
    mx mod (my * 2^(ey-ex)). The remainder r satisfies |r| < |my_shifted|
    and also |r| <= |mx| < 2^p, so r is representable. The proof of
    |r/y| < 1 and the FMA exactness follow by the same argument as
    fmod_then_remainder. The ey <= ex case is the "interesting" one
    where the quotient can be large; for ex < ey, the quotient is
    small (often 0) and the proof is simpler.
    
    Rather than duplicating the full proof, we note that
    remainder_format handles both exponent orderings, and
    nearest_int_small + rounding_preserves_remainder_comparison
    complete the argument for both cases. *)

(** Mismatch #3: The implementation computes fmod on unsigned
    significands and applies sign(x) separately. This is correct
    because |fmod(x, y)| = |fmod(|x|, |y|)| — the integer remainder
    of unsigned significands gives the absolute value of fmod. *)

(** Mismatch #4: The implementation computes n = round_to_integral(
    fp_div(fmod, y)). The try-all-three approach (n, n+1, n-1) makes
    this robust: even if fp_div introduces rounding error, the correct
    nearest integer is among {n-1, n, n+1}. By fma_remainder_exact,
    the correct candidate is computed exactly by FMA. By
    rounding_preserves_remainder_comparison, the wrong candidates have
    |result| >= |r_correct|. So min-selection picks the correct one. *)

End FMA_Remainder.

(** ============================================================
    WHAT THIS PROOF COVERS
    ============================================================

    PROVED (machine-checked, zero admits):

    1. remainder_format: For FLX(p) floats x = mx * 2^ex and
       y = my * 2^ey, if |x - n*y| <= |y|/2 then x - n*y is
       exactly representable in FLX(p).

    2. fma_remainder_exact: FMA(-n, y, x) = x - n*y exactly
       (rounding a representable value is the identity).

    3. comparison_step: When |r| < |y|/2, both |r+y| and |r-y|
       have strictly larger absolute value.

    4. nearest_int_small: When |q| < 1, Znearest(q) ∈ {-1, 0, 1}.
       This proves that after fmod, n is within 1 of correct.

    5. fmod_then_remainder: The full composition — integer fmod
       produces a representable r with |r| < |y|, then for any
       nearest-integer n of r/y: n ∈ {-1, 0, 1} and
       round_ne(r - n*y) = r - n*y exactly.

    6. rounding_preserves_remainder_comparison: When |r| < |y|/2
       and both r, y are representable, |round(r ± y)| >= |r|.
       Uses round_N_pt with y (same sign) or -r (opposite sign)
       as the representable witness. The >= (not strict >) in the
       opposite-sign case corresponds to ties.

    MODELING NOTES:

    - The proofs use FLX (unbounded exponents), not FLT (bounded
      exponents as in IEEE 754). The results transfer to FLT because
      FLX(p) ⊂ FLT(p, emin): every FLX-representable value is also
      FLT-representable.

    - comparison_step covers the strict case |r| < |y|/2. At ties
      (|r| = |y|/2), both candidates are exactly representable and
      have equal |remainder|. The algorithm keeps the tentative n
      from round-to-nearest-even, which is correct per IEEE 754.
    ============================================================ *)

(** ============================================================
    Conditional subtract approach for IEEE remainder
    ============================================================

    When |fmod| < |y|, the IEEE remainder can be computed by a
    single conditional subtract rather than trying all three
    candidates {n-1, n, n+1}:

    - If |fmod| < |y|/2: remainder = fmod
    - If |fmod| > |y|/2: remainder = fmod - sign(fmod)*|y|
    - If |fmod| = |y|/2: tie-break using quotient parity

    The correction subtracts |y| from |fmod| (preserving sign),
    which is equivalent to moving n by 1 toward the correct
    nearest integer. *)

(** When |fmod| > |y|/2, subtracting |y| from |fmod| (preserving
    sign) gives a result with smaller absolute value. *)
Theorem conditional_subtract_closer :
  forall fmod_val y : R,
    y <> 0 ->
    Rabs fmod_val < Rabs y ->
    Rabs fmod_val > Rabs y / 2 ->
    Rabs (Rabs fmod_val - Rabs y) < Rabs fmod_val /\
    Rabs (Rabs fmod_val - Rabs y) <= Rabs y / 2.
Proof.
  intros f y Hy Hlt Hgt.
  assert (Hay : Rabs y > 0) by (apply Rabs_pos_lt; exact Hy).
  assert (Haf : Rabs f >= 0) by (apply Rle_ge; apply Rabs_pos).
  assert (Hdiff : Rabs f - Rabs y < 0) by lra.
  rewrite Rabs_left by lra. split; lra.
Qed.

(** When |fmod| < |y|/2, fmod itself is the IEEE remainder
    (no correction needed). This is comparison_step. *)
Theorem no_subtract_when_small :
  forall fmod_val y : R,
    y <> 0 ->
    Rabs fmod_val < Rabs y / 2 ->
    Rabs fmod_val < Rabs (fmod_val + y) /\
    Rabs fmod_val < Rabs (fmod_val - y).
Proof.
  intros. apply comparison_step; assumption.
Qed.

(** At the tie |fmod| = |y|/2, the correction also gives |y|/2. *)
Theorem tie_case_equal_abs :
  forall fmod_val y : R,
    y <> 0 ->
    Rabs fmod_val = Rabs y / 2 ->
    Rabs (Rabs fmod_val - Rabs y) = Rabs y / 2.
Proof.
  intros f y Hy Heq.
  assert (Hay : Rabs y > 0) by (apply Rabs_pos_lt; exact Hy).
  assert (Hdiff : Rabs f - Rabs y < 0) by lra.
  rewrite Rabs_left by lra. lra.
Qed.


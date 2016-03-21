(** *** The Baire Category Theorem for complete metric spaces  by  Ken'ichi Kuga ****)
(** Simplified using SSReflect by Mitsuharu Yamamoto **)
(** ***************************************************************

Theorem BaireCategoryTheorem :  complete d d_metric -> baire_space.

******************************************************************)
Require Import ClassicalChoice.
Require Export ChoiceFacts.
Require Import Reals.
Require Import Fourier.
From mathcomp
Require Import ssreflect ssrbool.
From Topology
Require Export MetricSpaces Completeness RationalsInReals.
From ZornsLemma
Require Import EnsemblesSpec.

Open Scope R_scope.

Section BaireSpaces.

Variable X : TopologicalSpace.

(* We use the the following form of the Axiom of Choice *)
Lemma FDC : FunctionalDependentChoice_on (point_set X * { r:R | r > 0} * nat).
Proof.
  apply: functional_choice_imp_functional_dependent_choice.
  exact: choice.
Qed.

(* Definition of Baire Spaces *)
Definition baire_space : Prop :=
  forall V : IndexedFamily nat (point_set X),
    (forall n: nat, (open (V n)) /\ (dense (V n))) ->
       dense (IndexedIntersection V).

(* Introducing metric metrizing X *)
Variable d : (point_set X) -> (point_set X) -> R.
Hypothesis d_metric : metric d.
Hypothesis d_metrizes : metrizes X d.

(* Some definitions and lemmas  *)

Lemma ln_mult_pow : forall a:R, a > 0 ->
  forall k:nat, (INR k)*(ln a) = ln (a^k).
Proof.
move=>a a_pos.
induction k.
simpl.
rewrite Rmult_0_l.
rewrite ln_1.
reflexivity.
have H: S k = (k + 1)%nat by auto with *.
rewrite H; clear H.
have H1: INR (k + 1)%nat = (INR k ) + 1 by apply plus_INR.
rewrite H1; clear H1.
have H2: (INR k + 1) * ln a = (INR k) * ln a + 1 * ln a.
apply Rmult_plus_distr_r.
rewrite H2.
have H3: a^(k+1) = a^k * a^1 by auto with real.
rewrite H3.
clear H2 H3.
have H4: ln (a^k * a^1) = ln (a^k) + ln (a^1).
apply ln_mult.
move: a_pos; by auto with real.
move: a_pos; by auto with real.
rewrite H4; clear H4.
rewrite IHk.
have H5: 1 * ln a = ln a by auto with real.
rewrite H5; clear H5.
have H6: a^1 =a by auto with real.
rewrite H6; clear H6.
reflexivity.
Qed.


Lemma Req_move_pr2ml: forall r1 r2 r : R, r1 = r2 + r -> r1 - r = r2.
Proof.
move=> r1 r2 r ->.
by rewrite /Rminus Rplus_assoc Rplus_opp_r Rplus_0_r.
Qed.

Lemma Req_move_pl2mr: forall r1 r2 r : R, r1 + r = r2 -> r1 = r2 - r.
Proof.
by move=> r1 r2 r; symmetry; apply: Req_move_pr2ml; symmetry.
Qed.

Lemma Req_move_mr2pl: forall r1 r2 r : R, r1 = r2 - r -> r1 + r = r2.
Proof.
move=> r1 r2 r ->.
by rewrite /Rminus Rplus_assoc Rplus_opp_l Rplus_0_r.
Qed.

Lemma Req_move_ml2pr: forall r1 r2 r : R, r1 - r = r2 -> r1 = r2 + r.
Proof.
by move=> r1 r2 r; symmetry; apply: Req_move_mr2pl; symmetry.
Qed.

Lemma Rle_move_pr2ml: forall r1 r2 r : R, r1 <= r2 + r -> r1 - r <= r2.
Proof.
move=> r1 r2 r lhs.
rewrite /Rminus (_ : r2 = r2 + r + -r); first auto with real.
by rewrite Rplus_assoc Rplus_opp_r Rplus_0_r.
Qed.

Lemma Rle_move_pl2mr: forall r1 r2 r : R, r1 + r <= r2 -> r1 <= r2 - r.
Proof.
move=> r1 r2 r lhs.
rewrite /Rminus (_ : r1 = r1 + r + -r ); first auto with real.
by rewrite Rplus_assoc Rplus_opp_r Rplus_0_r.
Qed.

Lemma Rle_move_mr2pl: forall r1 r2 r : R, r1 <= r2 - r -> r1 + r <= r2.
Proof.
move=> r1 r2 r lhs.
rewrite /Rminus (_ : r2 = r2 + -r + r); first auto with real.
by rewrite Rplus_assoc Rplus_opp_l Rplus_0_r.
Qed.

Lemma Rle_move_ml2pr: forall r1 r2 r : R, r1 - r <= r2 -> r1 <= r2 + r.
Proof.
move=> r1 r2 r lhs.
rewrite /Rminus (_ : r1 = r1 + -r + r); first auto with real.
by rewrite Rplus_assoc Rplus_opp_l Rplus_0_r.
Qed.

Lemma Rlt_move_pr2ml: forall r1 r2 r : R, r1 < r2 + r -> r1 - r < r2.
Proof.
move=> r1 r2 r lhs.
rewrite /Rminus (_ : r2 = r2 + r + -r); first auto with real.
by rewrite Rplus_assoc Rplus_opp_r Rplus_0_r.
Qed.

Lemma Rlt_move_pl2mr: forall r1 r2 r : R, r1 + r < r2 -> r1 < r2 - r.
Proof.
move=> r1 r2 r lhs.
rewrite /Rminus (_ : r1 = r1 + r + -r ); first auto with real.
by rewrite Rplus_assoc Rplus_opp_r Rplus_0_r.
Qed.

Lemma Rlt_move_mr2pl: forall r1 r2 r : R, r1 < r2 - r -> r1 + r < r2.
Proof.
move=> r1 r2 r lhs.
rewrite /Rminus (_ : r2 = r2 + -r + r); first auto with real.
by rewrite Rplus_assoc Rplus_opp_l Rplus_0_r.
Qed.

Lemma Rlt_move_ml2pr: forall r1 r2 r : R, r1 - r < r2 -> r1 < r2 + r.
Proof.
move=> r1 r2 r lhs.
rewrite /Rminus (_ : r1 = r1 + -r + r); first auto with real.
by rewrite Rplus_assoc Rplus_opp_l Rplus_0_r.
Qed.

Lemma Rge_move_pr2ml: forall r1 r2 r : R, r1 >= r2 + r -> r1 - r >= r2.
Proof.
by move=> r1 r2 r /Rge_le /Rle_move_pl2mr /Rle_ge.
Qed.

Lemma Rge_move_pl2mr: forall r1 r2 r : R, r1 + r >= r2 -> r1 >= r2 - r.
Proof.
by move=> r1 r2 r /Rge_le /Rle_move_pr2ml /Rle_ge.
Qed.

Lemma Rge_move_mr2pl: forall r1 r2 r : R, r1 >= r2 - r -> r1 + r >= r2.
Proof.
by move=> r1 r2 r /Rge_le /Rle_move_ml2pr /Rle_ge.
Qed.

Lemma Rge_move_ml2pr: forall r1 r2 r : R, r1 - r >= r2 -> r1 >= r2 + r.
Proof.
by move=> r1 r2 r /Rge_le /Rle_move_mr2pl /Rle_ge.
Qed.

Lemma Rgt_move_pr2ml: forall r1 r2 r : R, r1 > r2 + r -> r1 - r > r2.
Proof.
by move=> r1 r2 r /Rlt_move_pl2mr.
Qed.

Lemma Rgt_move_pl2mr: forall r1 r2 r : R, r1 + r > r2 -> r1 > r2 - r.
Proof.
by move=> r1 r2 r /Rlt_move_pr2ml.
Qed.

Lemma Rgt_move_mr2pl: forall r1 r2 r : R, r1 > r2 - r -> r1 + r > r2.
Proof.
by move=> r1 r2 r /Rlt_move_ml2pr.
Qed.

Lemma Rgt_move_ml2pr: forall r1 r2 r : R, r1 - r > r2 -> r1 > r2 + r.
Proof.
by move=> r1 r2 r /Rlt_move_mr2pl.
Qed.

Lemma Rle_pow_inv2_1: forall n:nat, (/2)^n <= 1.
Proof.
move=> n.
rewrite -[x in _ <= x](pow1 n).
apply: pow_incr.
split; first auto with real.
rewrite -[x in _ <= x]Rinv_1.
by apply: Rinv_le_contravar; auto with real.
Qed.

(*************************************************)

Lemma Rle_n_pow_2_n: forall n:nat,  (INR n) <= (2^n).
Proof.
elim => [| n IHn] ; first auto with real.
rewrite [in x in x <= _](_ : S n = (n + 1)%nat); last by auto with *.
rewrite /= (_ : INR (n + 1) = INR n + INR 1); last by auto with real.
rewrite (_ : 2 * 2 ^ n = 2 ^ n + 2 ^ n); last by field.
apply: Rplus_le_compat => //.
apply: pow_R1_Rle.
by auto with real.
Qed.

Lemma pow_inv_2_n_approach_0: forall eps : R, eps > 0 ->
  exists N : nat, forall n : nat, (n >= N)%nat -> (/2)^n <= eps.
Proof.
move=> eps eps_pos.
case: (inverses_of_nats_approach_0 _ eps_pos) => N [HNpos HNlt].
exists N => n lenN.
move/Rlt_le: HNlt; apply: Rle_trans.
rewrite -Rinv_pow; last by discrR.
apply: Rinv_le_contravar; first auto with real.
apply: Rle_trans (_ : INR n <= _); last by apply: Rle_n_pow_2_n.
by auto with real.
Qed.

(*************************************************)
Lemma open_ball_is_open:
  forall (x: point_set X) (r: R),
    r > 0 -> open (open_ball (point_set X) d x r).
Proof.
move=> x r H_r_pos.
have H_In_MTOB_oball:
  In (metric_topology_neighborhood_basis d x)
     (open_ball (point_set X) d x r)
  by constructor.
have: open_neighborhood (open_ball (point_set X) d x r) x.
  by apply: (open_neighborhood_basis_elements (metric_topology_neighborhood_basis d x) x).
by case.
Qed.

Lemma open_ball_in_open_set:
  forall (x : point_set X) (U : Ensemble (point_set X)),
    open U -> In U x  ->
    exists r : R, r > 0 /\
      Included (open_ball (point_set X) d x r) U.
Proof.
move=> x U open_U In_U_x.
have [oball [[r H_rpos] HbInU]]:
  exists oball : Ensemble (point_set X),
        In (metric_topology_neighborhood_basis d x ) oball /\
        Included oball U
  by apply: (open_neighborhood_basis_cond
               (metric_topology_neighborhood_basis d x) x (d_metrizes x)).
by exists r.
Qed.

Definition closed_ball (x0 : point_set X) (r : R):
  Ensemble (point_set X):=
     fun (x : point_set X)  => d x0 x <= r.

Lemma closed_ball_is_closed :
  forall (x0: point_set X) (r: R), closed (closed_ball x0 r).
Proof.
move=> x0 r0; rewrite /closed.
pose cover (xd: { x: point_set X | d x0 x > r0 }%type) :=
  open_ball (point_set X) d (proj1_sig xd) (d x0 (proj1_sig xd) - r0).
suff ->: Complement (closed_ball x0 r0) = IndexedUnion cover.
{ apply: open_indexed_union => xd.
  apply: open_ball_is_open.
  apply: Rgt_minus.
  exact: (proj2_sig xd).
}
apply: Extensionality_Ensembles; split.
- move=> x /Rnot_le_gt dx0x_gt_r0.
  exists (exist _ x dx0x_gt_r0).
  constructor => //=.
  rewrite metric_zero //.
  exact: Rgt_minus.
- move=> _ [a x [/Rlt_move_mr2pl]].
  rewrite (metric_sym _ _ d_metric) Rplus_comm => /Rlt_move_pl2mr H.
  apply: Rgt_not_le.
  apply: Rge_gt_trans (_ : d x0 (proj1_sig a) - d x (proj1_sig a) > _) => //.
  apply: Rge_move_pl2mr.
  apply: Rle_ge.
  exact: triangle_inequality.
Qed.

(* The Baire Category Theorem for complete metric spaces *)

Theorem BaireCategoryTheorem :  complete d d_metric -> baire_space.

Proof.

move=> H_cplt V H_od.
apply: Extensionality_Ensembles; split => // x H.
apply: meets_every_open_neighborhood_impl_closure => U H_opn_U H_In_U_x.
pose IStep (xrn0 xrn1: point_set X * { r:R | r > 0} * nat) :=
  snd xrn1 = S (snd xrn0) /\
  proj1_sig (snd (fst xrn1)) <= (proj1_sig (snd (fst xrn0))) * /2 /\
  d (fst (fst xrn0)) (fst (fst xrn1)) < (proj1_sig (snd (fst xrn0))) * /2 /\
  Included
    (open_ball _ d (fst (fst xrn1)) (2*proj1_sig (snd (fst xrn1))))
    (V (snd xrn1)).
(* step 0 *)
have [x0] : Inhabited (Intersection (V 0%nat) U).
  by apply: dense_meets_every_nonempty_open => //;
     [case: (H_od 0%nat) | exists x].
case/open_ball_in_open_set;
  first by apply: open_intersection2 => //; case (H_od 0%nat).
move=> r0_t [r0_t_pos Inc_ball_V0U].
pose r0 := r0_t/2.
have r0_pos: r0>0 by rewrite /r0; fourier.
pose rp0 := exist (fun r:R => r>0)r0 r0_pos.
(**** Axiom of Choice used *******)
have [Fn [H_0 H_n]]: exists Fn : nat -> point_set X * { r:R | r>0 } * nat,
    (Fn 0%nat) = (pair (pair x0 rp0) 0%nat) /\
    (forall n : nat, (IStep (Fn n) (Fn (S n)))).
{ apply: FDC.
(*********************************)
  (* step n *)
  move=> xrn.
  pose xn := fst (fst xrn).
  pose rn := proj1_sig (snd (fst xrn)).
  pose rn_pos := proj2_sig (snd (fst xrn)).
  pose nn := snd xrn.
  have [yn] : Inhabited (Intersection (V (S nn)) (open_ball (point_set X) d xn (rn * /2))).
  { apply: dense_meets_every_nonempty_open.
    - by case: (H_od (S nn)).
    - apply: open_ball_is_open.
      exact: eps2_Rgt_R0.
    - exists xn => /=; constructor.
      rewrite /= metric_zero //.
      exact: eps2_Rgt_R0.
  }
  case/open_ball_in_open_set.
  - apply: open_intersection2; first by case: (H_od (S nn)).
    apply: open_ball_is_open.
    exact: eps2_Rgt_R0.
  - move=> rn1_t [rn1_t_pos HIbVnb].
    pose rn1 := Rmin (rn1_t/2) (rn* /2).
    have rn1_pos: rn1 > 0
      by rewrite /rn1; apply/Rmin_Rgt; split; apply: eps2_Rgt_R0.
    pose rpn1 := exist (fun r:R => r > 0) rn1 rn1_pos.
    exists (yn, rpn1, S nn).
    repeat split => /=; [ by apply: Rmin_r | | ].
    + rewrite -/rn -/xn.
      have: In (Intersection (V (S nn)) (open_ball (point_set X) d xn (rn * /2))) yn
        by apply: HIbVnb; constructor; rewrite metric_zero.
      by case => [? _ []].
    + move=>x1 In_rn1.
      have In_rn1_t : In (open_ball (point_set X) d yn rn1_t) x1.
      { constructor.
        case: In_rn1 => Hlt.
        apply: Rlt_le_trans (_ : 2 * rn1 <= _) => //.
        have rn1_le_rn1_t_half: rn1 <= rn1_t/2 by apply: Rmin_l.
        by fourier.
      }
      have: In (Intersection (V (S nn))
               (open_ball (point_set X) d xn (rn * /2))) x1
        by apply: HIbVnb.
      by case.
}
(* sequences and properties obtained so far*)
pose x_n (n : DS_set nat_DS) := fst (fst (Fn n)).
have x_n_0 : x_n 0%nat = x0
  by rewrite /x_n H_0.
pose r_n (n : nat) := proj1_sig (snd (fst (Fn n))).
have r_n_0 : r_n 0%nat = r0
  by rewrite /r_n H_0.
have r_n_pos : forall n : nat, r_n n > 0
  by move => n; apply: proj2_sig.
have r_n_r_Sn : forall n : nat, r_n (S n) <= (r_n n) * /2.
  by move=> n; case: (H_n n) => ? [].
have r_n_r_ni : forall n i : nat, r_n (n+i)%nat <= r_n n * (/2)^i.
{ move=> n.
  elim=> [| i IHi] /=; first by rewrite -plus_n_O Rmult_1_r; apply: Rle_refl.
  rewrite -plus_n_Sm.
  apply: Rle_trans (_ :  r_n (n + i)%nat * / 2 <= _) => //.
  rewrite (_ : /2 * (/2)^i = (/2)^i * /2); last by auto with real.
  rewrite -Rmult_assoc.
  apply: Rmult_le_compat_r => //.
  by auto with real.
}
have x_n_x_Sn_r_n : forall n : nat, d (x_n n) (x_n (S n)) < (r_n n) * /2
  by move=> n; case: (H_n n) => ? [? []].
have x_ni_x_nSi_r_n : forall n i : nat,
  d (x_n (n+i)%nat) (x_n (n + (S i))%nat) < (r_n n)* /2 * (/2)^i.
{ move=> n i.
  rewrite -plus_n_Sm.
  apply: Rlt_le_trans (_ : r_n (n + i)%nat * / 2 <= _) => //.
  rewrite (_ : r_n n * /2 * (/2)^i = r_n n * (/2)^i * /2); last by field.
  apply: Rmult_le_compat_r => //.
  by auto with real.
}
have x_n_x_nk: forall n : nat,
  forall k : nat, d (x_n n%nat) (x_n (n+k)%nat) <= r_n n * (1 - (/2)^k).
{ move=> n.
  elim=> [| k IHk] /=.
  - rewrite -plus_n_O metric_zero // /Rminus Rplus_opp_r Rmult_0_r.
    by auto with real.
  - apply: Rle_trans (_ : d (x_n n) (x_n (n + k)%nat)
                          + d (x_n (n + k)%nat) (x_n (n + (S k))%nat) <= _);
      first by apply: triangle_inequality.
    rewrite [x in _ <= x](_ : _ = r_n n * (1 - (/ 2) ^ k)
                                  + r_n n * / 2 * (/ 2) ^ k); last by field.
    apply: Rlt_le.
    exact: Rplus_le_lt_compat => //.
}
have HCauchy: cauchy d x_n.
{ move=> eps eps_pos.
  have [N HN]: exists N:nat, forall n:nat,
        (n >=N)%nat -> (/2)^n <= (/r0) * (/2) * eps.
  { apply: pow_inv_2_n_approach_0.
    by do !apply: Rmult_gt_0_compat => //; apply: Rinv_0_lt_compat; auto with real.
  }
  exists N.
  have Hn: forall n:nat, (n>=N)%nat -> d (x_n N) (x_n n) < r0 * ((/2)^N).
  { move=>n ngeN.
    rewrite (_ : n = (N + (n - N))%nat); last by auto with *.
    set k := (n - N)%nat.
    apply: Rle_lt_trans (_ : r_n N * (1 - (/ 2) ^ k) < _) => //.
    move: (r_n_r_ni 0%nat N) => /=.
    rewrite r_n_0.
    apply: Rlt_le_trans.
    rewrite -[x in _ < x]Rmult_1_r.
    apply: Rmult_lt_compat_l; first by apply: Rgt_lt.
    apply: Rlt_move_pr2ml.
    rewrite -[x in x < _]Rplus_0_r.
    apply: Rplus_lt_compat_l.
    by auto with real.
  }
  move=> m1 n1 m1gtN n1gtN.
  apply: Rle_lt_trans (_ : d (x_n m1) (x_n N) + d (x_n N) (x_n n1) < _);
    first by apply: triangle_inequality.
  rewrite (metric_sym _ _ d_metric).
  apply: Rlt_le_trans (_ : r0 * (/ 2) ^ N + r0 * (/ 2) ^ N <= _);
    first by apply: Rplus_lt_compat; apply: Hn.
  rewrite [x in x <= _](_ : _ = 2 * r0 * (/2)^N); last by field.
  apply: Rle_trans (_ : 2 * r0 * (/ r0 * / 2 * eps) <= _);
    first by apply: Rmult_le_compat_l; [fourier | apply: HN].
  * auto with real.
  * rewrite [x in x <= _](_ : _ = eps); first by auto with real.
    field.
    auto with real.
}
(***********************)
case: (H_cplt _ HCauchy) => xL Lim.
(***********************)
pose D := open_ball (point_set X) d xL r0.
have HopenD: open D
  by apply: open_ball_is_open.
case: (Lim D).
(* assumption. (* <-DOESN'T WORK-*)*)
- rewrite /=. (** THIS simpl REVEALS THIS open D ISN'T THAT open D**)
(*apply B_open_intro.*)
  pose F := Singleton D.
  have ->: D = FamilyUnion F.
  { apply: Extensionality_Ensembles; split; last by move => ? [? ?] [].
    move => x1 H0.
    by exists D.
  }
  constructor.
  move=> x1 [].
  by exists xL.
- constructor.
  by rewrite metric_zero.
- rewrite /= => x1 H0.
  have nn_Vnn: forall n:nat,
      snd (Fn n) = n /\ Included (open_ball (point_set X) d (x_n n) (2*(r_n n))) (V n).
  { elim=> [| n [Hn_n _]].
    - rewrite H_0 x_n_0 r_n_0; split => //.
      rewrite (_ : 2 * r0 = r0_t); last by rewrite /r0; field.
      move => z InObz.
      have: In (Intersection (V 0%nat) U) z by apply: Inc_ball_V0U.
        by case.
    - case: (H_n n) => Hn_Sn [_ [_ Hn_V]].
      split; first by rewrite Hn_Sn Hn_n.
      by rewrite Hn_Sn Hn_n in Hn_V.
  }
(************************************)
  exists xL.
  split.
  + constructor => n.
    pose D_n := open_ball (point_set X) d xL (r_n n).
    case: (Lim D_n).
    * pose F_n := Singleton D_n.
      have ->: D_n = FamilyUnion F_n.
      { apply: Extensionality_Ensembles; split; last by move => ? [? ?] [].
        move => x2 H1.
        by exists D_n.
      }
      constructor => x2 [].
      by exists xL.
    * constructor.
      rewrite metric_zero => //.
      exact: Rgt_lt.
    * rewrite /= => x2 H1.
      pose n1 := max x2 n.
      have [d_xL_xn1]: In D_n (x_n n1).
      { apply: H1.
        by apply: Max.le_max_l.
      }
      pose k1 := (n1 - n)%nat.
      have le_0_k1: le 0%nat k1.
      { rewrite (_: (0 = n - n)%nat); last by auto with *.
        apply: minus_le_compat_r.
        by apply: Max.le_max_r.
      }
      have d_xn_xn1: d (x_n n) (x_n n1) <= r_n n.
      { rewrite (_: n1 = (n + k1)%nat);
          last by apply: le_plus_minus; apply: Max.le_max_r.
        apply: Rle_trans (_ : r_n n * (1 - (/ 2) ^ k1) <= _) => //.
        rewrite -[x in _ <= x]Rmult_1_r.
        apply: Rmult_le_compat_l; first by apply: Rlt_le; apply: Rgt_lt.
        apply: Rle_move_pr2ml.
        rewrite -[x in x <= _]Rplus_0_r.
        apply: Rplus_le_compat_l.
        apply: Rlt_le.
        by auto with real.
      }
      case: (nn_Vnn n) => _ bVn.
      apply: bVn.
      constructor.
      apply: Rle_lt_trans (_ : d (x_n n) (x_n n1) + d (x_n n1) xL < _);
        first by apply: triangle_inequality.
      rewrite [d (x_n n1) xL]metric_sym //.
      rewrite (_ : 2 * r_n n = r_n n + r_n n); last by field.
      exact: Rplus_le_lt_compat.
(*****************************)
  + pose n2 := x1.
    case: (H0 n2); first by auto.
    move=> H1.
    case: (Inc_ball_V0U xL) => //.
    constructor.
    have H3: d (x_n n2) (x_n 0%nat) <= r_n 0%nat.
    { rewrite metric_sym //.
      move: (x_n_x_nk 0%nat n2).
      rewrite /= => H2.
      apply: Rle_trans (_ : r_n 0%nat * (1 - (/ 2) ^ n2) <= _) => //.
      rewrite -[x in _ <= x]Rmult_1_r.
      apply: Rmult_le_compat_l; first by apply: Rlt_le; apply: Rgt_lt.
      apply: Rle_move_pr2ml.
      rewrite -[x in x <= _]Rplus_0_r.
      apply: Rplus_le_compat_l.
      apply: Rlt_le.
      by auto with real.
    }
    rewrite r_n_0 x_n_0 in H3.
    rewrite metric_sym //.
    apply: Rle_lt_trans (_ : d xL (x_n n2) + d (x_n n2) x0 < _);
      first by apply: triangle_inequality.
    rewrite (_ : r0_t =  r0_t / 2 + r0_t / 2); last by field.
    exact: Rplus_lt_le_compat.
Qed. (* BaireCategoryTheorem *)

End BaireSpaces.


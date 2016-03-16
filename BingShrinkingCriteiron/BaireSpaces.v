(** *** The Baire Category Theorem for complete metric spaces  by  Ken'ichi Kuga ****)
(** ***************************************************************

Theorem BaireCategoryTheorem :  complete d d_metric -> baire_space. 

******************************************************************)

Require Import ssreflect ssrbool.  
Require Export MetricSpaces. 
Require Export Completeness.
Require Import ClassicalChoice.
Require Export ChoiceFacts.
Require Import EnsemblesSpec.
Require Import RationalsInReals.
Require Import Reals.
Require Import Fourier.

Open Scope R_scope.

Section BaireSpaces.

Variable X : TopologicalSpace.

(* We use the the following form of the Axiom of Choice *)
Print FunctionalDependentChoice_on.
Axiom FDC : FunctionalDependentChoice_on (point_set X * { r:R | r > 0} * nat).
Print FunctionalDependentChoice_on.

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


Lemma Rm2p: forall r1 r2 : R, r1 - r2 = r1 + -r2.
Proof. move=> r1 r2; auto. Qed.

Lemma Req_move_pr2ml: forall r1 r2 r : R, r1 = r2 + r -> r1 - r = r2.
Proof.
move=> r1 r2 r lhs. rewrite Rm2p. 
have H: r1 + -r = r2 + r + -r. 
move: lhs. auto with real.
rewrite H. 
rewrite Rplus_assoc.
rewrite Rplus_opp_r.
rewrite Rplus_0_r.
reflexivity.
Qed.

Lemma Req_move_pl2mr: forall r1 r2 r : R, r1 + r = r2 -> r1 = r2 - r.
Proof.
move=> r1 r2 r lhs.
apply eq_sym.
apply Req_move_pr2ml.
by apply eq_sym.
Qed.

Lemma Req_move_mr2pl: forall r1 r2 r : R, r1 = r2 - r -> r1 + r = r2.
Proof.
move=> r1 r2 r lhs.
rewrite Rm2p in lhs.
have H: r1 + r = r2 + -r + r.
move: lhs.
auto with real.
rewrite Rplus_assoc in H.
have H0: -r + r = 0 by auto with real.
rewrite H0 in H.
rewrite Rplus_0_r in H.
exact.
Qed.

Lemma Req_move_ml2pr: forall r1 r2 r : R, r1 - r = r2 -> r1 = r2 + r.
Proof.
move=> r1 r2 r lhs.
apply eq_sym.
apply Req_move_mr2pl.
by apply eq_sym.
Qed.

Lemma Rle_move_pr2ml: forall r1 r2 r : R, r1 <= r2 + r -> r1 - r <= r2.
Proof.
move=> r1 r2 r lhs. rewrite Rm2p. 
have H: r1 + -r <= r2 + r + -r. 
move: lhs. auto with real.
rewrite Rplus_assoc in H.
rewrite Rplus_opp_r in H.
rewrite Rplus_0_r in H. 
exact.
Qed.

Lemma Rle_move_pl2mr: forall r1 r2 r : R, r1 + r <= r2 -> r1 <= r2 - r.
Proof.
move=> r1 r2 r lhs. rewrite Rm2p.
have H: r1 + r + - r <= r2 + - r.
move: lhs. auto with real.
rewrite Rplus_assoc in H.
rewrite Rplus_opp_r in H. 
rewrite Rplus_0_r in H. 
exact.
Qed.

Lemma Rle_move_mr2pl: forall r1 r2 r : R, r1 <= r2 - r -> r1 + r <= r2.
Proof.
move=> r1 r2 r lhs. 
rewrite Rm2p in lhs.
have H: r1 + r <= r2 + -r + r.
move: lhs.
auto with real.
rewrite Rplus_assoc in H.
have H0: -r + r = 0 by auto with real.
rewrite H0 in H.
rewrite Rplus_0_r in H.
exact.
Qed.

Lemma Rle_move_ml2pr: forall r1 r2 r : R, r1 - r <= r2 -> r1 <= r2 + r.
Proof.
move=> r1 r2 r lhs. rewrite Rm2p in lhs.
have H: r1 + - r +r <= r2 +  r.
move: lhs. auto with real.
rewrite Rplus_assoc in H.
rewrite Rplus_opp_l in H. 
rewrite Rplus_0_r in H. 
exact.
Qed.

Lemma Rlt_move_pr2ml: forall r1 r2 r : R, r1 < r2 + r -> r1 - r < r2.
Proof.
move=> r1 r2 r lhs. rewrite Rm2p. 
have H: r1 + -r < r2 + r + -r. 
move: lhs. auto with real.
rewrite Rplus_assoc in H.
rewrite Rplus_opp_r in H.
rewrite Rplus_0_r in H. 
exact.
Qed.

Lemma Rlt_move_pl2mr: forall r1 r2 r : R, r1 + r < r2 -> r1 < r2 - r.
Proof.
move=> r1 r2 r lhs. rewrite Rm2p.
have H: r1 + r + - r < r2 + - r.
move: lhs. auto with real.
rewrite Rplus_assoc in H.
rewrite Rplus_opp_r in H. 
rewrite Rplus_0_r in H. 
exact.
Qed.

Lemma Rlt_move_mr2pl: forall r1 r2 r : R, r1 < r2 - r -> r1 + r < r2.
Proof.
move=> r1 r2 r lhs. 
rewrite Rm2p in lhs.
have H: r1 + r < r2 + -r + r.
move: lhs.
auto with real.
rewrite Rplus_assoc in H.
have H0: -r + r = 0 by auto with real.
rewrite H0 in H.
rewrite Rplus_0_r in H.
exact.
Qed.

Lemma Rlt_move_ml2pr: forall r1 r2 r : R, r1 - r < r2 -> r1 < r2 + r.
Proof.
move=> r1 r2 r lhs. rewrite Rm2p in lhs.
have H: r1 + - r +r < r2 +  r.
move: lhs. auto with real.
rewrite Rplus_assoc in H.
rewrite Rplus_opp_l in H. 
rewrite Rplus_0_r in H. 
exact.
Qed.

Lemma Rge_move_pr2ml: forall r1 r2 r : R, r1 >= r2 + r -> r1 - r >= r2.
Proof.
move=> r1 r2 r lhs. 
apply Rle_ge. 
apply Rge_le in lhs. 
by apply Rle_move_pl2mr. 
Qed.

Lemma Rge_move_pl2mr: forall r1 r2 r : R, r1 + r >= r2 -> r1 >= r2 - r.
Proof.
move=> r1 r2 r lhs. 
apply Rle_ge. 
apply Rge_le in lhs. 
by apply Rle_move_pr2ml. 
Qed.

Lemma Rge_move_mr2pl: forall r1 r2 r : R, r1 >= r2 - r -> r1 + r >= r2.
Proof.
move=> r1 r2 r lhs. 
apply Rle_ge. 
apply Rge_le in lhs. 
by apply Rle_move_ml2pr. 
Qed.

Lemma Rge_move_ml2pr: forall r1 r2 r : R, r1 - r >= r2 -> r1 >= r2 + r.
Proof.
move=> r1 r2 r lhs. 
apply Rle_ge. 
apply Rge_le in lhs. 
by apply Rle_move_mr2pl. 
Qed.

Lemma Rgt_move_pr2ml: forall r1 r2 r : R, r1 > r2 + r -> r1 - r > r2.
Proof.
move=> r1 r2 r lhs. 
apply Rlt_gt. 
apply Rgt_lt in lhs. 
by apply Rlt_move_pl2mr. 
Qed.

Lemma Rgt_move_pl2mr: forall r1 r2 r : R, r1 + r > r2 -> r1 > r2 - r.
Proof.
move=> r1 r2 r lhs. 
apply Rlt_gt. 
apply Rgt_lt in lhs. 
by apply Rlt_move_pr2ml. 
Qed.

Lemma Rgt_move_mr2pl: forall r1 r2 r : R, r1 > r2 - r -> r1 + r > r2.
Proof.
move=> r1 r2 r lhs. 
apply Rlt_gt. 
apply Rgt_lt in lhs. 
by apply Rlt_move_ml2pr. 
Qed.

Lemma Rgt_move_ml2pr: forall r1 r2 r : R, r1 - r > r2 -> r1 > r2 + r.
Proof.
move=> r1 r2 r lhs. 
apply Rlt_gt. 
apply Rgt_lt in lhs. 
by apply Rlt_move_mr2pl. 
Qed.

Lemma Rle_pow_inv2_1: forall n:nat, (/2)^n <= 1.
Proof.
induction n.
simpl.
by auto with *.
have H: S n = (n + 1)%nat by auto with *.
rewrite H; clear H.
have H1: (/2)^(n + 1)= (/2)^n * (/2)^1 by auto with *.
rewrite H1; clear H1.
simpl.
have H2: (/2)^n * (/2 * 1) <= 1 * (/2 * 1).
move: IHn.
apply Rmult_le_compat_r.
rewrite Rmult_1_r.
auto with *.
apply Rle_trans with (1*(/2 * 1)).
assumption.
rewrite Rmult_1_l.
rewrite Rmult_1_r.
fourier.
Qed.

(*************************************************)

Lemma Rle_n_pow_2_n: forall n:nat,  (INR n) <= (2^n).
Proof.
induction n.
simpl.
by auto with *.
have H: S n = (n + 1)%nat by auto with *.
rewrite H; clear H.
have H1: INR (n + 1)%nat = (INR n) + (INR 1) by auto with *.
rewrite H1; clear H1.
have H2: 2^(n + 1) = 2^n * 2^1 by auto with *.
rewrite H2; clear H2.
simpl.
rewrite Rmult_1_r.
have H3: INR n + 1 <= 2^n + 1 by apply Rplus_le_compat_r.
apply Rle_trans with (2^n + 1).
assumption. clear H3.
have H4: 2^n * 2 = 2^n + 2^n by field.
rewrite H4; clear H4.
apply Rplus_le_compat_l.
clear IHn.
induction n.
simpl.
by auto with *.
have H: S n = (n + 1)%nat by auto with *.
rewrite H; clear H.
have H2: 2^(n + 1) = 2^n * 2^1 by auto with *.
rewrite H2; clear H2.
simpl.
fourier.
Qed.

Lemma pow_inv_2_n_approach_0: forall eps : R, eps > 0 ->
  exists N : nat, forall n : nat, (n >= N)%nat -> (/2)^n <= eps.
Proof.
move=> eps eps_pos.
have H: exists N: nat, (N>0)%nat /\ /(INR N) < eps. 
apply inverses_of_nats_approach_0 with (eps:=eps).
assumption.
destruct H as [N].
exists N.
move=> n lenN.
destruct H.
have H1: (/2)^n <= (/2)^N.
have H2: n = ((n - N) + N)%nat by auto with *.
rewrite H2; clear H2.
have H3: (/2)^(n-N+N) = (/2)^(n-N)*(/2)^N by auto with *.
rewrite H3; clear H3.
have H4: (/2)^(n-N) <= 1.
auto with *.
set k:= (n - N)%nat.
induction k.
simpl.
by auto with *.
have H5: S k = (k + 1)%nat by auto with *.
rewrite H5; clear H5.
have H6: (/2)^(k+1) = (/2)^k*(/2)^1 by auto with *.
rewrite H6; clear H6.
simpl.
have H7: (/2)^k*(/2) <= 1*(/2).
apply Rmult_le_compat_r.
by auto with *.
assumption.
rewrite Rmult_1_r.
rewrite Rmult_1_l in H7.
apply Rle_trans with (/2).
assumption.
fourier.
have H8: (/2)^(n-N)*(/2)^N <= 1* (/2)^N.
apply Rmult_le_compat_r.
have H9: 0 < (/2)^N by auto with real.
move: H9.
by auto with *.
assumption.
rewrite Rmult_1_l in H8.
move: H8.
by auto with *.
have H10: (/2)^N <= /(INR N).
have H11: (/2)^N = /(2^N).
apply eq_sym.
apply Rinv_pow.
pose proof Rlt_R0_R2 as H12.
move:H12.
auto with *.
clear H11.
apply Rle_trans with ((/2)^N).
auto with *.
have H13: /(2^N) = (/2)^N.
apply Rinv_pow.
pose proof Rlt_R0_R2 as H14.
move:H14.
auto with *.
rewrite <- H13.
apply Rle_Rinv.
move: H.
by auto with *.
by auto with *.
apply Rle_n_pow_2_n.
apply Rle_trans with ((/2)^N).
assumption.
apply Rle_trans with (/ INR N).
assumption.
move:H0.
by auto with *.
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
  by apply: intro_open_ball.
have H_ON_oball : open_neighborhood (open_ball (point_set X) d x r) x.
apply:  (open_neighborhood_basis_elements (metric_topology_neighborhood_basis d x) x).
by apply: d_metrizes.
assumption.
by destruct H_ON_oball.
Qed.

Lemma open_ball_in_open_set:
  forall (x : point_set X) (U : Ensemble (point_set X)),
    open U -> In U x  -> 
    exists r : R, r > 0 /\ 
      Included (open_ball (point_set X) d x r) U. 
Proof.
move=> x U open_U In_U_x.
have Hoball: exists oball : Ensemble (point_set X),
        In (metric_topology_neighborhood_basis d x ) oball /\
        Included oball U.
apply: (open_neighborhood_basis_cond
         (metric_topology_neighborhood_basis d x) x (d_metrizes x)).
red; split. 
assumption.
assumption.
destruct Hoball as [oball H_oball].
destruct H_oball as [HmNb HbInU].
destruct HmNb as [r H_rpos].
exists r.
by move: H_rpos HbInU.
Qed.

Definition closed_ball (x0 : point_set X) (r : R):
  Ensemble (point_set X):=
     fun (x : point_set X)  => d x0 x <= r.

Lemma closed_ball_is_closed :
  forall (x0: point_set X) (r: R), closed (closed_ball x0 r). 
Proof. 
move=> x0 r0.
red.
set cover := fun (xd: { x: point_set X | d x0 x > r0 }%type) =>
  open_ball (point_set X) d (proj1_sig xd) (d x0 (proj1_sig xd) - r0).  
have cplmt_as_union:
  Complement (closed_ball x0 r0) = IndexedUnion cover.
apply: Extensionality_Ensembles; red; split.
red. 
move=> x In_C_c_x.
have cplmt_x : ~ In (closed_ball x0 r0) x.
by apply: In_C_c_x.
have not_dx0x_le_r0: d x0 x <= r0 -> False.
have Hcb: d x0 x <= r0 -> (closed_ball x0 r0) x by auto.
have Hncb: (closed_ball x0 r0) x -> False by apply: cplmt_x.
move: Hcb Hncb; tauto.
have dx0x_gt_r0 : d x0 x > r0 by apply: Rnot_le_gt.
clear In_C_c_x cplmt_x not_dx0x_le_r0.
have xd_exists : 
  exists xd : { x: point_set X | d x0 x > r0 }, proj1_sig xd = x.
exists (exist (fun y : point_set X => d x0 y > r0) x dx0x_gt_r0).
auto. 
destruct xd_exists as [xd].
have cx : In (cover xd) x.
constructor.
rewrite H.
rewrite metric_zero.
apply: Rlt_move_pl2mr.
apply: Rgt_lt.
rewrite Rplus_0_l.
exact.
assumption.
apply (indexed_union_intro cover xd).  
exact.
red.
move=> x InIndUx.
destruct InIndUx.
destruct H.
have H1 : d x0 (proj1_sig a) > r0.
apply (proj2_sig a). 
have Ht: d x0 x >= (d x0 (proj1_sig a)) - (d (proj1_sig a) x).
have h_tmp: d (proj1_sig a) x = d x (proj1_sig a) by apply metric_sym.
rewrite h_tmp. clear h_tmp.
apply: Rge_move_pl2mr.
apply Rle_ge.
apply triangle_inequality.
assumption.
apply Rlt_move_mr2pl in H.
rewrite Rplus_comm in H.
apply Rlt_move_pl2mr in H.
apply Rlt_gt in H. 
have H2: d x0 x > r0.
apply Rge_gt_trans with (r2:= d x0 (proj1_sig a) - d (proj1_sig a) x).
exact.
exact.
red.
red.
red.
move=> InCbx.
destruct InCbx.
apply Rgt_not_le in H2.
apply Rlt_le in H0.
move: H0 H2.
tauto.
apply Rgt_not_le in H2.
apply Req_le in H0.
move: H0 H2.
tauto.
have HoU: open (IndexedUnion cover).
Print IndexedUnion.
SearchAbout IndexedUnion.
apply open_indexed_union.
move=>xd.
apply: open_ball_is_open.
apply Rgt_move_pr2ml.
rewrite Rplus_0_l.
apply (proj2_sig xd).
rewrite cplmt_as_union.
exact.
Qed.
Print complete.

(* The Baire Category Theorem for complete metric spaces *)

Theorem BaireCategoryTheorem :  complete d d_metric -> baire_space.
 
Proof.
move=> H_cplt.
rewrite/baire_space /dense.
move=> V H_od. 
apply: Extensionality_Ensembles; split; red; intros.
exact.
apply: meets_every_open_neighborhood_impl_closure.
move=> U H_opn_U H_In_U_x.
set (IStep (xrn0 xrn1: point_set X * { r:R | r > 0} * nat) := 
  snd xrn1 = S (snd xrn0) /\ 
  proj1_sig (snd (fst xrn1)) <= (proj1_sig (snd (fst xrn0))) * /2 /\
  d (fst (fst xrn0)) (fst (fst xrn1)) < (proj1_sig (snd (fst xrn0))) * /2 /\
  Included 
    (open_ball _ d (fst (fst xrn1)) (2*proj1_sig (snd (fst xrn1))))
    (V (snd xrn1))).
(* step 0 *) 
have H_V0U : Inhabited (Intersection (V 0%nat) U). 
apply: dense_meets_every_nonempty_open.
move: (H_od 0%nat).
tauto.
assumption.
move: H_In_U_x.
by apply Inhabited_intro.
destruct H_V0U as [x0 H_V0U].
apply (open_ball_in_open_set x0 (Intersection (V 0%nat) U)) in H_V0U.
destruct H_V0U as [r0_t HrI].
destruct HrI as [r0_t_pos Inc_ball_V0U].
set r0:=r0_t/2.
have r0_pos: r0>0.
rewrite/r0.
fourier.
set rp0 := exist (fun r:R => r>0)r0 r0_pos.
(**** Axiom of Choice used *******)
have CFun: exists Fn : nat -> point_set X * { r:R | r>0 } * nat,
 (Fn 0%nat) = (pair (pair x0 rp0) 0%nat) /\
 (forall n : nat, (IStep (Fn n) (Fn (S n)))).
apply: FDC.
(*********************************)
(* step n *)
move=> xrn.
set xn := fst (fst xrn).
set rn := proj1_sig (snd (fst xrn)).
set rn_pos := proj2_sig (snd (fst xrn)).
set nn := snd xrn.
have H_Vn1B : Inhabited (Intersection (V (S nn)) (open_ball (point_set X) d xn (rn * /2))).  
apply: dense_meets_every_nonempty_open.
move: (H_od (S nn)).
tauto.
apply: open_ball_is_open.
apply : eps2_Rgt_R0.
by apply: rn_pos.
exists xn.
red.
constructor.
rewrite metric_zero.
apply: Rgt_lt.
apply: eps2_Rgt_R0.
by apply: rn_pos.
assumption.  
destruct H_Vn1B as [yn H_In_Int_yn].
apply (open_ball_in_open_set yn) in H_In_Int_yn.
destruct H_In_Int_yn as [rn1_t HVSnyn].
destruct HVSnyn as [rn1_t_pos HIbVnb].
set (rn1 := Rmin (rn1_t/2) (rn* /2)).
have rn1_pos: rn1 > 0.
rewrite/rn1.
apply/Rmin_Rgt; split.
fourier.
apply: eps2_Rgt_R0.
by apply: rn_pos.
set rpn1 := (exist (fun r:R => r > 0) rn1 rn1_pos).
exists (pair (pair yn rpn1) (S nn)).
rewrite/IStep.
split.
simpl.
rewrite/nn.
reflexivity.
split.
simpl.
have Hrn: proj1_sig (snd (fst xrn)) = rn by auto.
rewrite Hrn.
rewrite/ rn1.
by apply: Rmin_r.
split.
simpl.
have Hrn: proj1_sig (snd (fst xrn)) = rn by auto.
rewrite Hrn.
have Hxn: (fst (fst xrn)) = xn by auto.
rewrite Hxn.
have HynInInt: In (Intersection (V (S nn)) (open_ball (point_set X) d xn (rn * /2))) yn.
apply: HIbVnb.
constructor.
rewrite metric_zero.
by apply: rn1_t_pos.
assumption.
destruct HynInInt as [yn HVSnyn Hbxnyn].
destruct Hbxnyn.
exact.
simpl.
red.
move=>x1 In_rn1.
have In_rn1_t : In (open_ball (point_set X) d yn rn1_t) x1.
red.
constructor.
destruct In_rn1.
have rn1_le_rn1_t_half: rn1 <= rn1_t/2.
rewrite/rn1.
by apply: Rmin_l.
have : 2* rn1 <= rn1_t  by fourier.
move: H0.
by apply: Rlt_le_trans. 
have In_Vb : In (Intersection (V (S nn))
                   (open_ball (point_set X) d xn (rn * /2))) x1
by apply: HIbVnb.
destruct In_Vb.
assumption.
apply: open_intersection2.
move: (H_od (S nn)).
tauto.
apply: open_ball_is_open.
apply: eps2_Rgt_R0.
exact.
destruct CFun as [Fn H_I].
destruct H_I as [H_0 H_n]. 
(* sequences and properties obtained so far*)
set (x_n (n : DS_set nat_DS) := fst (fst (Fn n))).
have x_n_0 : x_n 0%nat = x0.
have h_tmp: x_n 0%nat = fst (fst (Fn 0%nat)) by auto.
rewrite h_tmp; clear h_tmp.
rewrite H_0.
auto.
set (r_n (n : nat) := proj1_sig (snd (fst (Fn n)))).
have r_n_0 : r_n 0%nat = r0.
have h_tmp: r_n 0%nat = proj1_sig (snd (fst (Fn 0%nat))) by auto.
rewrite h_tmp; clear h_tmp.
rewrite H_0.
auto.
have r_n_pos : forall n : nat, r_n n > 0.
move=>n.
pose proof (proj2_sig (snd (fst (Fn n)))).
simpl in H0.
have h_tmp: (r_n n) = proj1_sig (snd (fst (Fn n))) by auto.
by rewrite h_tmp; clear h_tmp.
have r_n_r_Sn : forall n : nat, r_n (S n) <= (r_n n)* /2.
move=> n.
pose proof (H_n n).
destruct H0.
destruct H1.
have h_tmp: r_n (S n) = proj1_sig (snd (fst (Fn (S n)))) by auto.
rewrite h_tmp; clear h_tmp.
have h_tmp: r_n n = proj1_sig (snd (fst (Fn n))) by auto.
rewrite h_tmp; clear h_tmp.
assumption.
have r_n_r_ni : forall n i : nat, r_n (n+i)%nat <= r_n n * (/2)^i.
move=> n.
induction i.
simpl.
have h_tmp: (n + O)%nat = n by auto.
rewrite h_tmp; clear h_tmp.
have h_tmp: r_n n * 1 = r_n n by auto with real.
rewrite h_tmp; clear h_tmp.
auto with real.
simpl.
have h_tmp: (n + S i)%nat = S (n + i) by auto.
rewrite h_tmp; clear h_tmp.
have h_trans: 
   r_n (S (n + i)) <= r_n (n + i)%nat * /2
->  r_n (n + i)%nat * /2   <= r_n n * (/ 2 * (/ 2) ^ i)
 ->  r_n (S (n + i)) <= r_n n * (/ 2 * (/ 2) ^ i) by apply Rle_trans.
apply h_trans; clear h_trans.
apply: r_n_r_Sn. 
have h_tmp: r_n n * (/2 * (/2)^i) = r_n n * (/2)^i * (/2).
have h_tmp1: /2 * (/2)^i = (/2)^i * /2 by auto with real. 
rewrite h_tmp1; clear h_tmp1.
auto with real.
rewrite h_tmp; clear h_tmp.
move: IHi.
apply: Rmult_le_compat_r.
auto with real.
have x_n_x_Sn_r_n : forall n : nat,
  d (x_n n) (x_n (S n)) < (r_n n) * /2. 
move=>n.
pose proof (H_n n) as H_In. 
destruct H_In as [_ H_In].
destruct H_In as [_ H_In].
have h_tmp: r_n n = proj1_sig (snd (fst (Fn n))) by auto.
rewrite h_tmp; clear h_tmp.
have h_tmp: x_n n = fst (fst (Fn n)) by auto.
rewrite h_tmp; clear h_tmp.
have h_tmp: x_n (S n) = fst (fst (Fn (S n))) by auto.
rewrite h_tmp; clear h_tmp.
move: H_In.
tauto. 
have x_ni_x_nSi_r_n :
forall n i : nat, 
  d (x_n (n+i)%nat) (x_n (n + (S i))%nat) < (r_n n)* /2 * (/2)^i.
move=>n i.
have h_trans:
  d (x_n (n+i)%nat) (x_n (n + (S i))%nat) < r_n (n+i)%nat * /2 
->
 r_n (n+i)%nat * /2 <= (r_n n)* /2 * (/2)^i
->
 d (x_n (n+i)%nat) (x_n (n + (S i))%nat) < (r_n n)* /2 * (/2)^i
by apply:Rlt_le_trans.
apply h_trans; clear h_trans.
have h_tmp: (n + S i)%nat = S (n + i)%nat by auto with real. 
rewrite h_tmp; clear h_tmp.
apply: x_n_x_Sn_r_n.
have h_tmp: r_n n * /2 * (/2)^i = r_n n * (/2)^i * /2 by field.
rewrite h_tmp; clear h_tmp.
have h_tmp: r_n (n + i)%nat  <= r_n n * (/ 2) ^ i by apply: r_n_r_ni.
move:h_tmp.
apply: Rmult_le_compat_r.
by auto with real.
have x_n_x_nk: forall n : nat, 
           forall k : nat, d (x_n n%nat) (x_n (n+k)%nat) <= r_n n * (1 - (/2)^k). 
move=>n.
induction k.
simpl.
have tmp: (n + 0)%nat = n by auto.
rewrite tmp. clear tmp.
rewrite metric_zero.
have tmp: 1 - 1 = 0.
rewrite Rm2p.
auto with real.
rewrite tmp.
rewrite Rmult_0_r.
by auto with real.
assumption.  
have tri : d (x_n n) (x_n (n + (S k))%nat) <= 
            d (x_n n) (x_n (n + k)%nat) + d (x_n (n + k)%nat) (x_n (n + (S k))%nat).
apply triangle_inequality.
assumption.
have tmp:  d (x_n n) (x_n (n + k)%nat) + d (x_n (n + k)%nat) (x_n (n + (S k))%nat) <=
                  r_n n * (1 - (/2)^k) + d (x_n (n + k)%nat) (x_n (n + (S k))%nat).
apply Rplus_le_compat_r.
by apply IHk.
have tri2: d (x_n n) (x_n (n + (S k))%nat) <= 
      r_n n * (1 - (/2)^k) + d (x_n (n + k)%nat) (x_n (n + (S k))%nat).
apply Rle_trans with
  (r2:= d (x_n n) (x_n (n + k)%nat) + d (x_n (n + k)%nat) (x_n (n + (S k))%nat)).
apply tri.
apply tmp.
clear tri tmp.
have tmp : d (x_n (n + k)%nat) (x_n (n + S k)%nat) < r_n n * /2 * (/2)^k by apply x_ni_x_nSi_r_n.
have tmp1 :  r_n n * (1 - (/ 2) ^ k) + d (x_n (n + k)%nat) (x_n (n + S k)%nat) <
                       r_n n * (1 - (/ 2) ^ k) + r_n n * /2 * (/2)^k.
apply Rplus_lt_compat_l.
by apply tmp.
have tmp2 : d (x_n n) (x_n (n + S k)%nat) < r_n n * (1 - (/ 2) ^ k) + r_n n * / 2 * (/ 2) ^ k.
apply Rle_lt_trans with (r2 :=r_n n * (1 - (/ 2) ^ k) + d (x_n (n + k)%nat) (x_n (n + S k)%nat) ).
apply tri2.
by apply tmp1.
have ineq : r_n n * (1 - (/ 2) ^ k) + r_n n * / 2 * (/ 2) ^ k 
          <=  r_n n * (1 - (/ 2) ^ S k).
have tmp3:  r_n n * (1 - (/ 2) ^ k) + r_n n * / 2 * (/ 2) ^ k 
  = r_n n * ((1 - (/ 2) ^ k) +  / 2 * (/ 2) ^ k). 
SearchAbout Rmult.  rewrite  Rmult_plus_distr_l.
have tmp4: r_n n * (/2 * (/2)^k) = r_n n * /2 *(/2)^k.
rewrite Rmult_assoc.
reflexivity.
rewrite tmp4.
reflexivity.
rewrite tmp3.
apply Rmult_le_compat_l.
have tmp5: 0 < r_n n.
apply Rgt_lt.
by apply r_n_pos. 
move: tmp5.
apply Rlt_le.
clear tmp tmp1 tmp2 tmp3.
apply Rle_move_mr2pl.
apply Rle_move_pr2ml.
have tmp:
  0 <=  0 - (/ 2) ^ S k - / 2 * (/ 2) ^ k + (/ 2) ^ k ->
  1+0 <=  1 + (0 - (/ 2) ^ S k - / 2 * (/ 2) ^ k + (/ 2) ^ k) 
                                   by apply Rplus_le_compat_l.
have tmp1: 1 + 0 = 1 by apply Rplus_0_r.
rewrite tmp1 in tmp. clear tmp1.
have tmp2: 1 + (0 - (/ 2) ^ S k - / 2 * (/ 2) ^ k + (/ 2) ^ k)
    = 1  - (/ 2) ^ S k - / 2 * (/ 2) ^ k + (/ 2) ^ k.
field.
rewrite tmp2 in tmp.
apply tmp.
clear tmp tmp2.
have tmp3 : 0  - (/ 2) ^ S k - / 2 * (/ 2) ^ k + (/ 2) ^ k
 =  - (/ 2) ^ S k - / 2 * (/ 2) ^ k + (/ 2) ^ k.
field. rewrite tmp3. clear tmp3.
have tmp4: (/2)^S k = /2* (/2)^k by auto.
rewrite tmp4. clear tmp4.
have tmp3 : - (/ 2 * (/2)^k) - / 2 * (/ 2) ^ k + (/ 2) ^ k
 = (- /2 -/2 +1) * (/ 2) ^ k.
field.
rewrite tmp3. clear tmp3.
have tmp4: -/2 -/2 +1 = 0 by field.
rewrite tmp4. 
rewrite Rmult_0_l.
by auto with real.
have Ineq: d (x_n n) (x_n (n + S k)%nat) < r_n n * (1 - (/ 2) ^ S k).
apply Rlt_le_trans with (r2:= r_n n * (1 - (/ 2) ^ k) + r_n n * / 2 * (/ 2) ^ k).
exact.
exact.
move: Ineq.
by apply Rlt_le.

(*********************************)
Print Inhabited_intro.
Print cauchy.
have HCauchy: cauchy  d x_n. 
red.
move=> eps eps_pos.
have HN: exists N:nat, forall n:nat, 
      (n >=N)%nat -> (/2)^n <= (/r0) * (/2) * eps.  
apply pow_inv_2_n_approach_0 with (eps:= (/r0) * (/2) * eps).
apply Rmult_gt_0_compat.
apply Rmult_gt_0_compat.
apply Rlt_gt.
apply Rinv_0_lt_compat.
assumption.
auto with *.
assumption.
destruct HN as [N HN].
exists N.
have Hn: forall n:nat, (n>=N)%nat -> d (x_n N) (x_n n) < r0 * ((/2)^N).
move=>n ngeN.
have tmp: n=(N+(n-N))%nat by auto with *.
rewrite tmp; clear tmp.
set k:= (n-N)%nat.
have Hk: d(x_n N) (x_n (N+k)%nat) <= r_n N * (1-(/2)^k).
apply x_n_x_nk.
have HrN : r_n (0+N)%nat <= (r_n 0%nat) * (/2)^N  by apply r_n_r_ni. 
simpl in HrN.
rewrite r_n_0 in HrN.
have HrN1: r_n N * (1 - (/2)^k) <= r0 * (/2)^N * (1-(/2)^k).
move: HrN.
apply Rmult_le_compat_r.
apply Rle_move_pl2mr.
rewrite Rplus_0_l. 
by apply Rle_pow_inv2_1.
have HrNk: d(x_n N) (x_n (N+k)%nat) <= r0 * (/2)^N * (1 - (/2)^k).
apply Rle_trans with (r_n N * (1 - (/2)^k)).
assumption.
assumption.
clear Hk HrN HrN1.
have HrN2: r0 * (/2)^N * (1 - (/2)^k) < r0 * (/2)^N.
have tmp3: r0 * (/2)^N = r0 * (/2)^N * 1 by auto with *. 
rewrite {2} tmp3. clear tmp3.
apply Rmult_lt_compat_l.
have tmp4: 0 < r0.
by apply Rgt_lt.
have tmp5: 0< (/2)^N by auto with *.
move: tmp4 tmp5.
by apply Rmult_lt_0_compat.
apply Rlt_move_pr2ml.
rewrite Rplus_comm.
apply Rlt_move_ml2pr.
have tmp7: 1-1 = 0 by auto with *.
rewrite tmp7; clear tmp7.
by auto with *.
apply Rle_lt_trans with (r0 * (/ 2) ^ N * (1 - (/ 2) ^ k)).
assumption.
assumption.
move=>m1 n1 m1gtN n1gtN.
have Tri: d (x_n m1) (x_n n1) <= d (x_n m1) (x_n N) + d (x_n N) (x_n n1) by apply triangle_inequality. 
have Hdm1: d (x_n m1) (x_n N) < r0 * (/2)^N.
rewrite metric_sym.
apply Hn.
assumption.
assumption.
have Hdn1: d (x_n N) (x_n n1) < r0 * (/2)^N.
apply Hn.
assumption.
have Hsum: d (x_n m1) (x_n N) + d (x_n N) (x_n n1) < r0 * (/2)^N + r0 * (/2)^N.
apply Rplus_lt_compat.
assumption.
assumption.
have Hs : r0 * (/2)^N + r0 * (/2)^N = 2 * r0 * (/2)^N. 
field.
rewrite Hs in Hsum; clear Hs.
clear Hdm1 Hdn1.
have Htr: d (x_n m1) (x_n n1) < 2 * r0 * (/2)^N.
apply Rle_lt_trans with (d (x_n m1) (x_n N) + d (x_n N) (x_n n1)).
assumption.
assumption.
have Htr2: (/2)^N <= / r0 * /2 * eps by apply HN.
have Htr3: 2 * r0 * (/2)^N <= 2 * r0 * /r0 * /2 * eps.
have tmp4: 2 * r0 * /r0 * /2 * eps = 2 * r0 * (/r0 * /2 * eps).
field.
move: (r0_pos). 
auto with *.
rewrite tmp4; clear tmp4.
apply Rmult_le_compat_l with (r:= 2 * r0).
have r0pos: 0 <= r0.
apply Rge_le.
move: (r0_pos).
auto with *.
move: r0pos.
have tmp: 0 = 2 * 0 by auto with *.
rewrite {2} tmp.
auto with *.
assumption.
clear Htr2.
apply Rlt_le_trans with (2 * r0 * (/ 2) ^ N).
assumption.
have HNeps: (/2)^N <= / r0 * /2 * eps.
apply HN. 
auto with *.
have HNeps2: (2 * r0) * (/2)^N <= (2 * r0) * (/r0 * /2 * eps).
move: HNeps.
apply Rmult_le_compat_l with (r:= 2 * r0).
have r0pos: 0 <= r0.
apply Rge_le.
move: (r0_pos).
auto with *.
move: r0pos.
have tmp: 0 = 2 * 0 by auto with *.
rewrite {2} tmp.
auto with *.
have Hre: 2 * r0 * /r0 */2 * eps = eps. 
have Hre1: 2 * /2 * eps = eps.
have tmp: 2* /2 = 1 by field.
have tmp2: r0 * /r0 = 1.
field.
move: (r0_pos).
auto with *.
rewrite tmp.
rewrite Rmult_1_l.
reflexivity.
have tmp3: 2 * r0 * /r0 = 2 * (r0 * /r0).
field.
move: (r0_pos).
auto with *.
rewrite tmp3.
have tmp4: r0 * /r0 = 1.
auto with *.
rewrite tmp4.
clear tmp3 tmp4.
have tmp5: 2*1 = 2 by field.
rewrite tmp5.
assumption.
have tmp5: 2 * r0 * (/r0 * /2 * eps) = 2 * r0* /r0* /2 * eps.
field.
move: (r0_pos).
by auto with *.
rewrite tmp5 in HNeps2.
rewrite Hre in HNeps2.
assumption.
(************************)
destruct (H_cplt x_n) as [xL Lim].
assumption.
(***********************)
set D:= open_ball (point_set X) d xL r0.
have HopenD: open D.
(* simpl--DOES NOTHING HERE...BUT *)
apply open_ball_is_open.
assumption.
destruct (Lim D).
(* assumption. (* <-DESN'T WORK-*)*)
simpl. (** THIS simpl REVEALS THIS open D ISN'T THAT open D**)
Print B_open.
(*apply B_open_intro.*)
Print IndexedFamily.
Print Singleton.
set F:= Singleton D.
Check F.
have FD: D=FamilyUnion F.
apply Extensionality_Ensembles; red; split.
red. intros.
Print FamilyUnion.
apply (family_union_intro F D).
Print Singleton.
apply In_singleton.
assumption.  
red.
intros.
destruct H0.
SearchAbout Singleton.
have tmp: D = S by apply Singleton_inv. 
rewrite tmp; clear tmp.
assumption.
rewrite FD.
apply (B_open_intro (point_set X) ).
red.
intros. 
have temp2: D=x1 by apply Singleton_inv.
apply eq_sym in temp2.
rewrite temp2.
rewrite temp2 in H0.
apply indexed_union_intro with xL.
red.
constructor.
assumption.
constructor.
rewrite metric_zero.
assumption. 
assumption.
have nn_Vnn: forall n:nat, 
  snd (Fn n) = n /\ Included (open_ball (point_set X) d (x_n n) (2*(r_n n))) (V n).
induction n.
split.
by rewrite H_0.
rewrite x_n_0.
rewrite r_n_0.
have temp: 2*r0 = r0_t.
rewrite/r0.
field.
rewrite temp; clear temp.
red.
move=>z InObz.
have InV0Uz : In (Intersection (V 0%nat) U) z.
apply: Inc_ball_V0U.
assumption.
destruct InV0Uz.
assumption.
pose proof (H_n n).
destruct H1 as [Hn_Sn Hn_V].
destruct Hn_V as [_ Hn_V].
destruct Hn_V as [_ Hn_V].
destruct IHn as [Hn_n _]. 
split.
rewrite Hn_Sn.
rewrite Hn_n.
reflexivity.
rewrite/x_n /r_n.
rewrite Hn_Sn in Hn_V.
rewrite Hn_n in Hn_V.
assumption.
(************************************)
apply Inhabited_intro with xL.
split.
apply indexed_intersection_intro.
move=>n.
simpl in H0.
simpl in x1.

set D_n:= open_ball (point_set X) d xL (r_n n).
destruct (Lim D_n).
set F_n:= Singleton D_n.
have FD_n: D_n=FamilyUnion F_n.
apply Extensionality_Ensembles; red; split.
red. intros.
apply (family_union_intro F_n D_n).
apply In_singleton.
assumption.  
red.
intros.
destruct H1.
have tmp: D_n = S by apply Singleton_inv. 
rewrite tmp; clear tmp.
assumption.
rewrite FD_n.
apply (B_open_intro (point_set X) ).
red.
intros. 
have temp2: D_n=x2 by apply Singleton_inv.
apply eq_sym in temp2.
rewrite temp2.
rewrite temp2 in H1.
apply indexed_union_intro with xL.
red.
constructor.
by apply r_n_pos.
constructor.
rewrite metric_zero.
move: (r_n_pos n).
by auto with *.
assumption. 
simpl in H1.
simpl in x2.
set n1:= max x2 n.
have Dnn1: In D_n (x_n n1).
apply H1.
rewrite/n1.
by apply Max.le_max_l.
destruct Dnn1 as [d_xL_xn1].
set k1:= (n1 - n)%nat.
have le_0_k1: le 0%nat k1.
rewrite/k1.
have tmp0: (0 = n - n)%nat by auto with *. 
rewrite tmp0; clear tmp0.
apply minus_le_compat_r. 
rewrite/n1. 
by apply Max.le_max_r.
have d_xn_xn1: d (x_n n) (x_n n1) <= r_n n. 
have tmpk: n1 = (n + k1)%nat.
rewrite/k1.
apply le_plus_minus.
rewrite/n1.
by apply Max.le_max_r.
rewrite tmpk.
apply Rle_trans with (r_n n * (1-(/2)^k1)).
by apply x_n_x_nk.
have tmp3: 1-(/2)^k1 <= 1.
apply Rle_move_pr2ml.
have tmp4: 1 = 1 + 0 by auto with real.
rewrite {1} tmp4; clear tmp4.
apply Rplus_le_compat_l.
have: 0<(/2)^k1 by auto with real.
by auto with real.
have tmp5: r_n n = (r_n n)*1 by auto with real.
rewrite {2} tmp5; clear tmp5.
move: tmp3.
apply Rmult_le_compat_l.
have tmp2: (n + (n1 - n) = (n1 - n)+ n)%nat by ring.
(*rewrite tmp2; clear tmp2.*)
move:(r0_pos).
by auto with *.
rewrite metric_sym in d_xn_xn1.
have d_xn_xL: d xL (x_n n) < 2*r_n n.
have triang : d xL (x_n n) <= d xL (x_n n1) + d (x_n n1) (x_n n) by apply triangle_inequality.
have tmp6: d xL (x_n n1) + d (x_n n1) (x_n n) <= d xL (x_n n1) + r_n n.
apply Rplus_le_compat_l.
assumption.
have tmp7: d xL (x_n n1) + r_n n < r_n n + r_n n.
apply Rplus_lt_compat_r.
assumption. 
have tmp8: 2*r_n n = r_n n + r_n n by field. 
rewrite tmp8; clear tmp8.
apply Rle_lt_trans with (d xL (x_n n1) + d (x_n n1) (x_n n)).
assumption.
apply Rle_lt_trans with (d xL (x_n n1) + r_n n).
assumption.
assumption.
rewrite metric_sym in d_xn_xL.
destruct (nn_Vnn n) as [_ bVn].
red in bVn.
apply bVn.
constructor.
assumption.
assumption.
assumption.
(*****************************)
simpl in H0.
simpl in x1.
set n2:= x1.
destruct (H0 n2).
rewrite/n2. 
by auto.
have H3: d (x_n n2) (x_n 0%nat) <= r_n 0%nat.
apply Rle_trans with ((r_n 0%nat) * (1-(/2)^n2)).
rewrite metric_sym.
have tmp9: n2 = (0 + n2)%nat by auto with real. 
rewrite tmp9; clear tmp9.
by apply x_n_x_nk.
assumption.
have tmp10: r_n 0%nat = (r_n 0%nat)*1 by auto with *.
rewrite {2} tmp10; clear tmp10.
apply Rmult_le_compat_l. 
move:(r0_pos).
rewrite r_n_0.
by auto with *.
apply Rle_move_pr2ml.
have tmp11 : 1=1+0 by auto with real.
rewrite {1} tmp11; clear tmp11.
apply Rplus_le_compat_l with (r:=1).
have : 0 < (/2)^n2 by auto with real.
by auto with real.
rewrite r_n_0 in H3.
rewrite x_n_0 in H3.
have d_x0_xL: d x0 xL < r0_t.
rewrite metric_sym.
apply Rle_lt_trans with (d xL (x_n n2) + d (x_n n2) x0).
apply triangle_inequality.
assumption.
apply Rlt_le_trans with (r0 + d (x_n n2) x0).
apply Rplus_lt_compat_r.
assumption.
have tmp12: r0_t = r0 + r0.
rewrite/r0.
rewrite/Rdiv.
SearchAbout Rmult.
rewrite -Rmult_plus_distr_r.
field.
rewrite tmp12; clear tmp12.
apply Rplus_le_compat_l.
assumption.
assumption.
red in Inc_ball_V0U.
have Inball: In (open_ball (point_set X) d x0 r0_t) xL.
constructor.
by apply d_x0_xL.
have InV0U: In (Intersection (V 0%nat) U) xL.
apply Inc_ball_V0U.
by apply Inball.
destruct InV0U.
assumption.
(**********************)
apply open_intersection2.
destruct (H_od 0%nat).
assumption.
assumption.
Qed. (* BaireCategoryTheorem *)

End BaireSpaces.


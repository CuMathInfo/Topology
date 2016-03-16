(** LemmasForBSC.v by Ken'ichi Kuga *)
(** Lemmas for BingShrinkingCriterion.v **)

From mathcomp
Require Import ssreflect ssrbool.
Require Import ClassicalChoice.
Require Import FunctionalExtensionality.
Require Import Fourier.
From Topology
Require Import MetricSpaces Compactness Completeness SubspaceTopology.
From Topology
Require Import WeakTopology RationalsInReals Subbases.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Open Scope R_scope.

Section UnifCompact. 

Variables X Y:Type.
Variables (d:X->X->R) (d':Y->Y->R).
Hypotheses (d_metric: metric d) (d'_metric: metric d').
Let Xt := MetricTopology d d_metric.
Let Yt := MetricTopology d' d'_metric.
Variable f : point_set Xt -> point_set Yt.
Hypothesis h_f_conti : continuous f.
Hypotheses X_compact: compact Xt. (* Y_compact: compact Yt.*)

Definition RR (eps: R) (n:nat) (xx: X*X):Prop :=
    d (fst xx) (snd xx) < / INR (S n) /\ 
    d' (f (fst xx)) (f (snd xx)) >= eps. 

Definition Mtemp2 (eps: R) : Prop := (*Better to Rename*)
forall delta : R, delta > 0 -> exists x1 x2 : X,
      d x1 x2 < delta /\ d' (f x1) (f x2) >= eps.
      
Lemma Mtemp1 (eps: R) (n : nat): (*Better to Rename*)
           Mtemp2 eps -> exists y : X * X, RR eps n y.
Proof.
have ISn_pos: (/ INR (S n)) > 0. 
 by apply /Rinv_0_lt_compat /lt_0_INR /lt_0_Sn.
move=> h_d.
 case: (h_d (/ INR (S n)) ISn_pos) => x1 {ISn_pos}.
 case=> x2 [h_dxx h_d'ff]; exists (x1,x2).
 by apply: conj.
Qed.

Lemma exists_xx (eps :R) : 
     Mtemp2 eps -> exists choice_xx: nat -> X*X, 
                 forall n:nat, RR eps n (choice_xx n).
Proof. by move=> h_d; apply: choice=> n; apply: Mtemp1. Qed.

Lemma OBu (delta1 : R) (x_0 : point_set Xt) :
open_ball (point_set Xt) d x_0 (delta1 * /2) = FamilyUnion (Singleton (open_ball (point_set Xt) d x_0 (delta1 * /2))).
Proof.
 apply: Extensionality_Ensembles; apply: conj => x H.
 apply: (family_union_intro (Singleton _) _ x).
 by apply: In_singleton.
 by [].
 case: H => {x} S x H H0.
 by rewrite ((Singleton_inv _ _ S) H).
Qed.

Lemma h_f_conti_at_x0 (eps: R) (x_0 : point_set Xt)
 (h_eps_pos : eps > 0):  exists delta1:R,
  delta1 > 0 /\  forall x':point_set Xt, d x_0 x' < delta1
        -> d' (f x_0) (f x') < eps * /2.
Proof.
 apply: metric_space_fun_continuity_converse.
 -by apply: MetricTopology_metrizable.
 -by apply: MetricTopology_metrizable.
 -by apply: continuous_func_continuous_everywhere.
 -apply: Rmult_gt_0_compat => //=.
  by fourier. (* h_f_conti_at_x0 has been shown *)
Qed.

Lemma HH: (* Better to Rename *)
~ (exists eps:R, eps > 0 /\ (Mtemp2 eps)).
Proof.
(* Change SUBGOAL to False 
   and Introduce eps, h_eps_pos, and h_d *)
case => eps [h_eps_pos h_d].
(* Introduce choice_xx, h_RRn, and xn *)
case: (exists_xx h_d) => [choice_xx h_RRn] {h_d}.
set xn:Net nat_DS Xt := fun n:nat => fst (choice_xx n).
(* Introduce x_0 h_x_0 *)
have Ex_x_0: exists x_0 :point_set Xt, net_cluster_point xn x_0.
 apply: compact_impl_net_cluster_point;
  first by [].
  by apply: (inhabits O).
case: Ex_x_0 => [x_0 h_x_0]. (* Introduced *)
(* Introduce delta1, h_d1_pos, h_f_x_0, and OB *)
case: (h_f_conti_at_x0 x_0 h_eps_pos)=> [delta1 [h_d1_pos h_f_x_0]].
set OB:= open_ball (point_set Xt) d x_0 (delta1 * /2).
   rewrite {h_eps_pos}. (*h_eps_pos is not used any more *)
(* Introduce n0 and h_n0pos h_n0*)
have h_n0: exists n0:nat, (n0 > 0)%nat /\ / (INR n0) < delta1 * /2. 
 by apply: inverses_of_nats_approach_0; fourier.
case: h_n0 => [n0 [h_n0pos h_n0]].
(* Introduce h_n and InOBxn *)
case: (h_x_0 OB _ _ n0) => /= [ | | n [h_n InOBxn]].
-rewrite /OB (OBu delta1 x_0).
 apply: B_open_intro => S.
 move/ (Singleton_inv _ OB S) <-.
 apply /(indexed_union_intro _ x_0) /intro_open_ball.
 by fourier.
-apply: intro_characteristic_sat.
 rewrite metric_zero; last by [].
 by fourier.
   rewrite {h_x_0}. (*h_x_0 is not used any more *)

(* Introduce x1 and its properties*)
set x1:= fst (choice_xx n).
(* Property of x1 *)
have dx0x1 : d x_0 x1 < delta1 * /2.
 by case: InOBxn; rewrite (_ : (xn n)=x1 ).
(* Property of x1 *)
have d'f0f1: d'(f x_0) (f x1) < eps * /2.
 apply: h_f_x_0.
 by apply: (Rlt_trans _ (delta1 * /2) _); fourier.
rewrite {h_d1_pos InOBxn OB}. (*They are not used any more *)

(* Introduce x2 *)
set x2:= snd (choice_xx n).
(* Property of x2 *)
have d'f0f2 : d' (f x_0) (f x2) < eps * /2.
 have h_npos: (n > 0)%nat. by apply:(lt_le_trans _ n0 _).
 apply /h_f_x_0 /(Rle_lt_trans _ (d x_0 x1 + d x1 x2) _);
  first by apply: triangle_inequality.
 rewrite (_ : delta1 = delta1 * /2 + delta1 * /2); last by field.
  apply: Rplus_lt_compat; first by [].
  apply: (Rlt_trans _ (/ INR (S n)) _). 
  -by case: (h_RRn n).
  -apply: (Rlt_trans _ (/ INR n) _).
   +apply: Rinv_lt_contravar.
    *apply: Rmult_gt_0_compat; apply: lt_0_INR; first by [].
     by apply: lt_0_Sn.
    *by apply: lt_INR; apply: lt_n_Sn.
   +apply: (Rle_lt_trans _ (/ INR n0) _);  last by [].
    by apply: Rle_Rinv;
      [apply: lt_0_INR |apply: lt_0_INR |apply: le_INR].
rewrite {h_f_x_0 h_n0pos h_n0 h_n n0}. (*They are not used any more *)

(* RETURN TO SUBGOAL : False :  For Contradiction X *)
have h_d'f1f2: d' (f x1) (f x2) < eps.
 rewrite (_: eps = eps * /2 + eps * /2); last by field.
 apply: (Rle_lt_trans _ (d' (f x1) (f x_0) + d' (f x_0) (f x2)) _).
 -by apply: triangle_inequality.
 -apply: Rplus_lt_compat; last by [].
  by rewrite metric_sym.

(* RETURN TO SUBGOAL : False :  For Contradiction ~X *)
have Nh_d'f1f2: d' (f x1) (f x2) >= eps.
 by case: (h_RRn n) => [_ hd'] {h_RRn} ; rewrite/x1 /x2.

(* Show False by Contradiction *)
by apply: (Rlt_not_ge (d' (f x1) (f x2)) eps).
Qed.


(* Following lemma is uniform continuity of 
           (x1,x2) |-> d' (f x1) (f x2) on compact (X times X) *)
Lemma dist_uniform_on_compact (eps : R): 
eps > 0 ->
  exists delta:R, delta >0 /\ forall (x1:X) (x2:X),
    d x1 x2 < delta -> d' (f x1) (f x2) < eps.
Proof.
move=> h_eps_pos.
apply: NNPP => h_Ne.
(* SUBGOAL : False *) (* Introduce h_nExx and delta *)
 apply: HH; exists eps.
 apply: (conj h_eps_pos) => delta h_delta_pos.
 apply: NNPP => h_nExx.
(* Return to SUBGOAL : False *) (* Introduce h_d'ge *)
 apply: h_Ne; exists delta.
 apply: (conj h_delta_pos) => x1 x2 h_dxx.
 apply: Rnot_ge_lt => h_d'ge.
(* Return to SUBGOAL : False *)
 by apply: h_nExx; exists x1; exists x2. (* Thanks to h_d'ge *)
Qed.

End UnifCompact.

Section CompactComplete.

Variable X:Type.
Variable d:X->X->R.

Hypothesis d_metric: metric d.
Let Xt:=  MetricTopology d d_metric. 

Lemma compact_complete : compact Xt -> complete d d_metric. 
Proof.
move=> cpt xn xn_cchy.
set xN:Net nat_DS Xt := xn.

have cluster_pt: exists x0: point_set Xt, net_cluster_point xN x0. 
  apply: compact_impl_net_cluster_point; first by apply: cpt.
  by apply /inhabits /O.

case: cluster_pt => x0 x0_cluster.
exists x0. 
apply: (metric_space_net_limit Xt d)=> [ | eps eps_pos]; first
 by apply: MetricTopology_metrizable.
apply metric_space_net_cluster_point_converse 
          with (d:=d) (eps:=/2 * eps) in x0_cluster; last first.
 by fourier.
 by apply: MetricTopology_metrizable.

case: (xn_cchy (/2 * eps)) =>  [ | i0 H_cchy]; first by fourier.
case: (x0_cluster i0) => j0 [H_i0j0 H_cluster].
exists j0 => j H_j0j.
rewrite /xN in H_cluster.
apply: (Rle_lt_trans _ (d x0 (xn j0) + d (xn j0) (xn j)) _); first
 by apply /triangle_inequality /d_metric.
apply: (Rlt_le_trans _ (/2 * eps + /2 * eps) _); last by fourier.
apply: Rplus_lt_compat; first by apply: H_cluster.
apply: H_cchy; first by [].
by apply: (le_trans _ j0 _).
Qed.

End CompactComplete.

Section InvImage.

Variables X Y:Type.
Variable f:X->Y.
Variable T:Ensemble Y.

Lemma inverse_image_image (x : X): In (inverse_image f T) x -> In T (f x). 
Proof. by case. Qed.

End InvImage.

Section OpenBallinOpen.

Variable X:Type.
Variable d:X->X->R.

Hypothesis d_metric: metric d.

Let Xt := MetricTopology d d_metric.

Variable A : Ensemble (point_set Xt).

Let At := SubspaceTopology  A.
Let d_A := fun x y: point_set At =>
   d (proj1_sig x) (proj1_sig y).

Lemma d_A_metric : metric d_A.
Proof. by apply: d_restriction_metric. Qed.

Lemma open_ball_in_open
 (x: point_set Xt) (U : Ensemble (point_set Xt))
  :In U x -> open U ->
          exists r:R, r>0 /\ Included (open_ball (point_set Xt) d x r) U.
Proof.
move=>InUx Uopen.
destruct Uopen; destruct InUx.

 have SU: In (IndexedUnion (metric_topology_neighborhood_basis d)) S; first
  by apply: H.

rewrite {H}.
destruct SU as [x' D]; destruct H.
set r0:= r - d x' x.
exists r0.

apply: conj.
-case: H1 => H1.
 by rewrite/r0; fourier.
-apply: (Inclusion_is_transitive X _ (open_ball X d x' r) _)=> x0 H2;
 last by apply: (family_union_intro _ (open_ball X d x' r)).
 apply /intro_characteristic_sat /(Rle_lt_trans _ (d x' x + d x x0) _); first
  by apply: triangle_inequality.
 rewrite (_ : r = d x' x + r0); last by rewrite /r0; field.
 by apply: Rplus_lt_compat_l; case: H2.
Qed.

Lemma pr_inc (a: point_set At) : proj1_sig a = subspace_inc A a.
Proof. by []. Qed.
 
Lemma open_ball_in_subspace_open
 (a: point_set At) (U:Ensemble (point_set At)):
  In U a -> open U ->
          exists r:R, r>0 /\ Included (open_ball (point_set At) d_A a r) U.
Proof.
move=> InUa U_open.
 have ExtU: exists V: Ensemble (point_set Xt), open V /\
  U = inverse_image (subspace_inc A) V; first
 by apply: subspace_topology_topology.
 case: ExtU => [V [V_open U_invV]].

have Xball: exists r:R, r>0 
             /\ Included (open_ball (point_set Xt) d (proj1_sig a) r) V.
 apply: open_ball_in_open; last by [].
 apply: inverse_image_image.
 by rewrite -U_invV.
 case: Xball => [r [r_pos IncOB_V]].

exists r.

apply: conj=> [ | a']; first by [].
case; rewrite /d_A => daa'_r.
 have InOBpra':
  In (open_ball (point_set Xt) d (proj1_sig a) r) (proj1_sig a'); first
  by apply: intro_characteristic_sat.
 have InVpra': In V (proj1_sig a'); first
  by apply /IncOB_V /InOBpra'.

by rewrite U_invV; apply: intro_characteristic_sat.
Qed.

End OpenBallinOpen.

Section MetricRestrictionMetrizes.

Variable X:Type.
Variable d:X->X->R.

Hypothesis d_metric: metric d.

Let Xt := MetricTopology d d_metric.

Variable A : Ensemble (point_set Xt).

Let At := SubspaceTopology  A.
Let d_A := fun x y: point_set At => d (proj1_sig x) (proj1_sig y).

Lemma ob_oN (x : point_set At) (r : R) (H : r > 0) :
  In (metric_topology_neighborhood_basis d (proj1_sig x))
    (open_ball (point_set Xt) d (proj1_sig x) r).
Proof. by apply: intro_open_ball. Qed.

Lemma d_metrizes: metrizes Xt d.
Proof. by apply: MetricTopology_metrizable. Qed.

Lemma inv_oball (x : point_set At) (r : R) (H : r > 0)
: open_ball (point_set At) d_A x r = 
  inverse_image (@subspace_inc Xt A) (open_ball (point_set Xt) d (proj1_sig x) r).
Proof.
apply: Extensionality_Ensembles;
 split; intros; constructor; destruct H0=> //=.
by destruct H0.
Qed.

Lemma onb (x : point_set At) (r : R) (H : r > 0):
 open_neighborhood (open_ball (point_set Xt) d (proj1_sig x) r) (proj1_sig x).
Proof. by apply d_metrizes. Qed.

Lemma pra (x a : point_set At) (r : R) (H : r > 0) (dxar : d_A x a < r) :
 In (open_ball (point_set Xt) d (proj1_sig x) r) 
    (proj1_sig a).
Proof. by apply: intro_characteristic_sat. Qed.

Lemma d_restriction_metrizes: metrizes At d_A. 
Proof.
constructor => U tmpU; destruct tmpU.

(* first branch *)
apply: conj.
-rewrite inv_oball; last by [].
 apply: (subspace_inc_continuous  Xt A).
 by case: (onb x H).
-apply: intro_characteristic_sat.
 rewrite metric_zero; first by [].
 by apply: d_restriction_metric.

(* second branch *)
have U': exists U':Ensemble (point_set Xt), open U' /\ 
   U = inverse_image (@subspace_inc Xt A) U'; first
 by apply: subspace_topology_topology.

case: U' => [U' [U'open U_U']]. 

have ObX: exists r:R, r>0 /\ Included (open_ball (point_set Xt) d (proj1_sig x) r) U'.
 apply: open_ball_in_open; last by [].
 rewrite /(subspace_inc A) in U_U'.
 apply: inverse_image_image=> /=.
 by rewrite -U_U'.

case: ObX => r [r_pos IobU'].
set V:= open_ball (point_set At) d_A x r.
exists V.
apply: conj=> [| a [dxar]]; first by apply: intro_open_ball.

have praU': In U' (proj1_sig a); first by apply: IobU'.
by rewrite U_U'.
Qed.

End MetricRestrictionMetrizes.

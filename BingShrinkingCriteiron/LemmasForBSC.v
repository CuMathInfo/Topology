(** LemmasForBSC.v by Ken'ichi Kuga *)
(** Lemmas for BingShrinkingCriterion.v **)

Require Import ssreflect ssrbool.
Require Import ClassicalChoice.
Require Import FunctionalExtensionality.
Require Import MetricSpaces.
Require Export Compactness.
Require Import Completeness.
Require Import SubspaceTopology.
Require Import WeakTopology.
Require Import RationalsInReals.
Require Export Subbases.
Require Import Fourier.

Open Scope R_scope.

Section UnifCompact. 

Variables X Y:Type.
Variables (d:X->X->R) (d':Y->Y->R).
Hypotheses (d_metric: metric d) (d'_metric: metric d').
Let Xt := MetricTopology d d_metric.
Let Yt := MetricTopology d' d'_metric.
Variable f : point_set Xt -> point_set Yt.
Hypotheses X_compact: compact Xt. (* Y_compact: compact Yt.*)
 
(* Following lemma is uniform continuity of 
           (x1,x2) |-> d' (f x1) (f x2) on compact (X times X) *)
Lemma dist_uniform_on_compact: continuous f -> 
forall eps:R, eps > 0 ->
  exists delta:R, delta >0 /\ forall (x1:X) (x2:X),
    d x1 x2 < delta -> d' (f x1) (f x2) < eps.
Proof.
move=> h_f_conti.
suff HH: ~ (exists eps:R, eps > 0 /\ (forall delta:R, delta > 0 -> 
  (exists (x1 x2:X), d x1 x2 < delta /\ d' (f x1) (f x2) >= eps))).
  move=>eps h_eps_pos.
  apply NNPP.
    move=>h_Ne.
    apply HH.
    clear HH.
    exists eps.
    split.
  by apply h_eps_pos.
  move=>delta h_delta_pos.
  apply NNPP.
    move=> h_nExx.
    apply h_Ne.
    clear h_Ne.
    exists delta.
    split.
  by apply h_delta_pos.
  move=> x1 x2 h_dxx.
    apply Rnot_ge_lt.
    move=>h_d'ge.
    apply h_nExx.
    exists x1.
    exists x2.
    split.
  by apply h_dxx.
by apply h_d'ge.
move=>h_Ee.
destruct h_Ee as [eps [h_eps_pos h_d]].

pose RR (n:nat) (xx: X*X):Prop :=
    d (fst xx) (snd xx) < / INR (S n) /\ 
    d' (f (fst xx)) (f (snd xx)) >= eps. 
have exists_xx: exists choice_xx: nat -> X*X, 
  forall n:nat, RR n (choice_xx n).
apply choice.
move=> n.
destruct h_d with (/ INR (S n)) as [x1].
red.
apply Rinv_0_lt_compat.
apply lt_0_INR.
by apply lt_0_Sn.
destruct H as [x2 [h_dxx h_d'ff]].
exists (x1,x2).
red.
split.
by apply h_dxx.
by apply h_d'ff.
destruct exists_xx as [choice_xx h_RRn].
set xn:Net nat_DS Xt := fun n:nat => fst (choice_xx n).
have Ex_x_0: exists x_0 :point_set Xt, net_cluster_point xn x_0.
apply compact_impl_net_cluster_point.
by apply X_compact.
by apply (inhabits O).
destruct Ex_x_0 as [x_0 h_x_0].
red in h_x_0.
have h_f_conti_at_x0: exists delta1:R, delta1 > 0 /\
  forall x':point_set Xt,
     d x_0 x' < delta1 -> d' (f x_0) (f x') < eps * /2.
apply metric_space_fun_continuity_converse.
by apply MetricTopology_metrizable.
by apply MetricTopology_metrizable.
apply continuous_func_continuous_everywhere.
by apply h_f_conti.
apply Rmult_gt_0_compat.
by apply h_eps_pos.
fourier. 
destruct h_f_conti_at_x0 as [delta1 [h_d1_pos h_f_x_0]].
set OB:= open_ball (point_set Xt) d x_0 (delta1 * /2).
have h_n0: exists n0:nat, (n0 > 0)%nat /\ / (INR  n0) < delta1 * /2. 
apply inverses_of_nats_approach_0.
fourier.
destruct h_n0 as [n0 [h_n0pos h_n0]].
destruct h_x_0 with OB n0 as [n]. 
simpl.
have OBu: OB = FamilyUnion (Singleton OB).
apply Extensionality_Ensembles; split; red; intros.
apply family_union_intro with OB.
by apply In_singleton.
exact.
destruct H.
apply Singleton_inv in H.
by rewrite H.
rewrite OBu.
apply B_open_intro . 
move=> S h_OBS.
apply Singleton_inv in h_OBS.
rewrite<-h_OBS.
rewrite/OB.
apply indexed_union_intro with x_0.
constructor.
fourier.
constructor.
rewrite metric_zero.
fourier.
exact.
destruct H as [h_n InOBxn].
simpl in n.
simpl in h_n.
have h_npos: (n > 0)%nat.
red.
red in h_n0pos.
apply lt_le_trans with n0.
exact.
exact.
set x1:= fst (choice_xx n).
set x2:= snd (choice_xx n).
have xnn_x1: (xn n) = x1.
rewrite/x1.
by rewrite/xn.
destruct InOBxn.
rewrite xnn_x1 in H.
have d'f0f1: d'(f x_0) (f x1) < eps * /2.
apply h_f_x_0.
apply Rlt_trans with (delta1 * /2).
(* destruct InOBxn.
rewrite<-xnn_x1.*)
exact.
fourier.
have d'f0f2 : d' (f x_0) (f x2) < eps * /2.
apply h_f_x_0.
apply Rle_lt_trans with (d x_0 x1 + d x1 x2).
by apply triangle_inequality.
have d2 : delta1 = delta1 * /2 + delta1 * /2 by field.
rewrite d2; clear d2.
apply Rplus_lt_compat.
exact.
apply Rlt_trans with (/ INR (S n)). 
destruct h_RRn with n.
by rewrite/x1 /x2.
apply Rlt_trans with (/ INR n). 
apply Rinv_lt_contravar.
apply Rmult_gt_0_compat.
red.
apply lt_0_INR.
red in h_npos.
exact.
red.
apply lt_0_INR.
by apply lt_0_Sn.
apply lt_INR.
by apply lt_n_Sn.
apply Rle_lt_trans with (/ INR n0).
SearchAbout Rinv.
apply Rle_Rinv.
apply lt_0_INR.
red in h_n0pos.
exact.
apply lt_0_INR.
red in h_npos.
exact.
apply le_INR.
exact.
exact.
have h_d'f1f2: d' (f x1) (f x2) < eps.
have eps2: eps = eps * /2 + eps * /2 by field.
rewrite eps2; clear eps2.
apply Rle_lt_trans with (d' (f x1) (f x_0) + d' (f x_0) (f x2)).
by apply triangle_inequality.
apply Rplus_lt_compat.
by rewrite metric_sym.
exact.
have h_d'f1f2e: d' (f x1) (f x2) >= eps.
destruct h_RRn with n as [_ hd'].
by rewrite/x1 /x2.
move: h_d'f1f2e.
apply Rlt_not_ge.
exact.
Qed.

End UnifCompact.

Section CompactComplete.


Variable X:Type.
Variable d:X->X->R.

Hypothesis d_metric: metric d.
Let Xt:=  MetricTopology d d_metric. 

Lemma compact_complete : compact Xt -> complete d d_metric. 
Proof.
move=> cpt.  
red.
move=> xn xn_cchy.
set xN:Net nat_DS Xt := xn.
have cluster_pt: exists x0: point_set Xt, net_cluster_point xN x0. 
  apply compact_impl_net_cluster_point.
  apply cpt.
  constructor.
  by apply O.
destruct cluster_pt as [x0 x0_cluster].
exists x0. 
apply metric_space_net_limit with d.
apply MetricTopology_metrizable.
move=> eps eps_pos.
apply metric_space_net_cluster_point_converse 
          with (d:=d) (eps:=/2 * eps) in x0_cluster.
destruct xn_cchy with (eps:= /2 * eps) as [i0 H_cchy].
fourier.
destruct x0_cluster with i0 as [j0 [H_i0j0 H_cluster]].
exists j0.
move=> j H_j0j.
rewrite/xN.
rewrite/xN in H_cluster.
apply Rle_lt_trans with (d x0 (xn j0) + d (xn j0) (xn j)).
apply triangle_inequality.
apply d_metric.
apply Rlt_le_trans with (/2 * eps + /2 * eps).
apply Rplus_lt_compat.
apply H_cluster.
apply H_cchy.
red. 
by apply H_i0j0.
red.
apply le_trans with j0.
by apply H_i0j0.
by apply H_j0j.
fourier.
by apply MetricTopology_metrizable.
fourier.
Qed.

End CompactComplete.

(********)

Section InvImage.
Print inverse_image.

Variables X Y:Type.
Variable f:X->Y.
Variable T:Ensemble Y.

Lemma inverse_image_image: forall x:X, In (inverse_image f T) x -> In T (f x). 
Proof.
move=>x Ix.
by destruct Ix.
Qed.

End InvImage.

(*
Section SubB.

Variable X: TopologicalSpace.
Variable SB:Family (point_set X).

Record my_subbasis : Prop:= {
  subbasis_elements : forall U:Ensemble (point_set X),
    In SB U -> open U;
  subbasis_cover: forall (U: Ensemble (point_set X)) (x :point_set X),
  In U x -> open U ->
  exists A:Type, FiniteT A /\
  exists V:A -> Ensemble (point_set X),
    (forall a:A, In SB (V a) ) /\
    In (IndexedIntersection V) x /\
    Included (IndexedIntersection V) U
}.

Print open.
Check subbasis_elements.
Check subbasis_cover.

Check open_basis_is_subbasis.
Lemma open_basis_is_subbasis: open_basis SB -> my_subbasis.
Proof. 
intros.
destruct H.
constructor.
exact open_basis_elements.
intros.
destruct (open_basis_cover x U H0 H).
destruct H1 as [? [? ?]].
exists True.
split. 
Print True_finite.
apply True_finite.
Print True_rect.
exists (True_rect x0).
repeat split;intros.
destruct a.
simpl.
assumption.
destruct a.
simpl.
assumption.
red.
intros.
destruct H4.
apply H2.
exact (H4 I).
Qed.
 
              
End SubB.
*)


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
Proof.
by apply d_restriction_metric.
Qed.


Lemma open_ball_in_open: 
 forall (x: point_set Xt) (U:Ensemble (point_set Xt)),In U x -> open U ->
          exists r:R, r>0 /\ Included (open_ball (point_set Xt) d x r) U.
Proof.
move=>x U InUx Uopen.
destruct Uopen.
destruct InUx.
have SasU: In (IndexedUnion (metric_topology_neighborhood_basis d)) S by apply H.
clear H.
Print IndexedUnion.
destruct SasU as [x' D].
destruct H.
set r0:= r - d x' x.
exists r0.
split.
destruct H1.
rewrite/r0.
fourier.
apply Inclusion_is_transitive with (open_ball X d x' r).
constructor.
apply Rle_lt_trans with (d x' x + d x x0).
by apply triangle_inequality.
have rr0: r = d x' x + r0.
rewrite/r0.
field.
rewrite rr0.
apply Rplus_lt_compat_l.
by destruct H2.
red.
move=>x0 Inob'x0.
Print FamilyUnion.
apply family_union_intro with (open_ball X d x' r).
assumption.
assumption.
Qed.

Lemma open_ball_in_subspace_open: 
 forall (a: point_set At) (U:Ensemble (point_set At)), In U a -> open U ->
          exists r:R, r>0 /\ Included (open_ball (point_set At) d_A a r) U.
Proof.
move=> a U InUa U_open.
have ExtU: exists V: Ensemble (point_set Xt), open V /\
  U = inverse_image (subspace_inc A) V.
by apply subspace_topology_topology.
destruct ExtU as [V [V_open U_invV]].
have Xball: exists r:R, r>0 /\ Included (open_ball (point_set Xt) d (proj1_sig a) r) V.
apply open_ball_in_open.
have pr_inc: proj1_sig a = subspace_inc A a by [].
rewrite pr_inc.
apply inverse_image_image.
by rewrite <- U_invV.
assumption.
destruct Xball as [r [r_pos IncOB_V]].
exists r.
apply conj.
assumption.
red.
move=>a' InOBa.
destruct InOBa as [daa'_r].
rewrite/d_A in daa'_r.
have InOBpra': In (open_ball (point_set Xt) d (proj1_sig a) r) (proj1_sig a').
by constructor.
have InVpra': In V (proj1_sig a').
apply IncOB_V.
by apply InOBpra'.
rewrite U_invV.
constructor.
have inc_proj: subspace_inc A a' = proj1_sig a' by [].
by rewrite inc_proj.
Qed.

End OpenBallinOpen.

Section MetricRestrictionMetrizes.

Variable X:Type.
Variable d:X->X->R.

Hypothesis d_metric: metric d.

Let Xt := MetricTopology d d_metric.

Variable A : Ensemble (point_set Xt).

Let At := SubspaceTopology  A.
Let d_A := fun x y: point_set At =>
   d (proj1_sig x) (proj1_sig y).


Lemma d_restriction_metrizes: metrizes At d_A. 
constructor.
move=> U MNBU.
destruct MNBU. 
constructor.
Print subspace_inc.
have inv_oball: open_ball (point_set At) d_A x r = 
 inverse_image (@subspace_inc Xt A) (open_ball (point_set Xt) d (proj1_sig x) r).
apply Extensionality_Ensembles;split;red;intros.
constructor.
simpl.
destruct H0.
rewrite/d_A in H0.
rewrite/subspace_inc.
constructor.
assumption.
constructor.
rewrite/d_A.
destruct H0.
destruct H0.
rewrite/subspace_inc in H0.
assumption.
rewrite inv_oball.
apply (subspace_inc_continuous  Xt A).
have ob_oN: 
In (metric_topology_neighborhood_basis d (proj1_sig x))
    (open_ball (point_set Xt) d (proj1_sig x) r).
apply intro_open_ball. 
assumption.
have d_metrizes: metrizes Xt d.
by apply MetricTopology_metrizable.
Print open_neighborhood_basis.
have onb: open_neighborhood (open_ball (point_set Xt) d (proj1_sig x) r) (proj1_sig x).
apply d_metrizes.
assumption.
destruct onb.
assumption.
constructor.
rewrite metric_zero.
red in H.
assumption.
apply d_restriction_metric.
assumption.
move=> U onUx.
destruct onUx.
have U': exists U':Ensemble (point_set Xt), open U' /\ 
   U = inverse_image (@subspace_inc Xt A) U'
by apply subspace_topology_topology.
destruct U' as [U' [U'open U_U']]. 
have ObX: exists r:R, r>0 /\ Included (open_ball (point_set Xt) d (proj1_sig x) r) U'.
apply open_ball_in_open.
rewrite/(subspace_inc A) in U_U'.
apply inverse_image_image.
simpl.
simpl in U_U'.
by rewrite<- U_U'.
assumption.
destruct ObX as [r [r_pos IobU']].
Print open_ball.
set V:= open_ball (point_set At) d_A x r.
exists V.
split.
rewrite/V.
constructor.
assumption.
red.
move=>a InVa.
destruct InVa as [dxar].
rewrite/d_A in dxar.
have pra:
 In (open_ball (point_set Xt) d (proj1_sig x) r) 
    (proj1_sig a).
by constructor.
have praU': In U' (proj1_sig a).
by apply IobU'. 
rewrite U_U'.
constructor.
by rewrite/subspace_inc.
Qed.

End MetricRestrictionMetrizes.


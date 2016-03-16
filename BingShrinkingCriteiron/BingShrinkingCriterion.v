(** BingShrinkingCriterion.v by Ken'ichi Kuga **************)
(*   Bing Shrinking Criterion                              *)
(*          and                                            *)
(*     Bing Shrinking Theorem for compact spaces           *)
(* *********************************************************)
(*

Definition approximable_by_homeos (f:X->Y): Prop:=
  forall eps:R, eps>0 ->
    exists h:point_set Xt -> point_set Yt,
    homeomorphism h /\
    (forall x:X, d' (f x) (h x) < eps). 

Definition Bing_shrinkable (f:X->Y): Prop:=     
  forall eps:R, eps>0 ->
    exists h : point_set Xt -> point_set Xt,
    homeomorphism h /\
    (forall x:X, d' (f x) (f (h x)) < eps) /\
    (forall x1 x2:X,  (f x1) = (f x2) -> d (h x1) (h x2)  < eps). 

Theorem Bing_Shrinking_Theorem:
 forall f: point_set Xt -> point_set Yt, 
continuous f -> surjective f ->
 (Bing_shrinkable f -> approximable_by_homeos f).    

************************************************************)

Require Import ssreflect ssrbool.
Require Import MetricSpaces.
Require Import RTopology.
Require Import Continuity.
Require Import ContinuousFactorization.
Require Import Completeness.
Require Import Compactness.
Require Import WeakTopology.
Require Import Homeomorphisms.
Require Import ProofIrrelevance.
Require Import Proj1SigInjective.
Require Import ClassicalChoice.
Require Import Classical.
Require Import Fourier.
Require Import FunctionalExtensionality.
Require Import RationalsInReals.

(*******************************)
Require Import BaireSpaces.
Require Import LemmasForBSC.
(*******************************)
Open Scope R_scope.

Section Logical_Topological_Lemmas.
(*** Some basic logic preparation ***)

Lemma piq_i_nqinp: forall p q:Prop,
(p -> q) -> (~q -> ~p).
Proof.
move=> p q hpiq hnq hp.
destruct hnq.
by apply:hpiq.
Qed.

Lemma npinq_i_qip:  forall p q:Prop,
 (~p -> ~q) -> (q -> p).
Proof.
move=> p q hnpinq hq.
apply NNPP.
move=> hnp.
move: hq.
by apply: hnpinq.
Qed.


Lemma naan_i_ee:
forall (T:Type) (R: T->T->Prop),
 ~(forall a b:T, ~(R a b)) -> exists a b:T, R a b. 
Proof.  
move=> T R hnaan.
apply NNPP.
move: hnaan.
apply piq_i_nqinp.
move=> ne a b Rab.
destruct ne.
exists a.
exists b.
assumption.
Qed.

(*** Some frequently used inequqlities ***)

Lemma pos_INR_Sn: forall n:nat, 0 < INR (S n).
Proof.
move=>n; 
by apply lt_0_INR, lt_0_Sn.
Qed.

Lemma pos_inv_INR_Sn: forall n:nat, 0 < /INR (S n).
Proof.
move=>n0.
apply Rinv_0_lt_compat.
by apply lt_0_INR; apply lt_0_Sn.
Qed.

Lemma Rlt_inv_INR_S_contravar:
forall n m:nat, (n < m)%nat -> /INR (S m) < /INR (S n).
Proof.
move=> n m nltm.
apply Rinv_lt_contravar.
apply Rmult_lt_0_compat.
apply pos_INR_Sn.
apply pos_INR_Sn.
apply lt_INR.
by apply lt_n_S.
Qed.

Lemma Rle_inv_INR_S_contravar:
forall n m:nat, (n <= m)%nat -> /INR (S m) <= /INR (S n).
Proof.
move=> n m nlem.
apply le_lt_eq_dec in nlem.
destruct nlem.
apply Rlt_le.
by apply Rlt_inv_INR_S_contravar.
rewrite e.
apply Req_le.
reflexivity.
Qed.

(******)

Definition id_map (XT:TopologicalSpace): point_set XT -> point_set XT:= 
  fun x:point_set XT => x.

Lemma id_map_continuous :
  forall XT:TopologicalSpace, continuous (id_map XT).
Proof.
move=> XT V V_open.
have inv_id: inverse_image (id_map XT) V = V. 
apply Extensionality_Ensembles; split; red; intros.
destruct H.
by rewrite/id_map in H.
constructor.
by rewrite/id.
by rewrite inv_id.
Qed.

Lemma id_map_homeomorphism : 
  forall XT:TopologicalSpace, homeomorphism (id_map XT).
Proof.
move=>XT.
Print homeomorphism.
apply intro_homeomorphism with (id_map XT).
apply id_map_continuous.
apply id_map_continuous.
by rewrite/id_map.
by rewrite/id_map.
Qed.

Variable T:Type.
Variable dt:T->T->R.
Hypothesis dt_metric: metric dt.

Let Tt := MetricTopology dt dt_metric.

Lemma open_ball_open:
  forall (x: T) (r: R) (D: Ensemble (point_set Tt)), 
    r > 0 -> D = open_ball T dt x r -> open D. 
Proof.
move=> x r D H_r_pos DisOB.
simpl.
set F:= Singleton D.
have DisUF : D = FamilyUnion F.
apply Extensionality_Ensembles;split;red;intros.
apply family_union_intro with D.
by apply In_singleton.
assumption.
destruct H.
have DisS: D = S by apply Singleton_inv.
by rewrite DisS.
have H: Included F (IndexedUnion (metric_topology_neighborhood_basis dt)).
move=> D' InFD'.
apply indexed_union_intro with x.
have DisD': D=D' by apply Singleton_inv.
rewrite <- DisD'.
rewrite DisOB.
apply intro_open_ball.
assumption.
rewrite DisUF.
by apply B_open_intro.
Qed.

Lemma MetricTopology_Hausdorff: Hausdorff (MetricTopology dt dt_metric). 
Proof.
apply T3_sep_impl_Hausdorff.
apply normal_sep_impl_T3_sep.
apply metrizable_impl_normal_sep.
apply intro_metrizable with dt.
apply dt_metric.
by apply MetricTopology_metrizable.
Qed.

Lemma lim_range: 
  forall (x: T) (xn:Net nat_DS Tt) (r:R) (n0:nat),
   (forall n:nat, 
          (n0 <= n)%nat  -> dt (xn n0) (xn n) <= r)
      -> net_limit xn x
         -> dt (xn n0) x <= r.
Proof.
move=> x xn r n0 dtxn0n lim_x.
apply NNPP.
move=> H.
apply Rnot_le_gt in H.
set eps:= dt (xn n0) x - r.
have eps_pos: eps > 0.
rewrite/eps.
fourier.
Print open_ball.
destruct lim_x with (open_ball T dt x eps).
apply open_ball_open with (x:=x) (r:=eps).
assumption.
reflexivity.
constructor.
rewrite metric_zero.
red in eps_pos.
assumption.
assumption.
simpl in H0.
simpl in x0.
set m0 := max x0 n0.
apply Rgt_lt in H.
have H1:
  dt (xn n0) x < r + eps.
apply Rle_lt_trans with
       (dt (xn n0) (xn m0) + dt (xn m0) x).
apply triangle_inequality.
assumption.
apply Rplus_le_lt_compat.
apply dtxn0n.
rewrite/m0.
apply Max.le_max_r.
destruct H0 with m0.
rewrite/m0.
apply Max.le_max_l.
by rewrite metric_sym.
rewrite/eps in H1.
fourier.
Qed.

End Logical_Topological_Lemmas.


Section BingShrinkingTheorem.

Variables X Y:Type.
Variables (d:X->X->R) (d':Y->Y->R).
Variable (y0:X->Y) (Y0:Y).
Hypotheses (d_metric: metric d)
           (d'_metric: metric d').
Hypothesis X_inhabited: inhabited X.

Let Xt := MetricTopology d d_metric.
Let Yt := MetricTopology d' d'_metric.


Let CMap := 
  { f:X->Y | bound (Im Full_set
             (fun x:X=> d' (y0 x) (f x)))/\ 
             @continuous Xt Yt f }.     

Let um (f g:CMap):R. 
refine (match f, g with exist f0 Hf, exist g0 Hg 
  => proj1_sig (sup (Im Full_set 
    (fun x:X => d' (f0 x) (g0 x))) _ _) end).
destruct Hf as [hf _].
destruct hf as [mf].
destruct Hg as [hg _].
destruct hg as [mg].
exists (mf + mg).
red; intros.
destruct H1.
rewrite H2.
apply Rle_trans with 
  (d' (y0 x) (f0 x) + d' (y0 x) (g0 x)).
Print metric_sym.
rewrite (metric_sym _ d' d'_metric (y0 x) (f0 x)); apply triangle_inequality; trivial.
assert (d' (y0 x) (f0 x) <= mf) 
  by (apply H; exists x; trivial).
assert (d' (y0 x) (g0 x) <= mg) 
  by (apply H0; exists x; trivial).
auto with real.
destruct X_inhabited as [x0].
exists (d' (f0 x0) (g0 x0)); exists x0. constructor.
reflexivity.
Defined.

Lemma um_metric: metric um.
Proof.
constructor.
move=> f g.
rewrite/um.
destruct f as [f0 Hf]; destruct g as [g0 Hg].
destruct sup. simpl.
destruct X_inhabited as [x0].
apply Rge_trans with (d' (f0 x0) (g0 x0)).
apply Rle_ge.
apply i.
by apply Im_intro with x0; constructor.
by apply d'_metric.

move=> f g.
rewrite/um.
destruct f as [f0 Hf]; destruct g as [g0 Hg].
destruct sup.
destruct sup.
simpl.
have j: Im Full_set (fun x:X => d'(f0 x) (g0 x))
      = Im Full_set (fun x:X => d'(g0 x) (f0 x)).
apply Extensionality_Ensembles;split;red;intros.
destruct H.
exists x1.
constructor.
by rewrite metric_sym.
destruct H.
exists x1.
constructor.
by rewrite metric_sym.
rewrite j in i.
apply Rle_antisym.
apply i; apply i0.
by apply i0; apply i.
move=> f g h.
destruct f as [f0 [Hf]].
destruct g as [g0 [Hg]].
destruct h as [h0 [Hh]].
simpl.
repeat destruct sup; simpl.
apply i.
red.
intros.
destruct H.
rewrite H0.
apply Rle_trans with 
  (d' (f0 x2) (g0 x2) + d' (g0 x2) (h0 x2)).
apply d'_metric.
have ifg: d' (f0 x2) (g0 x2) <= x0.
destruct i0 as [iH0]; apply iH0. by exists x2.
have igh: d' (g0 x2) (h0 x2) <= x1. 
destruct i1 as [iH1]; apply iH1. by exists x2.
by auto with real.

move=>f.
rewrite/um.
destruct f as [f0 [Bf Cf]].
destruct sup.
simpl.
destruct i.
apply Rle_antisym.
apply H0.
red; intros.
destruct H1.
rewrite H2.
rewrite (metric_zero _ d' d'_metric).
by auto with real.
apply H.
destruct X_inhabited as [x0].
exists x0.
by auto.
by rewrite (metric_zero Y d' d'_metric (f0 x0)).

move=> f g.
destruct f as [f0 [Bf Cf]].
destruct g as [g0 [Bg Cg]].
move=> Eum. 
(* Require Import Proj1SigInjective.*)
apply subset_eq_compatT.
(* Require Import FunctionalExtensionality.*)
extensionality x.
apply (metric_strict _ d' d'_metric). 
simpl in Eum.
destruct sup in Eum.
simpl in Eum.
rewrite Eum in i; clear Eum.
apply Rle_antisym.
apply i.
by exists x.
apply Rge_le.
Print metric_nonneg.
by apply (metric_nonneg _ d' d'_metric).
Qed.


Lemma Rle_d'_um: forall (f g:CMap) (x:X),
  d' (proj1_sig f x) (proj1_sig g x) <=  um f g. 
Proof.
move=> f g x.
destruct f as [f0 [Bf Cf]].
destruct g as [g0 [Bg Cg]].
simpl.
destruct sup.
simpl.
destruct i as [x0ub _].
apply x0ub.
by apply Im_intro with x.
Qed.

Lemma Rle_um_all_d': forall (f g:CMap) (r:R), r > 0 ->
(forall x:X, d' (proj1_sig f x) (proj1_sig g x) <=r) ->
  um f g <= r.
Proof.
move=> f g r r_pos Hd'r.
destruct f as [f0 [Bf Cf]].
destruct g as [g0 [Bg Cg]].
simpl.
destruct sup.
simpl.
simpl in Hd'r.
destruct i as [_ lub_x].
apply lub_x.
red.
move=>r1 Imr1.
destruct Imr1.
rewrite H0.
by apply Hd'r.
Qed.

Let CMapt := MetricTopology um um_metric.

Lemma um_complete: complete d' d'_metric -> complete um um_metric.
Proof.
red. 
move=> cpl_d' fn cauchy_fn.
SearchAbout nat_DS.
pose yn (x:X): Net nat_DS Yt:= fun n:nat => (proj1_sig (fn n%nat)) x.
have cauchy_yn: forall x:X, cauchy d' (yn x).
move=>x eps pos_eps.
destruct cauchy_fn with eps as [N cau_fn].
apply: pos_eps.
exists N.
move=>m n hm hn.
have d'xu: d' (yn x m) (yn x n) <= um (fn m) (fn n) by apply Rle_d'_um.
apply Rle_lt_trans with (um (fn m) (fn n)).
apply d'xu.
apply cau_fn.
apply hm.
by apply hn.
Print choice.
pose choice_R (x:X) (y:Y): Prop := net_limit (yn x) y. 
have choice_f0: forall x:X, exists y:Y, (choice_R x y).
move=>x.
rewrite/choice_R.
apply cpl_d'.
by apply cauchy_yn.
have choice_th: exists f0: X->Y, 
  (forall x:X, choice_R x (f0 x)) by apply choice. 
destruct choice_th as [f0 Hf0].
have Bf0: bound (Im Full_set (fun x:X=> d' (y0 x) (f0 x))).
red.
destruct cauchy_fn with 1 as [n0 Bd1].
apply Rlt_gt.
by apply Rlt_0_1.
pose Bfn0:=proj2_sig (fn n0).
destruct Bfn0 as [Bfn0 _].
destruct Bfn0 as [ub Bfn0].
red in Bfn0.
exists (ub+1).
red.
move=> r H. 
destruct H.
rewrite -> H0.
apply Rle_trans with  (d' (y0 x) (proj1_sig (fn n0) x) 
                    + d' (proj1_sig (fn n0) x) (f0 x)).
by apply triangle_inequality.
apply Rplus_le_compat.
destruct Bfn0 with (d' (y0 x) (proj1_sig (fn n0) x)).
by apply Im_intro with x.
by apply Rlt_le.
by apply Req_le.
have d'um1: forall n:nat, (n >= n0)%nat ->
  d' (proj1_sig (fn n0) x) (proj1_sig (fn n) x) < 1.
move=> n hn.
apply Rle_lt_trans with (um (fn n0) (fn n)).
apply Rle_d'_um. 
by apply Bd1.
apply Rnot_lt_le.
move=> Fh. 
set ep:= d' (proj1_sig (fn n0) x) (f0 x) - 1.
have hpos_ep: ep > 0.
apply Rlt_gt in Fh.
rewrite/ep.
by apply Rgt_minus.
Print net_limit.
Print open_ball.
destruct Hf0 with (x:=x) (U:= open_ball Y d' (f0 x) ep).
by apply open_ball_open with (x:=f0 x) (r:=ep).
constructor.
by rewrite metric_zero.
simpl in H1.
Print net_limit.
simpl in x0.
set m0:=max n0 x0.
destruct H1 with m0.
rewrite/m0.
by apply Max.le_max_r.
have tri: d' (proj1_sig (fn n0) x) (f0 x) <= 
   d' (proj1_sig (fn n0) x) (yn x m0) + d' (yn x m0) (f0 x) by apply triangle_inequality.
have H3: d' (proj1_sig (fn n0) x) (yn x m0) < 1.
apply d'um1.
rewrite/m0.
red.
by apply Max.le_max_l.
rewrite metric_sym in H2.
have H4: d' (proj1_sig (fn n0) x) (yn x m0) + d' (yn x m0) (f0 x) < 1 + ep 
                                                            by apply Rplus_lt_compat. 
rewrite/ep in H4.
have H5: 1+ (d' (proj1_sig (fn n0) x) (f0 x)-1) = d' (proj1_sig (fn n0) x) (f0 x) 
  by auto with real.
rewrite H5 in H4.
clear H5.
have H6: d' (proj1_sig (fn n0) x) (f0 x) < d' (proj1_sig (fn n0) x) (f0 x)
 by apply Rle_lt_trans with (d' (proj1_sig (fn n0) x) (yn x m0) + d' (yn x m0) (f0 x)).
by apply Rlt_irrefl in H6.
assumption.
have Cf0: @continuous Xt Yt f0.
apply pointwise_continuity.
move=>x.
simpl in x.
apply metric_space_fun_continuity with (dX:=d) (dY:=d').
apply MetricTopology_metrizable.
apply MetricTopology_metrizable.
move=> eps eps_pos.
simpl.
destruct cauchy_fn with (/4 * eps) as [N H].
by fourier.
have f0fN: forall x:X, 
  d' (f0 x) (proj1_sig (fn N) x) <= /4 * eps.
apply not_ex_not_all.
move=> FH.
destruct FH. 
apply Rnot_le_gt in H0.
set de:= d' (f0 x0) (proj1_sig (fn N) x0) - /4 * eps.
have de_pos: de > 0.
rewrite/de.
by fourier.
destruct Hf0 with x0 (open_ball Y d' (f0 x0) de).
apply open_ball_open with(x:=f0 x0) (r:=de).
assumption.
trivial.
constructor. 
by rewrite metric_zero.
simpl in H1.
simpl in x1.
set N1:= max N x1.
have f0ynx1 : d' (f0 x0) (yn x0 N1) < de.
apply H1.
rewrite/N1.
by apply Max.le_max_r.
have ynNynN1 : d' (yn x0 N1) (yn x0 N) < /4 * eps.
apply Rle_lt_trans with (um (fn N1) (fn N)).
apply Rle_d'_um.
apply H.
rewrite/N1.
red.
by apply Max.le_max_l.
auto.
have H2: d' (f0 x0) (yn x0 N) < de + /4 * eps.
apply Rle_lt_trans with 
 (d' (f0 x0) (yn x0 N1) + d' (yn x0 N1) (yn x0 N)).
apply triangle_inequality.
assumption.
by apply Rplus_lt_compat.
rewrite/de in H2.
rewrite/yn in H2.
have tmp: 
d' (f0 x0) (proj1_sig (fn N) x0) - /4 * eps + /4 * eps =
d' (f0 x0) (proj1_sig (fn N) x0) by fourier.
rewrite tmp in H2; clear tmp.
move:H2.
by apply Rlt_irrefl.
pose (proj2_sig (fn N)).
simpl in a.
destruct a as [_ HC].
Print continuous_func_continuous_everywhere.
apply (continuous_func_continuous_everywhere 
   Xt Yt (proj1_sig (fn N))) with x in HC.
Print metric_space_fun_continuity_converse.
apply (metric_space_fun_continuity_converse
  Xt Yt (proj1_sig (fn N)) x d d') with (/2 * eps) in HC.
destruct HC as [delta HC].
destruct HC as [delta_pos HC].
exists delta.
split.
assumption.
move=> x' dxx'_le_delta.
have dddd: d' (f0 x) (f0 x') <= 
d' (f0 x) (proj1_sig (fn N) x) 
+ d' (proj1_sig (fn N) x) (proj1_sig (fn N) x')
+ d' (proj1_sig (fn N) x') (f0 x').  
apply Rle_trans with 
 (d' (f0 x) (proj1_sig (fn N) x') 
+ d'(proj1_sig (fn N) x') (f0 x')).
apply triangle_inequality.
assumption.
apply Rplus_le_compat_r.
apply Rle_trans with
 (d' (f0 x) (proj1_sig (fn N) x)
+ d' (proj1_sig (fn N) x) (proj1_sig (fn N) x')).
apply triangle_inequality.
assumption.
apply Rplus_le_compat_r.
by apply Req_le.
apply Rle_lt_trans with
 (d' (f0 x) (proj1_sig (fn N) x) 
+ d' (proj1_sig (fn N) x) (proj1_sig (fn N) x')
+ d' (proj1_sig (fn N) x') (f0 x')).
apply dddd. clear dddd.
apply Rle_lt_trans with
 (d' (f0 x) (proj1_sig (fn N) x) 
+ d' (proj1_sig (fn N) x) (proj1_sig (fn N) x')
+ /4 * eps).
apply Rplus_le_compat_l.
rewrite metric_sym.
apply f0fN.
assumption.
have eps3 : eps = /4*eps + /2*eps + /4*eps by field.
rewrite {2} eps3.
clear eps3.
apply Rplus_lt_compat_r.
apply Rplus_le_lt_compat.
apply f0fN.
by apply HC.
apply MetricTopology_metrizable.
apply MetricTopology_metrizable.
fourier.
exists 
 (exist (fun g:X->Y => bound (Im Full_set
              (fun x:X=> d' (y0 x) (g x))) /\
              @continuous Xt Yt g) f0 (conj Bf0 Cf0)).
apply metric_space_net_limit with um.
apply MetricTopology_metrizable.
move=> eps eps_pos.
destruct cauchy_fn with (/2*eps) as [i0 H].
fourier.
exists i0.
move=> j i0j.
simpl in j.
simpl in i0j.
apply Rle_lt_trans with (/2*eps).
apply Rle_um_all_d'.
fourier. 
move=>x.
simpl.

have tmp: proj1_sig (fn j) x = (yn x) j by rewrite/yn.
rewrite tmp; clear tmp.
rewrite metric_sym.

Print lim_range.
apply (lim_range
           Y d' d'_metric (f0 x) (yn x) (/2*eps) j).
move=>n le_j_n.
rewrite/yn.
apply Rle_trans with (um (fn j) (fn n)).
apply Rle_d'_um.
apply Rlt_le.
apply H.
red.
assumption.
red.
apply le_trans with j.
assumption.
assumption.
apply Hf0.
assumption.
fourier.
Qed.

Hypothesis X_compact: compact Xt.
Hypothesis Y_compact: compact Yt.

Hypothesis y0Y0: forall x:X, y0 x = Y0.

Lemma continuous_bounded: forall f : point_set Xt -> point_set Yt,
  continuous f ->
  bound (Im Full_set (fun x:X=> d' (y0 x) (f x))).
Proof. 
move=> f f_conti.
set g: point_set Yt -> point_set RTop := 
                                  fun y => d' Y0 y.
set ft: point_set Xt -> point_set RTop := 
                                  fun x => g((f x)).
have ft_conti: continuous ft.
rewrite/ft.
apply continuous_composition. 
apply pointwise_continuity.
move=> y.
apply metric_space_fun_continuity with (dX:= d') (dY:=R_metric).
apply MetricTopology_metrizable.
apply RTop_metrization.
move=> eps eps_pos.
exists eps.
split.
assumption.
move=> y' d'yy'_eps.
rewrite/R_metric.
rewrite/g.
SearchAbout Rabs.
apply Rabs_def1. 
have tri1: d' Y0 y' <= d' y y' + d' Y0 y.
have tmp: d' y y' + d' Y0 y = d' Y0 y + d' y y' by apply Rplus_comm.
rewrite tmp; clear tmp.
by apply triangle_inequality.
have tri2: d' Y0 y'- d' Y0 y <= d' y y'.
fourier.
by apply Rle_lt_trans with (d' y y').
have tri2: d' Y0 y <= d' y y'+ d' Y0 y'.
have tmp: d' y y' + d' Y0 y' = d' Y0 y' + d' y y' by apply Rplus_comm.
rewrite tmp; clear tmp.
have tmp: d' y y' = d' y' y  by apply metric_sym.
rewrite tmp;clear tmp.
apply triangle_inequality.
assumption.
apply Rlt_le_trans with (- d' y y').
fourier.
fourier.
assumption.
apply R_compact_subset_bounded.
have Imft: Im Full_set (fun x : X => d' (y0 x) (f x))
  = Im Full_set ft.
apply Extensionality_Ensembles; split; red; intros.
Print Im.
destruct H.
rewrite y0Y0 in H0.
apply Im_intro with x.
assumption.
rewrite/ft.
by rewrite/g.
destruct H.
rewrite/ft in H0.
rewrite/g in H0.
rewrite<-y0Y0 with x in H0.
apply Im_intro with x.
assumption.
assumption.
rewrite Imft.
(* Require Import ContinuousFactorization. *)
(*have ft_img:
  forall x:point_set Xt, In (Im Full_set ft) (ft x).
move=>x.
by apply Im_intro with x.*)
Print continuous_surj_factorization.
set ftr := continuous_surj_factorization ft.
apply compact_image with ftr.
assumption.
apply continuous_surj_factorization_is_continuous.
assumption.
by apply continuous_surj_factorization_is_surjective.
Qed. (* continuous_bounded *)

Let W (f: CMap) (eps:R):
 Ensemble (point_set CMapt) :=
 fun g:CMap =>  forall (x1 x2:X), 
  (proj1_sig g x1) = (proj1_sig g x2) -> d x1 x2 < eps. 

Lemma W_is_open: forall (f: CMap) (eps:R),
                       eps > 0 -> open (W f eps). 
Proof.
apply NNPP. 
move=> FH.
apply not_all_ex_not in FH as [f FH2].
apply not_all_ex_not in FH2 as [r FH3].
apply imply_to_and in FH3.
destruct FH3 as [r_pos notOpen]. 
have front: exists fr:CMap, 
  (In (W f r) fr) /\ ~(In (interior (W f r)) fr).
apply not_all_not_ex.
move=> FH3.
have FH4: forall n:CMap, ~(In (W f r) n) \/ (In (interior (W f r))n).
move=>n.
have tmp: ~(In (W f r) n /\ ~In (interior (W f r))n)->
~(In (W f r) n) \/ (In (interior (W f r))n) by tauto.
apply tmp; clear tmp.
by apply FH3.
clear FH3.
have FH5: forall n:CMap, (In (W f r) n) -> (In (interior (W f r))n).
move=>n.
have tmp2: ~(In (W f r) n) \/ (In (interior (W f r))n)
      ->(In (W f r) n) -> (In (interior (W f r))n)
                           by tauto.
apply tmp2; clear tmp2.
by apply FH4.
clear FH4.
have FH6: Included (W f r) (interior (W f r)).
red.
by apply FH5.
have Winterior: (W f r) = interior (W f r).
apply Extensionality_Ensembles; split.
by apply FH6.
clear FH5 FH6.
by apply interior_deflationary.
have W_open: open (W f r).
rewrite Winterior.
by apply interior_open.
by move: W_open notOpen.
destruct front as [fr H].
destruct H as [fr_in_W fr_in_cl_c_W].
have fr_in_clcoW: In (Complement (interior (W f r))) fr. 
red.
red.
by apply fr_in_cl_c_W.
rewrite <- closure_complement in fr_in_clcoW.
clear fr_in_cl_c_W.
(********* fr found ***************)
rewrite/W in fr_in_W.
red in fr_in_W.
(**********************************) 
pose RR (n:nat) (g:CMap):Prop := 
  In (Complement (W f r)) g /\ um fr g < (/ INR (S n)).

have choice_gn : exists gn : nat -> CMap,
  forall n:nat, RR n (gn n).
apply choice.
move=>n.
have Exgn: Inhabited 
  (Intersection (Complement (W f r)) 
         (open_ball CMap um fr (/ INR (S n)))).
apply closure_impl_meets_every_open_neighborhood with fr.
by apply fr_in_clcoW.
apply open_ball_open with (x:=fr) (r:= / INR (S n)).
red.
apply Rinv_0_lt_compat.
apply lt_0_INR.
by apply lt_0_Sn.
reflexivity.
constructor.
rewrite metric_zero.
apply Rinv_0_lt_compat.
apply lt_0_INR.
by apply lt_0_Sn.
by apply um_metric.
destruct Exgn as [gn Hgn].
apply Intersection_inv in Hgn.
destruct Hgn as [CWgn OBgn].
destruct OBgn as [frgn].
exists gn.
red.
split.
by apply CWgn.
by apply frgn.
destruct choice_gn as [gn Hgn].
pose RA (k:nat ) (Ak: X * X * Y * CMap): Prop :=
    (proj1_sig (snd Ak)) (fst (fst (fst Ak))) = (snd (fst Ak)) /\
    (proj1_sig (snd Ak)) (snd (fst (fst Ak))) = (snd (fst Ak)) /\
     d (fst (fst (fst Ak))) (snd (fst (fst Ak))) >= r /\
    um fr (snd Ak) < / INR (S k). 
have choice_Ak: exists Ak: nat -> X * X * Y * CMap,
   forall k:nat, (RA k (Ak k)).
apply choice.
move=>k.
(********)
set nr:= S O.
(********)
have ABCk: exists (ak bk:X), 
  (proj1_sig (gn (max nr k)) ak) = (proj1_sig (gn (max nr k)) bk) /\
   d ak bk >= r.
apply naan_i_ee.
move=> FH1.   
destruct Hgn with (max nr k).
red in H.
red in H.  
rewrite/W in H.
rewrite/In in H.
destruct Hgn with (max nr k).
clear H2.
destruct H.
move=> a b pep.
apply Rfourier_not_ge_lt.
move:pep.
have log_lem1: forall p q:Prop, 
~(p/\q) -> (p -> q -> False) by tauto.
apply log_lem1.
by apply FH1.
Print exist.
destruct ABCk as [ak BCk].
destruct BCk as [bk Ck].
exists (ak, bk, (proj1_sig (gn (max nr k)) ak), (gn (max nr k))). 
rewrite/RA.
simpl.
split.
reflexivity.
destruct Ck as [Ck dakbk_r].
split.
apply eq_sym.
by apply Ck.
split.
by apply dakbk_r.
destruct Hgn with (max nr k).
induction k.
apply Rlt_le_trans with (/ INR (S (max nr 0))).
by apply H0.
apply Rle_Rinv.
by auto with real.
SearchAbout INR.
apply lt_0_INR.
by apply lt_0_Sn.
have INR1: 1 = INR(S O) by auto.
rewrite INR1.
apply le_INR.
apply le_n_S.
by apply Max.le_max_r.
apply Rlt_le_trans with (/ INR (S (max nr (S k)))).
by apply H0.
SearchAbout Rinv.
apply Rle_Rinv.
by auto with real.
apply lt_0_INR.
by apply lt_0_Sn.
have tmp2: INR (S k) + 1 = INR (S (S k)).
by auto with real.
rewrite tmp2; clear tmp2.
apply le_INR.
apply le_n_S.
by apply Max.le_max_r.
destruct choice_Ak as [abcgn Habcgn].
pose a_net:Net nat_DS Xt:= (fun (n:nat) => fst (fst (fst (abcgn n)))).
have cluster_a: exists a: point_set Xt, net_cluster_point a_net a.
apply compact_impl_net_cluster_point.
by apply X_compact.
by apply (inhabits O).
destruct cluster_a as [lim_a H_lim_a].
pose a_cond (n N:nat):= 
  (n <= N)%nat /\ d lim_a (a_net N) < / INR (S n).
have a_cond_choice: exists Na : nat -> nat, forall n, a_cond n (Na n).
apply choice.
move=>n.
destruct H_lim_a with (U:= (open_ball X d lim_a (/INR (S n)))) (i:= n).
apply open_ball_open with (x:= lim_a) (r:= /INR (S n)).
red.
by apply pos_inv_INR_Sn.
reflexivity.
constructor.
rewrite metric_zero.
by apply pos_inv_INR_Sn.
assumption.
destruct H.
destruct H0.
simpl in H.
simpl in x.
exists x.
red.
split.
assumption.
by apply H0.
destruct a_cond_choice as [Na H_Na].
red in H_Na.
pose b_net:Net nat_DS Xt:= (fun (n:nat) => snd (fst (fst (abcgn (Na n))))).
have cluster_b: exists b: point_set Xt, net_cluster_point b_net b.
apply compact_impl_net_cluster_point.
by apply X_compact.
by apply (inhabits O).
destruct cluster_b as [lim_b H_lim_b].
pose ab_cond (n N:nat):= (n <= N)%nat
  /\ (d lim_a (a_net (Na N)) < / INR (S n))
  /\ (d lim_b (b_net N) < / INR (S n)).
have ab_cond_choice: exists Nab : nat -> nat,
 forall n, ab_cond n (Nab n).
apply choice.
move=>n.
destruct H_lim_b with (U:= (open_ball X d lim_b (/INR (S n)))) (i:= n).
apply open_ball_open with (x:= lim_b) (r:= /INR (S n)).
red.
by apply pos_inv_INR_Sn.
reflexivity.
constructor.
rewrite metric_zero.
by apply pos_inv_INR_Sn.
assumption.
destruct H.
destruct H0.
simpl in H.
simpl in x.
exists x.
red.
split.
assumption.
split.
apply Rlt_le_trans with (/INR (S x)).
by apply H_Na.
apply Rle_inv_INR_S_contravar.
by apply H.
by apply H0.
destruct ab_cond_choice as [Nab H_Nab].
red in H_Nab.
(*******************)
pose aN (n:nat):X :=  a_net (Na (Nab n)).
pose bN (n:nat):X :=  b_net (Nab n). 
pose cN (n:nat): Y :=  snd (fst (abcgn (Na (Nab n)))). 
pose gN (n:nat): CMap := snd (abcgn (Na (Nab n))).
(********************)
have gNaN_cN : forall n:nat,
   proj1_sig (gN n) (aN n) = (cN n).
move=>n.
rewrite/(gN n) /(aN n) /(cN n).
rewrite/(a_net (Na (Nab n))).
destruct Habcgn with (Na (Nab n)).
by apply H.
have gNbN_cN : forall n:nat,
   proj1_sig (gN n) (bN n) = (cN n).
move=>n.
rewrite/(gN n) /(bN n) /(cN n).
rewrite/(b_net (Nab n)).
destruct Habcgn with (Na (Nab n)) as [Ha [Hb H]].
by apply Hb.
have daNbN_r : forall n:nat, d (aN n) (bN n) >= r.
move=>n.
rewrite/(aN n) /(bN n).
rewrite/(a_net (Na (Nab n)))  /(b_net (Nab n)).
destruct Habcgn with (Na (Nab n)) as [Ha [Hb [Hd H]]].
by apply Hd.
have umfrgN : forall n:nat, um fr (gN n) < / INR (S n).
move=>n.
rewrite/(gN n).
destruct Habcgn with (Na (Nab n)) as [Ha [Hb [Hd Hu]]].
apply Rlt_le_trans with (/ INR (S (Na (Nab n)))).
by apply Hu.
apply Rle_inv_INR_S_contravar.
apply le_trans with (Nab n).
destruct H_Nab with n as [H _].
by apply H.
destruct H_Na with (Nab n) as [H _].
by apply H.
have dlimaaN: forall n:nat, d lim_a (aN n) < / INR (S n).
move=>n.
rewrite/(aN n).
apply Rlt_le_trans with (/ INR (S (Nab n))).
destruct H_Na with (Nab n).
by apply H0.
apply Rle_inv_INR_S_contravar.
destruct H_Nab with n.
by apply H.
have dlimbbN: forall n:nat, d lim_b (bN n) < / INR (S n).
move=>n.
rewrite/(bN n).
destruct H_Nab with n.
destruct H0.
by apply H1.
(*************************)
SearchAbout metrizes.
have d_metrizes: metrizes Xt d 
by apply (MetricTopology_metrizable X d d_metric).
have d'_metrizes: metrizes Yt d' 
by apply (MetricTopology_metrizable Y d' d'_metric).
have frab: (proj1_sig fr lim_a) = (proj1_sig fr lim_b).
apply NNPP.
move=> fra_not_frb.
set eps := d' (proj1_sig fr lim_a) (proj1_sig fr lim_b).
have eps_nonneg: 0 <= eps.
rewrite/eps.
apply Rge_le.
by apply metric_nonneg.
red in eps_nonneg.
destruct eps_nonneg.
pose fr_conti:= proj2_sig fr.
simpl in fr_conti.
destruct fr_conti as [_ fr_conti].
have fr_conti_at_a: forall epsa : R, epsa > 0 ->
  exists deltaa:R, deltaa > 0 /\
  forall a': X, d lim_a a' < deltaa ->
    d' (proj1_sig fr lim_a) (proj1_sig fr a') < epsa.
apply (metric_space_fun_continuity_converse 
        Xt Yt (proj1_sig fr) lim_a d d' d_metrizes d'_metrizes).
apply continuous_func_continuous_everywhere.
by apply fr_conti.
have fr_conti_at_b: forall epsb : R, epsb > 0 ->
  exists deltab:R, deltab > 0 /\
  forall b': X, d lim_b b' < deltab ->
    d' (proj1_sig fr lim_b) (proj1_sig fr b') < epsb.
apply (metric_space_fun_continuity_converse 
        Xt Yt (proj1_sig fr) lim_b d d' d_metrizes d'_metrizes).
apply continuous_func_continuous_everywhere.
by apply fr_conti.
destruct fr_conti_at_a with (/4*eps) as [dela fr_conti_a].
by fourier.
destruct fr_conti_a as [dela_pos fr_conti_a].
destruct fr_conti_at_b with (/4*eps) as [delb fr_conti_b].
by fourier.
destruct fr_conti_b as [delb_pos fr_conti_b].
clear fr_conti_at_a fr_conti_at_b.
set del := Rmin dela delb.
have N_choice: exists N:nat, (N > 0)%nat /\ /INR N < Rmin (/4*eps) del.
apply RationalsInReals.inverses_of_nats_approach_0.
red.
apply Rmin_pos.
by fourier.
rewrite/del.
apply Rmin_pos.
by apply dela_pos.
by apply delb_pos.
destruct N_choice as [N H_N].
destruct H_N as [N_pos N_large].
have dfrafrb: d' (proj1_sig fr lim_a) (proj1_sig fr lim_b) <
 /4*eps + /4*eps + /4*eps + /4*eps.
apply Rle_lt_trans 
    with (d' (proj1_sig fr lim_a) (proj1_sig fr (bN N)) + 
          d' (proj1_sig fr (bN N)) (proj1_sig fr lim_b)).
apply triangle_inequality.
by apply d'_metric.
SearchAbout Rlt.
apply Rplus_lt_compat.
apply Rle_lt_trans
   with (d' (proj1_sig fr lim_a) (proj1_sig (gN N) (bN N)) + 
         d' (proj1_sig (gN N) (bN N)) (proj1_sig fr (bN N))).
apply triangle_inequality.
by apply d'_metric.
apply Rplus_lt_compat.
apply Rle_lt_trans
   with (d' (proj1_sig fr lim_a) (proj1_sig (gN N) (aN N)) +
         d' (proj1_sig (gN N) (aN N)) (proj1_sig (gN N) (bN N))).
apply triangle_inequality.
by apply d'_metric.
rewrite (gNaN_cN N).
rewrite (gNbN_cN N).
rewrite metric_zero.
SearchAbout Rplus.
rewrite Rplus_0_r.
apply Rle_lt_trans 
  with (d' (proj1_sig fr lim_a) (proj1_sig fr (aN N)) +
        d' (proj1_sig fr (aN N)) (cN N)).
apply triangle_inequality.
by apply d'_metric.
apply Rplus_lt_compat.
apply fr_conti_a.
apply Rlt_le_trans with del. 
apply Rlt_le_trans with (Rmin (/4*eps) del).
apply Rlt_trans with (/INR N).
apply Rlt_trans with (/INR (S N)).
by apply dlimaaN.
apply Rinv_lt_contravar.
apply Rmult_lt_0_compat.
apply lt_0_INR.
by red in N_pos.
by apply pos_INR_Sn.
apply lt_INR.
by apply lt_n_Sn.
SearchAbout Rmin.
apply Rmin_glb_lt.
apply Rlt_le_trans with (Rmin (/4*eps) del).
by apply N_large.
SearchAbout Rle.
by apply Rmin_l.
apply Rlt_le_trans with (Rmin (/4*eps) del).
by apply N_large.
by apply Rmin_r.
by apply Rmin_r.
rewrite/del.
by apply Rmin_l.
rewrite <- (gNaN_cN N).
apply Rle_lt_trans with (um fr (gN N)).
by apply Rle_d'_um.
apply Rlt_le_trans with (/INR (S N)).
by apply umfrgN.
apply Rlt_le.
apply Rlt_le_trans with (/INR N). 
SearchAbout Rinv.
apply Rinv_lt_contravar.
apply Rmult_lt_0_compat.
apply lt_0_INR.
by red in N_pos.
by apply pos_INR_Sn. 
apply lt_INR.
by apply lt_n_Sn.
apply Rlt_le.
apply Rlt_le_trans with (Rmin (/4*eps) del).
by apply N_large.
by apply Rmin_l.
by apply d'_metric.
apply Rle_lt_trans with (um fr (gN N)).
rewrite metric_sym.
by apply Rle_d'_um.
by apply d'_metric.
apply Rlt_le_trans with (/INR (S N)).
by apply umfrgN.
apply Rlt_le.
apply Rlt_le_trans with (/INR N). 
SearchAbout Rinv.
apply Rinv_lt_contravar.
apply Rmult_lt_0_compat.
apply lt_0_INR.
by red in N_pos.
by apply pos_INR_Sn. 
apply lt_INR.
by apply lt_n_Sn.
apply Rlt_le.
apply Rlt_le_trans with (Rmin (/4*eps) del).
by apply N_large.
by apply Rmin_l.
rewrite metric_sym.
apply fr_conti_b.
apply Rlt_le_trans with del.
apply Rlt_le_trans with  (Rmin (/4* eps) del).
apply Rlt_trans with (/INR N).
apply Rlt_trans with (/INR (S N)).
by apply dlimbbN.
apply Rinv_lt_contravar. 
apply Rmult_lt_0_compat.
apply lt_0_INR.
by red in N_pos.
by apply pos_INR_Sn.
apply lt_INR.
by apply lt_n_Sn.
by apply N_large.
by apply Rmin_r.
rewrite/del.
by apply Rmin_r.
by apply d'_metric.
have eps4:
/4*eps + /4*eps + /4*eps + /4*eps = eps by field.
rewrite eps4 in dfrafrb.
rewrite/eps in dfrafrb.
apply Rlt_not_eq in dfrafrb.
destruct dfrafrb.
by reflexivity.
rewrite/eps in H.
destruct fra_not_frb.
apply metric_strict with d'.
by apply d'_metric.
rewrite H.
by reflexivity.
(**********************************)
have dlimalimb_r: d lim_a lim_b < r.
apply fr_in_W.
by apply frab.
set eps2 := r - d lim_a lim_b.
have eps2_pos: eps2 > 0.
rewrite/eps2.
apply Rgt_minus.
by red.
have N_choice: exists N:nat, (N > 0)%nat /\ / INR N < /2* eps2.
apply RationalsInReals.inverses_of_nats_approach_0.
fourier.
destruct N_choice as [N [N_pos INR_e2]].
have invSN_e2: / INR (S N) < /2 * eps2.
apply Rlt_trans with (/ INR N).
apply Rinv_lt_contravar.
apply Rmult_lt_0_compat.
apply lt_0_INR.
by red in N_pos.
apply lt_0_INR.
by apply lt_0_Sn.
apply lt_INR. 
by apply lt_n_Sn.
by apply INR_e2.
have daNbN_lt_r: d(aN N) (bN N) < r.
apply Rle_lt_trans with (d (aN N) lim_b + d lim_b (bN N)).
apply triangle_inequality.
by apply d_metric.
apply Rle_lt_trans with (d (aN N) lim_a + d lim_a lim_b + d lim_b (bN N)).
apply Rplus_le_compat_r.
apply triangle_inequality.
by apply d_metric.
have dlalb: d lim_a lim_b = r - eps2.
rewrite/eps2.
by field.
rewrite dlalb.
apply Rlt_trans with (d (aN N) lim_a + (r - eps2) + /2* eps2).
apply Rplus_lt_compat_l.
apply Rlt_trans with (/ INR (S N)).
apply dlimbbN.
by apply invSN_e2.
apply Rlt_le_trans with (/2*eps2 + (r- eps2) + /2*eps2).
apply Rplus_lt_compat_r.
apply Rplus_lt_compat_r.
apply Rlt_trans with (/ INR (S N)).
rewrite metric_sym.
apply dlimaaN.
by apply d_metric.
by apply invSN_e2.
apply Req_le.
field.
apply Rlt_not_ge in daNbN_lt_r.
destruct daNbN_lt_r.
by apply daNbN_r. 
Qed. (*** W_is_open is defined ***)

Print Complement.
Print Im.
Lemma bijection_complement:
forall (Xt Yt:TopologicalSpace) 
(f: (point_set Xt) -> (point_set Yt)) (U: Ensemble (point_set Xt)),
 bijective f ->
 Complement (Im U f) = Im (Complement U) f.
move=> XT YT f U bij_f.
destruct bij_f as [inj_f surj_f].
apply Extensionality_Ensembles; split; red; move=> y H_y.
destruct surj_f with y.
red.
apply Im_intro with x.
red.
move=> In_U_x.
have InIm_y: In (Im U f) y.
red.
apply Im_intro with x.
assumption.
by apply eq_sym.
by destruct H_y.
by apply eq_sym.
red.
move=> ImUf_y.
red in H_y.
destruct H_y.
destruct ImUf_y.

have xeqx0: x = x0.
apply inj_f.
by rewrite <- H0.

rewrite xeqx0 in H.
by destruct H.
Qed.

(***********************************)

Lemma bij_conti_is_homeo_for_compact_Hausdorff_spaces:
compact Xt -> compact Yt -> Hausdorff Xt -> Hausdorff Yt ->
forall f: point_set Xt -> point_set Yt,
 bijective f -> continuous f -> homeomorphism f.
Proof.
move=> Xt_compact Yt_compact Xt_Hdf Yt_Hdf. 
move=> f f_bijective f_continuous.
apply invertible_open_map_is_homeomorphism.
apply bijective_impl_invertible.
assumption.
assumption.
red.
move => U U_open.
apply closed_complement_open.
apply compact_closed.
by apply Yt_Hdf.
have CImUf: forall xP : {x: point_set Xt | In (Complement U) x},
  Complement (Im U f) (f (proj1_sig xP)).
move=>xP.
destruct xP.
simpl.
red in i.
red in i.
red.
move=> InImUffx.
destruct i.
set y:= f x.
rewrite-/y in  InImUffx.
have yfx0: exists x0: point_set Xt, In U x0 /\ y = f x0.
destruct InImUffx.
exists x0.
split.
assumption.
assumption.
destruct yfx0.
destruct H.
destruct f_bijective.
Print injective.
by have ->: x=x0 by exact: H1.
(*have x_x0: x = x0 by exact: H1.*)
Print subset_eq_compatT.
(*
rewrite<-H0.
rewrite-/y.
reflexivity.

rewrite x_x0.
assumption.
*)
pose (fP:=fun xP: {x:point_set Xt | In (Complement U) x} =>
  (exist (Complement (Im U f)) (f (proj1_sig xP)) (CImUf xP)  )).
Print compact_image.     

apply (@compact_image 
        (SubspaceTopology (Complement U))
        (SubspaceTopology (Complement (Im U f)))
        fP). 

apply closed_compact.
apply Xt_compact.
red.
SearchAbout Complement.
by rewrite Complement_Complement.
red.
move=> V V_open.
Print subspace_inc.
have WinY: exists W:Ensemble (point_set Yt),
  open W /\ V = inverse_image (@subspace_inc Yt (Complement (Im U f))) W.
apply subspace_topology_topology.
assumption.
destruct WinY as [W' [W'_open V_inv_W']]. 
Print inverse_image.
have InvInv:  inverse_image fP V = 
              inverse_image (@subspace_inc Xt (Complement U))
                             (inverse_image f W').
rewrite/inverse_image.
rewrite/fP.   
simpl.
simpl.
apply Extensionality_Ensembles; split; red; intros.
destruct H.
red in H.
constructor.
constructor.
rewrite/subspace_inc.
rewrite V_inv_W' in H.
destruct H.
simpl in H.
assumption.
(*******************************)
red.
constructor.
red in H.
red.
rewrite/subspace_inc in H.
destruct H.
destruct H.
rewrite V_inv_W'.
rewrite/inverse_image.
constructor.
simpl.
assumption.
rewrite InvInv.
apply subspace_inc_continuous.
apply f_continuous.
assumption. 
destruct f_bijective as [f_inj f_surj].
red.
simpl.
move=> y.
destruct y as [y0' Hy0'].
destruct f_surj with y0' as [x0].
Print proof_irrelevance.
rewrite/fP.
have InCUx0: In (Complement U) x0.
red.
red.
move=> InUx0.
destruct Hy0'.
red.
by apply Im_intro with x0.
exists (exist _  _ InCUx0).
exact: subset_eq_compatT.
Qed. (*** bij_cont_is_homeo_for_compact_Hausdorff_spaces is defined ***)

(********************************************)


Definition approximable_by_homeos (f:X->Y): Prop:=
  forall eps:R, eps>0 ->
    exists h:point_set Xt -> point_set Yt,
    homeomorphism h /\
    (forall x:X, d' (f x) (h x) < eps). 

Definition Bing_shrinkable (f:X->Y): Prop:=     
  forall eps:R, eps>0 ->
    exists h : point_set Xt -> point_set Xt,
    homeomorphism h /\
    (forall x:X, d' (f x) (f (h x)) < eps) /\
    (forall x1 x2:X,  (f x1) = (f x2) -> d (h x1) (h x2)  < eps). 

Theorem Bing_Shrinking_Theorem:
 forall f: point_set Xt -> point_set Yt, 
continuous f -> surjective f ->
 (Bing_shrinkable f -> approximable_by_homeos f).    

Proof.
move=> f f_conti f_surj f_BS.
move=> eps eps_pos.
have f_bdd_conti: bound (Im Full_set (fun x:X=> d' (y0 x) (f x)))/\
                           @continuous Xt Yt f.
split.
apply continuous_bounded.
assumption.
assumption.
set fP := exist 
  (fun f: X->Y =>  bound (Im Full_set (fun x:X=> d' (y0 x) (f x)))/\
                           @continuous Xt Yt f) f f_bdd_conti. 

set fH : Ensemble (point_set CMapt) := 
  fun gP: CMap => exists hx: point_set Xt -> point_set Xt,
                  homeomorphism hx /\
                  forall x: point_set Xt, (proj1_sig gP) x = f (hx x).

have InfHfP: In fH fP.
red.
red.
exists (id_map Xt).
split.
by apply id_map_homeomorphism.
move=> x.
simpl.
by rewrite/id_map.
set CfH := closure fH.
set CfHt := SubspaceTopology CfH.
(* Caution: point_set CfHt = { gP:CfH | In CfH gP } *)
set um_restriction := fun f1PP f2PP: point_set CfHt =>
                                  um (proj1_sig f1PP) (proj1_sig f2PP).
have um_restriction_metric: metric um_restriction. 
apply d_restriction_metric. 
by apply um_metric.
have CfHt_baire: baire_space CfHt.
apply BaireCategoryTheorem with um_restriction um_restriction_metric.
apply d_restriction_metrizes.
have um_is_metric: metric um by apply um_metric.
have um_is_complete: complete um um_metric.
apply um_complete.
apply compact_complete.
rewrite - /Yt.
by apply Y_compact.
apply (closed_subset_of_complete_is_complete CMap um um_is_metric CfH).
by apply um_is_complete.
have CfH_closed: (@closed CMapt CfH) by apply closure_closed.
assumption.

set Wn: IndexedFamily nat (point_set CfHt) := fun n:nat =>
   inverse_image (subspace_inc CfH)  (W fP (/INR (S n))).
have WnOD: forall n:nat, open (Wn n) /\ dense (Wn n).   
move=>n.
apply conj.
have inc_conti: continuous (subspace_inc CfH) by apply subspace_inc_continuous.
rewrite/Wn.
apply:inc_conti.
apply:W_is_open.
red.
by apply pos_inv_INR_Sn.
(********************************************)  
apply meets_every_nonempty_open_impl_dense.
move=> U U_open U_Inhabited.
destruct U_Inhabited as [gPP InUgPP]. 
have exU: exists V:Ensemble (point_set CMapt), open V /\
  U = inverse_image (subspace_inc CfH) V.
apply subspace_topology_topology.
assumption.
destruct exU as [V [V_open U_iV]].
have r_exists: exists r:R, r>0 /\
 Included (open_ball (point_set CMapt) um (proj1_sig gPP) r) V.
apply open_ball_in_open.
rewrite U_iV in InUgPP.
red in InUgPP.
destruct InUgPP.
have projg_incg: proj1_sig gPP = subspace_inc CfH gPP by [].
by rewrite projg_incg.
assumption. 
destruct r_exists as [r [r_pos IcOB_V]]. 
(**********)
have Exfh0: Inhabited (Intersection fH (open_ball (point_set CMapt) um (proj1_sig gPP) (r*/2))). 
Print closure_impl_meets_every_open_neighborhood.
apply closure_impl_meets_every_open_neighborhood with (proj1_sig gPP).
destruct  gPP as [gP1 IngCfH].
simpl.
by rewrite/CfH. 
apply open_ball_open with (x:=proj1_sig gPP) (r:=r*/2).
fourier.
by simpl.
simpl.
constructor.
have umzero: um (proj1_sig gPP) (proj1_sig gPP) = 0. 
apply metric_zero.
by apply um_metric.
rewrite umzero.
clear umzero.
fourier.
destruct Exfh0 as [fh0 h1_fh0].
destruct h1_fh0 as [fh0 InfHfh0].
destruct H as [umgPfh0]. 
destruct InfHfh0 as [h0 [h_h0 h_fh0]].
destruct h_h0 as [h' h0_conti h'_conti h_h'h0 h_h0h'].
set eps1:= Rmin (r*/2) (/ INR (S n)).
have h_delta: exists delta:R, delta > 0 /\
  forall x1 x2 : X, d x1 x2 < delta -> d (h' x1) (h' x2) < eps1. 
apply dist_uniform_on_compact.
have h_Xt: Xt = MetricTopology d d_metric by rewrite/Xt.
by rewrite<-h_Xt.
assumption. 
rewrite/eps1.
red.
apply Rmin_pos.
fourier.
by apply pos_inv_INR_Sn.
destruct h_delta as [delta [pos_delta h_delta]].
destruct f_BS with (Rmin delta (r*/2)) as [k [k_homeo [h1_k h2_k]]].
red.
apply Rmin_pos.
by apply pos_delta.
fourier.
destruct k_homeo as [k' k_conti k'_conti h_k'k h_kk'].
set k'h := fun x: point_set Xt => k' (h0 x).
set h'k := fun x: point_set Xt => h' (k x).  
set fk'h := fun x: point_set Xt => f (k'h x).
have k'h_homeo: homeomorphism k'h.
apply intro_homeomorphism with h'k. 
rewrite/k'h.
apply continuous_composition.
by apply k'_conti.
by apply h0_conti.
rewrite/h'k.
apply continuous_composition.
by apply h'_conti.
by apply k_conti.
move=> x.
rewrite/h'k /k'h.
have kk'h0_h0: k (k' (h0 x)) = h0 x by apply h_kk'.
rewrite kk'h0_h0.
by apply h_h'h0.
move=> x.
rewrite/k'h /h'k.
have h0h'kx_kx : h0 (h' (k x)) = k x by apply h_h0h'.
rewrite h0h'kx_kx.
by apply h_k'k.
have fk'h_conti: continuous fk'h.
rewrite/fk'h.
apply continuous_composition.
assumption.
rewrite/k'h.
apply continuous_composition.
assumption.
assumption.
have fk'h_bdd_conti:
  bound (Im Full_set (fun x:X => d' (y0 x) (fk'h x))) /\
  continuous fk'h.
split.
apply continuous_bounded.
assumption.
assumption.
set fk'hP:=exist 
  (fun f: X->Y =>  bound (Im Full_set (fun x:X=> d' (y0 x) (f x)))/\
                           @continuous Xt Yt f) fk'h fk'h_bdd_conti. 
have InfHfk'hP: In fH fk'hP.
red.
red.
exists k'h.
split.
assumption.
simpl.
move=>x.
by rewrite/fk'h.
have InCfHfk'hP: In CfH fk'hP.
have IncfHCfH: Included fH CfH.
rewrite/CfH.
by apply closure_inflationary.
red in IncfHCfH.
apply IncfHCfH.
assumption.
set fk'hPP := exist (fun f0P: (point_set CMapt) => In CfH f0P) fk'hP InCfHfk'hP. 
exists fk'hPP.
split.
red.
red.
constructor.
red.
red.
move=>x1 x2 fk'hx1_fk'hx2.
simpl in fk'hx1_fk'hx2.
rewrite/fk'h in fk'hx1_fk'hx2.
have dfhx1_fhx2: d (k (k'h x1)) (k (k'h x2)) < delta.
apply Rlt_le_trans with (Rmin delta (r */2)).
by apply h2_k.
by apply Rmin_l.
rewrite/k'h in dfhx1_fhx2.
have kk'h0x1_h0x1: k (k' (h0 x1)) = h0 x1 by apply h_kk'.
have kk'h0x2_h0x2: k (k' (h0 x2)) = h0 x2 by apply h_kk'.
rewrite kk'h0x1_h0x1 in dfhx1_fhx2.
rewrite kk'h0x2_h0x2 in dfhx1_fhx2.
clear kk'h0x1_h0x1 kk'h0x2_h0x2.
have dx1x2_eps1: d (h' (h0 x1)) (h' (h0 x2)) < eps1 by apply h_delta.
have h'hx1_x1: h' (h0 x1) = x1 by apply h_h'h0.
have h'hx2_x2: h' (h0 x2) = x2 by apply h_h'h0.
rewrite h'hx1_x1 in dx1x2_eps1.
rewrite h'hx2_x2 in dx1x2_eps1.
clear h'hx1_x1 h'hx2_x2.
apply Rlt_le_trans with eps1.
by apply dx1x2_eps1.
rewrite/eps1.
by apply Rmin_r.
rewrite U_iV.
constructor.
rewrite/fk'hPP.
simpl.
suff InOBr: In (open_ball (point_set CMapt) um (proj1_sig gPP) r) fk'hP.
by apply IcOB_V.
constructor.
apply Rle_lt_trans with (um (proj1_sig gPP) fh0 + um fh0 fk'hP).
apply triangle_inequality.
by apply um_metric.
apply Rlt_le_trans with ((r * /2) + um fh0 fk'hP).
by apply Rplus_lt_compat_r.
have r_r2: r=r * /2 + r* /2 by field.
rewrite {2} r_r2; clear r_r2.
apply Rplus_le_compat_l.
apply Rle_um_all_d'.
fourier.
move=>x.
rewrite h_fh0.
simpl.
rewrite/fk'h.
rewrite/k'h .
have kk'h0x_h0x: k (k' (h0 x)) = h0 x by apply h_kk'.
have fh0x: f (h0 x) = f (k (k' (h0 x))) by  rewrite kk'h0x_h0x.
rewrite fh0x.
clear kk'h0x_h0x fh0x.
rewrite metric_sym.
apply Rlt_le.
apply Rlt_le_trans with (Rmin delta (r * /2)).
by apply h1_k.
by apply Rmin_r.
assumption.
Print baire_space.
have IWn_dense: dense (IndexedIntersection Wn).
apply CfHt_baire.
by apply WnOD.
(**********************************)
have InCfHfP: In CfH fP.
rewrite/CfH.
by apply closure_inflationary.
set fPP:= exist (fun gP : CMap => In CfH gP) fP InCfHfP.
set OBeps := (open_ball CMap um  fP eps). 
have WnBeps: Inhabited (Intersection (IndexedIntersection Wn) (inverse_image (subspace_inc CfH) OBeps)). 
apply dense_meets_every_nonempty_open.
by apply IWn_dense.
SearchAbout subspace_inc.
apply subspace_inc_continuous.
apply open_ball_open with (x:=fP) (r:=eps). 
apply eps_pos.
by rewrite/OBeps.
Print Inhabited.
apply Inhabited_intro with fPP.
constructor.
simpl.
rewrite/OBeps.
constructor.
rewrite metric_zero.
by apply eps_pos.
by apply um_metric.
destruct WnBeps as [hPP H_h].
destruct H_h as [hPP Wn_h OB_h].
(***)
set hP:= proj1_sig hPP.
set h:= proj1_sig hP.
set H_h := proj2_sig hP.
simpl in H_h.
destruct H_h as [b_h c_h].
clear b_h.
rewrite-/h in c_h.
destruct Wn_h as [hPP Wn_h].
destruct OB_h as [OB_h].
rewrite/subspace_inc in OB_h.
rewrite-/hP in OB_h.
destruct OB_h as [umfh].
exists h.
split.
apply bij_conti_is_homeo_for_compact_Hausdorff_spaces.
by apply X_compact.
by apply Y_compact.
by apply MetricTopology_Hausdorff.
by apply MetricTopology_Hausdorff .
constructor.
red.
move=> x1 x2 hx1_hx2.
apply metric_strict with d.
by apply d_metric.
apply NNPP.
move=> dx1x2n. 
apply Rdichotomy in dx1x2n.
destruct dx1x2n.
have dx1dx2nn: d x1 x2 >= 0.
apply metric_nonneg.
by apply d_metric.
move:H.
by apply Rge_not_lt.
have x1x2_n: exists n:nat, (n > 0)%nat /\ / (INR n) < d x1 x2.
apply inverses_of_nats_approach_0.
by apply H.
destruct x1x2_n as [n [n_pos x1x2_n]].
destruct Wn_h with n as [h_Wn].
rewrite/W in h_Wn.
red in h_Wn.
have sihPP_hP: subspace_inc CfH hPP = hP by rewrite/subspace_inc.
rewrite sihPP_hP in h_Wn.
rewrite-/h in h_Wn.
have dx1x2: d x1 x2 < / INR n.
apply Rlt_trans with (/ INR (S n)).
apply h_Wn.
by apply hx1_hx2.
apply Rinv_lt_contravar.
apply Rmult_lt_0_compat.
apply lt_0_INR.
by apply n_pos.
by apply pos_INR_Sn.
apply lt_INR.
by apply lt_n_Sn.
have dx1x2nn: d x1 x2 <= / INR n by apply Rlt_le.
move: dx1x2nn.
by apply Rgt_not_le.
red. 
apply NNPP.
move=>Nay.
apply not_all_ex_not in Nay.
destruct Nay as [y h_nx].
have InCImhy: In (Complement (Im Full_set h)) y.
rewrite/Complement.
red.
move=> InImhy.
destruct InImhy as [x InXx y_hx].
destruct h_nx.
by exists x.
Print Full_set.
Print Im.
have CImh_open: 
  open (@Complement (point_set Yt) (@Im (point_set Xt) _  Full_set h)).
apply closed_complement_open.
rewrite Complement_Complement.
apply compact_closed.
apply MetricTopology_Hausdorff.
Print continuous_factorization.
have h_img: forall x:point_set Xt, In (Im Full_set h) (h x).
move=>x.
by apply Im_intro with x.
Check continuous_surj_factorization.
set hf:= @continuous_factorization Xt Yt h (Im Full_set h) h_img.
apply compact_image with hf.
by apply X_compact.
by apply factorization_is_continuous.
red.
move=>y1P.  
destruct y1P as [y1 InImh_y1].
destruct InImh_y1  as [x1 InF_x y1 y1_hx1].
exists x1.
rewrite/hf.
rewrite/continuous_factorization.
pose proof (y1_hx1).
symmetry in H.
destruct H.
f_equal.
apply proof_irrelevance.
(*******************************) 
have y_r: exists r:R, r > 0 /\
  Included (open_ball (point_set Yt) d' y r) (Complement (Im Full_set h)).
apply open_ball_in_open.
by apply InCImhy.
by apply CImh_open.
destruct y_r as [r [r_pos IncObCImh]]. 
Check closure_impl_meets_every_open_neighborhood.
have fH_hP_r: Inhabited (
  Intersection fH (open_ball (point_set CMapt) um hP r)).  
apply closure_impl_meets_every_open_neighborhood with hP.
destruct hPP as [hP' InCfH_hP'].
simpl in hP.
rewrite/hP.
by rewrite/CfH.
apply open_ball_open with (x:= hP) (r:=r).
by apply r_pos.
by auto.
constructor.
rewrite metric_zero.
by red in r_pos.
by apply um_metric.
destruct fH_hP_r as [fh1 H].
destruct H as [fh1 InfHfh1 umhPfh1_r].
destruct umhPfh1_r as [umhPfh1_r].
destruct InfHfh1 as [h1 [h1_homeo fh1_f_h1]]. 
have Ex1:exists x1:point_set Xt, y = f (h1 x1).
destruct h1_homeo as [h1' h1_cont h1'_cont h1'h1 h1h1'].
destruct f_surj with y as [x2 fx2_y].
exists (h1' x2).
have h1h1'x2: h1 (h1' x2) = x2 by apply h1h1'.
by rewrite h1h1'x2; clear h1h1'x2.
destruct Ex1 as [x1 y_fh1x1].
have InObyr_hx1: In (open_ball (point_set Yt) d' y r) (h x1).
constructor.
rewrite y_fh1x1.
rewrite/h.
have fh1_pr: proj1_sig fh1 x1 = f (h1 x1) by apply fh1_f_h1.
rewrite-fh1_pr.
rewrite metric_sym.
apply Rle_lt_trans with (um hP fh1).
by apply Rle_d'_um.
by apply umhPfh1_r.
by apply d'_metric.
have InCImh_hx1: In (Complement (Im Full_set h)) (h x1).
by apply IncObCImh.
destruct InCImh_hx1.
Print Im.
by apply Im_intro with x1.
by apply c_h.
move=>x.
have f_fP: f = proj1_sig fP by rewrite/fP.
rewrite f_fP /h.
apply Rle_lt_trans with (um fP hP).
by apply Rle_d'_um.
exact.
Qed. (*  Bing_Shrinking_Theorem *)

End BingShrinkingTheorem.

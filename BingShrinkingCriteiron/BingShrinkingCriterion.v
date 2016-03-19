(** BingShrinkingCriterion.v by Ken'ichi Kuga **************)
(** Simplified using SSReflect by Mitsuharu Yamamoto  ******)

(***********************************************************)          
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
Require Import ProofIrrelevance.
Require Import ClassicalChoice.
Require Import Classical.
Require Import Fourier.
Require Import FunctionalExtensionality.
From mathcomp
Require Import ssreflect ssrbool.
From ZornsLemma
Require Import Proj1SigInjective.
From Topology
Require Import MetricSpaces RTopology ContinuousFactorization.
From Topology
Require Import Completeness Compactness WeakTopology Homeomorphisms.
From Topology
Require Import RationalsInReals Continuity.

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
by move=> n; apply: lt_0_INR; apply: lt_0_Sn.
Qed.

Lemma pos_inv_INR_Sn: forall n:nat, 0 < /INR (S n).
Proof.
by move=> n0; apply: Rinv_0_lt_compat; apply: pos_INR_Sn.
Qed.

Lemma Rlt_inv_INR_S_contravar:
forall n m:nat, (n < m)%nat -> /INR (S m) < /INR (S n).
Proof.
move=> n m nltm.
apply: Rinv_lt_contravar; first by apply: Rmult_lt_0_compat; apply: pos_INR_Sn.
by apply: lt_INR; apply: lt_n_S.
Qed.

Lemma Rle_inv_INR_S_contravar:
forall n m:nat, (n <= m)%nat -> /INR (S m) <= /INR (S n).
Proof.
move=> n m nlem.
apply: Rinv_le_contravar; first by apply: pos_INR_Sn.
by apply: le_INR; apply: le_n_S.
Qed.

(******)

Definition id_map (XT:TopologicalSpace): point_set XT -> point_set XT:= 
  fun x:point_set XT => x.

Lemma id_map_continuous :
  forall XT:TopologicalSpace, continuous (id_map XT).
Proof.
move=> XT V V_open.
suff ->: inverse_image (id_map XT) V = V by [].
apply: Extensionality_Ensembles; split => x //.
by case.
Qed.

Lemma id_map_homeomorphism : 
  forall XT:TopologicalSpace, homeomorphism (id_map XT).
Proof.
move=>XT.
by apply: (intro_homeomorphism _ (id_map XT)) => //; apply: id_map_continuous.
Qed.

Variable T:Type.
Variable dt:T->T->R.
Hypothesis dt_metric: metric dt.

Let Tt := MetricTopology dt dt_metric.

Lemma open_ball_open:
  forall (x: T) (r: R),
    r > 0 -> open (open_ball T dt x r : Ensemble (point_set Tt)).
Proof.
move=> x r H_r_pos.
apply: open_ball_is_open => //.
by apply: MetricTopology_metrizable.
Qed.

Lemma MetricTopology_Hausdorff: Hausdorff (MetricTopology dt dt_metric). 
Proof.
apply: T3_sep_impl_Hausdorff.
apply: normal_sep_impl_T3_sep.
apply: metrizable_impl_normal_sep.
apply: (intro_metrizable Tt dt) => //.
exact: MetricTopology_metrizable.
Qed.

Lemma lim_range: 
  forall (x: T) (xn:Net nat_DS Tt) (r:R) (n0:nat),
   (forall n:nat, 
          (n0 <= n)%nat  -> dt (xn n0) (xn n) <= r)
      -> net_limit xn x
         -> dt (xn n0) x <= r.
Proof.
move=> x xn r n0 dtxn0n lim_x.
apply: Rnot_gt_le => H.
set eps:= dt (xn n0) x - r.
have eps_pos: eps > 0 by apply: Rgt_minus.
case: (lim_x (open_ball T dt x eps)).
- exact: open_ball_open.
- constructor; by rewrite metric_zero.
- rewrite /= => x0 H0.
  suff: dt (xn n0) x < r + eps
    by apply: Rge_not_lt; rewrite /eps; fourier.
  set m0 := max x0 n0.  
  apply: Rle_lt_trans (_ : _ <= (dt (xn n0) (xn m0) + dt (xn m0) x)) _;
    first by apply: triangle_inequality.
  apply: Rplus_le_lt_compat (dtxn0n _ _) _; first by apply: Max.le_max_r.
  case: (H0 m0); first by apply: Max.le_max_l.
  by rewrite metric_sym.
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
rewrite (metric_sym _ d' d'_metric (y0 x) (f0 x)); apply triangle_inequality; trivial.
assert (d' (y0 x) (f0 x) <= mf) 
  by (apply H; exists x; trivial).
assert (d' (y0 x) (g0 x) <= mg) 
  by (apply H0; exists x; trivial).
auto with real.
destruct X_inhabited as [x0].
exists (d' (f0 x0) (g0 x0)); exists x0. constructor.
reflexivity.
(* Ssreflect-style proof.  But this makes the term bigger.
- case: Hf => [[mf Hf] _]; case: Hg => [[mg Hg] _].
  exists (mf + mg) => _ [x _ _ ->].
  apply: Rle_trans (_ : _ <= d' (f0 x) (y0 x)  + d' (y0 x) (g0 x)) _;
    first by apply: triangle_inequality.
  rewrite (metric_sym _ _ d'_metric).
  apply: Rplus_le_compat.
  + by apply: Hf; exists x.
  + by apply: Hg; exists x.
- case: X_inhabited => [x0].
  by exists (d' (f0 x0) (g0 x0)); exists x0.
*)
Defined.

Lemma um_metric: metric um.
Proof.
constructor.
- move=> [f0 Hf] [g0 Hg] /=.
  case: X_inhabited => [x0] /=.
  case: sup => /= x [Hxub Hxleast].
  apply: Rge_trans (_ : _ >= d' (f0 x0) (g0 x0)) _; last by case: d'_metric.
  apply: Rle_ge.
  apply: Hxub.
  by exists x0.
- move=> [f0 Hf] [g0 Hg] /=.
  case: sup => /= x [Hxub Hxleast].
  case: sup => /= y [Hyub Hyleast].
  have j: Im Full_set (fun x:X => d'(f0 x) (g0 x))
          = Im Full_set (fun x:X => d'(g0 x) (f0 x))
    by apply: Extensionality_Ensembles; split => /=;
       move => _ [x1 _ _ ->]; exists x1 => //; rewrite metric_sym.
  apply: Rle_antisym.
  + by apply: Hxleast; rewrite j; apply: Hyub.
  + by apply: Hyleast; rewrite -j; apply: Hxub.
- move=> [f0 Hf] [g0 Hg] [h0 Hh] /=.
  case: sup => /= x [Hxub Hxleast].
  case: sup => /= y [Hyub Hyleast].
  case: sup => /= z [Hzub Hzleast].
  apply: Hxleast => _ [x2 _ _ ->].
  apply: Rle_trans (_ : _ <= d' (f0 x2) (g0 x2) + d' (g0 x2) (h0 x2)) _;
    first by case: d'_metric.
  apply: Rplus_le_compat.
  + by apply: Hyub; exists x2.
  + by apply: Hzub; exists x2.
- move=> [f0 [Bf Cf]] /=.
  case: sup => /= x [Hxub Hxleast].
  apply: Rle_antisym.
  + apply: Hxleast => _ [x0 _ _ ->].
    rewrite metric_zero //.
    by auto with real.
  + apply: Hxub.
    case: X_inhabited => [x0].
    exists x0 => //.
    by rewrite metric_zero.
- move=> [f0 [Bf Cf]] [g0 [Bg Cg]] /=.
  case: sup => /= x0 [Hx0ub Hx0least] Hx0.
(* Require Import Proj1SigInjective.*)
  apply: subset_eq_compatT.
(* Require Import FunctionalExtensionality.*)
  extensionality x.
  apply: (metric_strict _ _ d'_metric).
  rewrite Hx0 in Hx0ub.
  rewrite Hx0 in Hx0least.
  apply: Rle_antisym.
  + apply: Hx0ub.
    by exists x.
  + apply: Rge_le.
    by case: d'_metric.
Qed.    


Lemma Rle_d'_um: forall (f g:CMap) (x:X),
  d' (proj1_sig f x) (proj1_sig g x) <=  um f g. 
Proof.
move=> [f0 [Bf Cf]] [g0 [Bg Cg]] /= x.
case sup => /= x0 [Hx0ub Hx0least].
apply: Hx0ub.
by exists x.
Qed.

Lemma Rle_um_all_d': forall (f g:CMap) (r:R), r > 0 ->
(forall x:X, d' (proj1_sig f x) (proj1_sig g x) <=r) ->
  um f g <= r.
Proof.
move=> [f0 [Bf Cf]] [g0 [Bg Cg]] /= r r_pos Hd'r.
case sup => /= x0 [Hx0ub Hx0least].
apply: Hx0least.
move=> _ [x _ _ ->].
exact: Hd'r.
Qed.

Let CMapt := MetricTopology um um_metric.

Lemma um_complete: complete d' d'_metric -> complete um um_metric.
Proof.
move=> cpl_d' fn cauchy_fn.
pose yn (x:X): Net nat_DS Yt:= fun n:nat => (proj1_sig (fn n%nat)) x.
have cauchy_yn: forall x:X, cauchy d' (yn x).
- move=> x eps pos_eps.
  case: (cauchy_fn _ pos_eps) => [N cau_fn].
  exists N.
  move=> m n hm hn.
  apply: Rle_lt_trans (Rle_d'_um _ _ _) _.
  by apply: cau_fn.
pose choice_R (x:X) (y:Y): Prop := net_limit (yn x) y. 
have choice_f0: forall x:X, exists y:Y, (choice_R x y)
  by move=> x; apply: cpl_d'; apply: cauchy_yn.
have [f0 Hf0]: exists f0: X->Y, 
  (forall x:X, choice_R x (f0 x)) by apply: choice. 
have Bf0: bound (Im Full_set (fun x:X=> d' (y0 x) (f0 x))).
- case: (cauchy_fn 1); first by apply: Rlt_0_1.
  move=> n0 Bd1.
  case: (proj2_sig (fn n0)) => [[ub Bfn0] _].
  exists (ub+1) => _ [x _ _ ->].
  apply: Rle_trans (_ : _ <= (d' (y0 x) (proj1_sig (fn n0) x)
                              + d' (proj1_sig (fn n0) x) (f0 x))) _;
    first by apply: triangle_inequality.
  apply: Rplus_le_compat.
  + apply: (Bfn0 (d' (y0 x) (proj1_sig (fn n0) x))).
    by exists x.
  + have d'um1: forall n:nat, (n >= n0)%nat ->
      d' (proj1_sig (fn n0) x) (proj1_sig (fn n) x) < 1.
    * move=> n hn.
      apply: Rle_lt_trans (Rle_d'_um _ _ _) _.
      by apply: Bd1.
    apply: Rnot_lt_le => Fh.
    set ep := d' (proj1_sig (fn n0) x) (f0 x) - 1.
    have hpos_ep: ep > 0 by apply: Rgt_minus.
    case: (Hf0 x (open_ball Y d' (f0 x) ep)).
    * exact: open_ball_open.
    * constructor.
      by rewrite metric_zero.
    * rewrite /= => x0 H1.
      set m0 := max n0 x0.
      case: (H1 m0); first by apply: Max.le_max_r.
      have H3: d' (proj1_sig (fn n0) x) (yn x m0) < 1
        by apply: d'um1; apply: Max.le_max_l.
      apply: Rle_not_gt.
      rewrite metric_sym //.
      apply: Rle_move_pr2ml.
      apply: Rle_trans (_ : _ <= d' (proj1_sig (fn n0) x) (yn x m0)
                                 + d' (yn x m0) (f0 x)) _;
        first by apply: triangle_inequality.
      apply: Rlt_le.
      apply: Rlt_le_trans (Rplus_lt_compat_r _ _ _ H3) _.
      auto with real.
have Cf0: @continuous Xt Yt f0.
- apply: pointwise_continuity => /= x.
  apply: (metric_space_fun_continuity Xt Yt _ _ d d').
  + exact: MetricTopology_metrizable.
  + exact: MetricTopology_metrizable.
  + move=> eps eps_pos /=.
    case: (cauchy_fn (/4 * eps)); first by fourier.
    move=> N H.
    have f0fN: forall x:X, 
      d' (f0 x) (proj1_sig (fn N) x) <= /4 * eps.
    * move=> x0.
      apply: Rnot_gt_le => H0.
      set de := d' (f0 x0) (proj1_sig (fn N) x0) - /4 * eps.
      have de_pos: de > 0 by apply: Rgt_minus.
      case (Hf0 x0 (open_ball Y d' (f0 x0) de)).
      - exact: open_ball_open.
      - constructor.
        by rewrite metric_zero.
      - rewrite /= => x1 H1.
        set N1 := max N x1.
        have f0ynx1 : d' (f0 x0) (yn x0 N1) < de
          by case: (H1 N1) => //; by apply: Max.le_max_r.
        have ynNynN1 : d' (yn x0 N1) (yn x0 N) < /4 * eps
          by apply: Rle_lt_trans (Rle_d'_um _ _ _) _; apply: H => //;
             apply: Max.le_max_l.
        have: d' (f0 x0) (yn x0 N) < de + /4 * eps.
        + apply: Rle_lt_trans (_ : _ <= (d' (f0 x0) (yn x0 N1)
                                         + d' (yn x0 N1) (yn x0 N))) _;
            first by apply: triangle_inequality.
            by apply: Rplus_lt_compat.
        apply: Rge_not_lt.
        rewrite /de /yn.
        by fourier.
    case: (proj2_sig (fn N)) => _.
    move/continuous_func_continuous_everywhere/(_ x).
    move/(metric_space_fun_continuity_converse Xt Yt _ _ d d').
    move/(_ (MetricTopology_metrizable _ _ _)).
    move/(_ (MetricTopology_metrizable _ _ _)).
    case/(_ (/2 * eps)); first by fourier.
    move=> delta [delta_pos HC].
    exists delta; split => // x' dxx'_le_delta.
    apply: Rle_lt_trans (_ : _ <= (d' (f0 x) (proj1_sig (fn N) x') 
                                   + d'(proj1_sig (fn N) x') (f0 x'))) _;
      first by apply: triangle_inequality.
    apply: Rle_lt_trans
             (Rplus_le_compat_r _ _ _
                (_ : _ <= (d' (f0 x) (proj1_sig (fn N) x) 
                           + d' (proj1_sig (fn N) x) (proj1_sig (fn N) x')))) _;
      first by apply: triangle_inequality.
    rewrite [d' _ (f0 x')]metric_sym //.
    apply: Rle_lt_trans (Rplus_le_compat_l _ _ _ (f0fN _)) _.
    rewrite [x in _ < x](_ : eps = /4*eps + /2*eps + /4*eps); last by field.
    apply: Rplus_lt_compat_r.
    apply: Rplus_le_lt_compat => //.
    by apply: HC.
exists (exist (fun g:X->Y => bound (Im Full_set
              (fun x:X=> d' (y0 x) (g x))) /\
              @continuous Xt Yt g) f0 (conj Bf0 Cf0)).
apply: (metric_space_net_limit CMapt um).
apply: MetricTopology_metrizable.
move=> eps eps_pos.
case: (cauchy_fn (/2*eps)); first by fourier.
move=> i0 H.
exists i0 => j i0j.
apply: Rle_lt_trans (_ : _ <= (/2*eps)) _.
- apply: Rle_um_all_d'; first by fourier.
  move=> x /=.
  rewrite -[proj1_sig (fn j) x]/((yn x) j).
  rewrite metric_sym //.
  rewrite /= in i0j.
  apply: (lim_range Y d' d'_metric (f0 x) (yn x) (/2*eps) j) => n le_j_n.
  + apply: Rle_trans (Rle_d'_um _ _ _) _.
    apply: Rlt_le.
    apply: H.
    by auto.
  + exact: le_trans le_j_n.
- exact: Hf0.
- by fourier.
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
- apply: continuous_composition => //.
  apply: pointwise_continuity => y.
  apply: (metric_space_fun_continuity Yt RTop _ _ d' R_metric).
  apply: MetricTopology_metrizable.
  by apply: RTop_metrization.
move=> eps eps_pos.
exists eps; split => //.
- move=> y' d'yy'_eps.
  rewrite /R_metric /g.
  apply: Rabs_def1. 
  + apply: Rlt_move_pr2ml.
    apply: Rle_lt_trans (_ : _ <= d' Y0 y + d' y y') _;
      first by apply: triangle_inequality.
    rewrite Rplus_comm.
    exact: Rplus_lt_compat_r.
  + apply: Rlt_move_pl2mr.
    rewrite Rplus_comm.
    apply: Rlt_move_mr2pl.
    apply: Rle_lt_trans (_ : _ <= d' Y0 y' + d' y' y) _;
      first by apply: triangle_inequality.
    apply: Rplus_lt_compat_l.
    by rewrite metric_sym // Ropp_involutive.
- apply: R_compact_subset_bounded.
  have ->: Im Full_set (fun x : X => d' (y0 x) (f x)) = Im Full_set ft
    by apply: Extensionality_Ensembles; split;
       move=> _ [x _ _ ->]; exists x => //; rewrite y0Y0.
(* Require Import ContinuousFactorization. *)
(*have ft_img:
  forall x:point_set Xt, In (Im Full_set ft) (ft x).
move=>x.
by apply Im_intro with x.*)
  set ftr := continuous_surj_factorization ft.
  apply: (compact_image ftr) => //.
  + exact: continuous_surj_factorization_is_continuous.
  + exact: continuous_surj_factorization_is_surjective.
Qed. (* continuous_bounded *)

Let W (eps:R):
 Ensemble (point_set CMapt) :=
 fun g:CMap =>  forall (x1 x2:X), 
  (proj1_sig g x1) = (proj1_sig g x2) -> d x1 x2 < eps. 

Lemma W_is_open: forall (eps:R),
                       eps > 0 -> open (W eps). 
Proof.
move=> r rpos.
suff ->: W r = interior (W r) by apply: interior_open.
apply: Extensionality_Ensembles; split; last by apply: interior_deflationary.
move=> fr fr_in_W.
rewrite -[W r]Complement_Complement interior_complement => fr_in_clcoW.
(********* fr found ***************)
pose RR (n:nat) (g:CMap):Prop := 
  In (Complement (W r)) g /\ um fr g < (/ INR (S n)).
have [gn Hgn]: exists gn : nat -> CMap,
  forall n:nat, RR n (gn n).
- apply: choice => n.
  have [gn Hgn]:
    Inhabited (Intersection (Complement (W r))
                            (open_ball CMap um fr (/ INR (S n)))).
  + apply: (closure_impl_meets_every_open_neighborhood _ _ fr) => //.
    * apply: open_ball_open.
      auto with *.
    * constructor. 
      rewrite metric_zero; last by apply: um_metric.
      auto with *.
  case: Hgn => {gn} gn CWgn [frgn].
  exists gn; split => //.
pose RA (k:nat) (Ak: X * X * Y * CMap): Prop :=
    (proj1_sig (snd Ak)) (fst (fst (fst Ak))) = (snd (fst Ak)) /\
    (proj1_sig (snd Ak)) (snd (fst (fst Ak))) = (snd (fst Ak)) /\
     d (fst (fst (fst Ak))) (snd (fst (fst Ak))) >= r /\
    um fr (snd Ak) < / INR (S k). 
have [abcgn Habcgn]: exists Ak: nat -> X * X * Y * CMap,
   forall k:nat, (RA k (Ak k)).
- apply: choice => k.
(********)
  set nr := S O.
(********)
  have [ak [bk [Ck dakbk_r]]]: exists (ak bk:X), 
      (proj1_sig (gn (max nr k)) ak) = (proj1_sig (gn (max nr k)) bk) /\
      d ak bk >= r.
  + apply: NNPP => Hnex.
    case: (Hgn (max nr k)).
    case=> ak bk Ck.
    apply: Rnot_ge_lt => dakbk_r.
    apply: Hnex.
    by exists ak, bk.
  exists (ak, bk, (proj1_sig (gn (max nr k)) ak), (gn (max nr k))).
  repeat split=> //.
  case: (Hgn (max nr k)) => _ H0.
  apply: Rlt_le_trans H0 _.
  apply: Rle_inv_INR_S_contravar.
  exact: Max.le_max_r.
pose a_net:Net nat_DS Xt:= (fun (n:nat) => fst (fst (fst (abcgn n)))).
have [lim_a H_lim_a]: exists a: point_set Xt, net_cluster_point a_net a
  by apply: compact_impl_net_cluster_point => //; apply: (inhabits O).
pose a_cond (n N:nat):= 
  (n <= N)%nat /\ d lim_a (a_net N) < / INR (S n).
have [Na H_Na]: exists Na : nat -> nat, forall n, a_cond n (Na n).
- apply: choice => n.
  case: (H_lim_a (open_ball X d lim_a (/INR (S n))) _ _ n).
  + apply: open_ball_open.
  + auto with *.
  + constructor.
    rewrite metric_zero => //.
    auto with *.
  + move=> x [H [H0]].
    by exists x.
pose b_net:Net nat_DS Xt:= (fun (n:nat) => snd (fst (fst (abcgn (Na n))))).
have [lim_b H_lim_b]: exists b: point_set Xt, net_cluster_point b_net b
  by apply: compact_impl_net_cluster_point => //; apply: (inhabits O).
pose ab_cond (n N:nat):= (n <= N)%nat
  /\ (d lim_a (a_net (Na N)) < / INR (S n))
  /\ (d lim_b (b_net N) < / INR (S n)).
have [Nab H_Nab]: exists Nab : nat -> nat, forall n, ab_cond n (Nab n).
- apply: choice => n.
  case: (H_lim_b (open_ball X d lim_b (/INR (S n))) _ _ n).
  + apply: open_ball_open.
  + auto with *.
  + constructor.
    rewrite metric_zero => //.
    auto with *.
  + move=> x [H [H0]].
    exists x; repeat split => //.
    apply: Rlt_le_trans (_ : _ < /INR (S x)) _; first by case: (H_Na x).
    exact: Rle_inv_INR_S_contravar.
(*******************)
pose aN (n:nat):X :=  a_net (Na (Nab n)).
pose bN (n:nat):X :=  b_net (Nab n). 
pose cN (n:nat): Y :=  snd (fst (abcgn (Na (Nab n)))). 
pose gN (n:nat): CMap := snd (abcgn (Na (Nab n))).
(********************)
have gNaN_cN : forall n:nat, proj1_sig (gN n) (aN n) = (cN n)
  by move=> n; case: (Habcgn (Na (Nab n))).
have gNbN_cN : forall n:nat, proj1_sig (gN n) (bN n) = (cN n)
  by move=> n; case: (Habcgn (Na (Nab n))) => _ [].
have daNbN_r : forall n:nat, d (aN n) (bN n) >= r
  by move=> n; case: (Habcgn (Na (Nab n))) => _ [_ []].
have umfrgN : forall n:nat, um fr (gN n) < / INR (S n).
- move=> n.
  apply: Rlt_le_trans (_ : _ < / INR (S (Na (Nab n)))) _;
    first by case: (Habcgn (Na (Nab n))) => _ [_ []].
  apply: Rle_inv_INR_S_contravar.
  apply: le_trans (_ : (_ <= Nab n)%nat) _; first by case: (H_Nab n).
  by case: (H_Na (Nab n)).
have dlimaaN: forall n:nat, d lim_a (aN n) < / INR (S n).
- move=> n.
  apply: Rlt_le_trans (_ : _ < / INR (S (Nab n))) _;
    first by case: (H_Na (Nab n)).
  apply: Rle_inv_INR_S_contravar.
  by case: (H_Nab n).
have dlimbbN: forall n:nat, d lim_b (bN n) < / INR (S n)
  by move=> n; case: (H_Nab n) => _ [].
have d_metrizes: metrizes Xt d 
  by apply: MetricTopology_metrizable.
have d'_metrizes: metrizes Yt d' 
  by apply: MetricTopology_metrizable.
have frab: (proj1_sig fr lim_a) = (proj1_sig fr lim_b).
- apply: (metric_strict _ d') => //.
  apply: Rle_antisym; last by apply: Rge_le; apply: metric_nonneg.
  apply: Rnot_gt_le.
  set eps := d' (proj1_sig fr lim_a) (proj1_sig fr lim_b).
  move=> eps_pos.
  case: (proj2_sig fr) => _ fr_conti.
  have fr_conti_at_a: forall epsa : R, epsa > 0 ->
    exists deltaa:R, deltaa > 0 /\
    forall a': X, d lim_a a' < deltaa ->
      d' (proj1_sig fr lim_a) (proj1_sig fr a') < epsa.
    by apply: (metric_space_fun_continuity_converse Xt Yt _ _ d d') => //;
       apply: continuous_func_continuous_everywhere.
  have fr_conti_at_b: forall epsb : R, epsb > 0 ->
    exists deltab:R, deltab > 0 /\
    forall b': X, d lim_b b' < deltab ->
      d' (proj1_sig fr lim_b) (proj1_sig fr b') < epsb.
    by apply: (metric_space_fun_continuity_converse Xt Yt _ _ d d') => //;
       apply: continuous_func_continuous_everywhere.
  case: (fr_conti_at_a (/4*eps)); first by fourier.
  move=> dela [dela_pos fr_conti_a] {fr_conti_at_a}.
  case: (fr_conti_at_b (/4*eps)); first by fourier.
  move=> delb [delb_pos fr_conti_b] {fr_conti_at_b}.
  set del := Rmin dela delb.
  have [N [N_pos N_large]]:
    exists N:nat, (N > 0)%nat /\ /INR N < Rmin (/4*eps) del
    by apply: RationalsInReals.inverses_of_nats_approach_0;
       do !apply: Rmin_pos => //; fourier.
  have HinvN: / INR (S N) < / INR N.
  + apply: Rinv_lt_contravar.
    apply: Rmult_lt_0_compat; auto with *.
    exact: lt_INR.
  have: d' (proj1_sig fr lim_a) (proj1_sig fr lim_b) <
        /4*eps + /4*eps + /4*eps + /4*eps.
  + apply: Rle_lt_trans
             (_ : _ <= (d' (proj1_sig fr lim_a) (proj1_sig fr (bN N)) + 
                        d' (proj1_sig fr (bN N)) (proj1_sig fr lim_b))) _;
      first by apply: triangle_inequality.
    apply: Rplus_lt_compat; last first.
    * rewrite metric_sym //.
      apply: fr_conti_b.
      apply: Rlt_le_trans (_ : _ < del) (Rmin_r _ _).
      apply: Rlt_le_trans (_ : _ < Rmin (/4*eps) del) (Rmin_r _ _).
      apply: Rlt_trans _ N_large.
      exact: Rlt_trans (dlimbbN _) _.
    apply: Rle_lt_trans
           (_ : _ <= (d' (proj1_sig fr lim_a) (proj1_sig (gN N) (bN N)) + 
                      d' (proj1_sig (gN N) (bN N)) (proj1_sig fr (bN N)))) _;
      first by apply: triangle_inequality.
    apply: Rplus_lt_compat; last first.
    * rewrite metric_sym //.
      apply: Rle_lt_trans (Rle_d'_um _ _ _) _.
      apply: Rlt_trans (umfrgN _) _.
      apply: Rlt_trans HinvN _.
      exact: Rlt_le_trans N_large (Rmin_l _ _).
    apply: Rle_lt_trans
             (_ : _ <= d' (proj1_sig fr lim_a) (proj1_sig (gN N) (aN N)) +
                       d' (proj1_sig (gN N) (aN N)) (proj1_sig (gN N) (bN N))) _;
      first by apply: triangle_inequality.
    rewrite gNaN_cN gNbN_cN metric_zero // Rplus_0_r.
    apply: Rle_lt_trans
             (_ : _ <= d' (proj1_sig fr lim_a) (proj1_sig fr (aN N)) +
                       d' (proj1_sig fr (aN N)) (cN N)) _;
      first by apply: triangle_inequality.
    apply: Rplus_lt_compat.
    * apply: fr_conti_a.
      apply: Rlt_le_trans (_ : _ < del) (Rmin_l _ _).
      apply: Rlt_le_trans (_ : _ < Rmin (/4*eps) del) (Rmin_r _ _).
      apply: Rlt_trans _ N_large.
      exact: Rlt_trans (dlimaaN _) _.
    * rewrite -gNaN_cN.
      apply: Rle_lt_trans (Rle_d'_um _ _ _) _.
      apply: Rlt_trans (umfrgN _) _.
      apply: Rlt_trans HinvN _.
      exact: Rlt_le_trans N_large (Rmin_l _ _).
  rewrite [x in _ < x](_ : _ = eps); last by field.
  exact: Rlt_irrefl.
have dlimalimb_r: d lim_a lim_b < r
  by apply: fr_in_W.
set eps2 := r - d lim_a lim_b.
have eps2_pos: eps2 > 0.
  by apply: Rgt_minus.
have [N [N_pos INR_e2]]: exists N:nat, (N > 0)%nat /\ / INR N < /2 * eps2.
  by apply: RationalsInReals.inverses_of_nats_approach_0; fourier.
apply: Rlt_not_ge (daNbN_r N).
have HinvSN: / INR (S N) < /2 * eps2.
- apply: Rlt_trans INR_e2.
  apply: Rinv_lt_contravar.
  apply: Rmult_lt_0_compat; auto with *.
  exact: lt_INR.
rewrite (_ : r = /2 * eps2 + ((r - eps2) + /2 * eps2)); last by field.
apply: Rle_lt_trans (_ : _ <= d (aN N) lim_a + d lim_a (bN N)) _;
  first by apply: triangle_inequality.
apply: Rplus_lt_compat;
  first by rewrite (metric_sym _ d) //; exact: Rlt_trans (dlimaaN _) HinvSN.
apply: Rle_lt_trans (_ : _ <= d lim_a lim_b + d lim_b (bN N)) _;
  first by apply: triangle_inequality.
apply: Rplus_le_lt_compat;
  last by exact: Rlt_trans (dlimbbN _) HinvSN.
by rewrite /eps2; fourier.
Qed. (*** W_is_open is defined ***)

Lemma bijection_complement:
forall (Xt Yt:TopologicalSpace) 
(f: (point_set Xt) -> (point_set Yt)) (U: Ensemble (point_set Xt)),
 bijective f ->
 Complement (Im U f) = Im (Complement U) f.
Proof.
move=> XT YT f U [inj_f surj_f].
apply: Extensionality_Ensembles; split => y H_y.
- case: (surj_f y) => x H.
  exists x => // In_U_x.
  apply: H_y.
  by exists x.
- case Ey0: _ / H_y => [x Hx y1 Hy1].
  case Ey1: _ / => [x0 Hx0 y2 Hy2].
  apply: Hx.
  move: Ey1.
  rewrite Hy1 Hy2.
  by move/inj_f => ->.
Qed.

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
by have ->: x=x0 by exact: H1.

pose (fP:=fun xP: {x:point_set Xt | In (Complement U) x} =>
  (exist (Complement (Im U f)) (f (proj1_sig xP)) (CImUf xP)  )).

apply (@compact_image 
        (SubspaceTopology (Complement U))
        (SubspaceTopology (Complement (Im U f)))
        fP). 

apply closed_compact.
apply Xt_compact.
red.
by rewrite Complement_Complement.
red.
move=> V V_open.
have WinY: exists W:Ensemble (point_set Yt),
  open W /\ V = inverse_image (@subspace_inc Yt (Complement (Im U f))) W.
apply subspace_topology_topology.
assumption.
destruct WinY as [W' [W'_open V_inv_W']]. 
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
   inverse_image (subspace_inc CfH)  (W (/INR (S n))).
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
have Exfh0: Inhabited (Intersection fH (open_ball (point_set CMapt) um (proj1_sig gPP) (r*/2))). 
apply closure_impl_meets_every_open_neighborhood with (proj1_sig gPP).
destruct  gPP as [gP1 IngCfH].
simpl.
by rewrite/CfH. 
apply open_ball_open.
fourier.
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
assumption.
have h_Xt: Xt = MetricTopology d d_metric by rewrite/Xt.
by rewrite<-h_Xt.
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
have IWn_dense: dense (IndexedIntersection Wn).
apply CfHt_baire.
by apply WnOD.

have InCfHfP: In CfH fP.
rewrite/CfH.
by apply closure_inflationary.
set fPP:= exist (fun gP : CMap => In CfH gP) fP InCfHfP.
set OBeps := (open_ball CMap um  fP eps). 
have WnBeps: Inhabited (Intersection (IndexedIntersection Wn) (inverse_image (subspace_inc CfH) OBeps)). 
apply dense_meets_every_nonempty_open.
by apply IWn_dense.
apply subspace_inc_continuous.
apply open_ball_open.
apply eps_pos.
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
have CImh_open: 
  open (@Complement (point_set Yt) (@Im (point_set Xt) _  Full_set h)).
apply closed_complement_open.
rewrite Complement_Complement.
apply compact_closed.
apply MetricTopology_Hausdorff.
have h_img: forall x:point_set Xt, In (Im Full_set h) (h x).
move=>x.
by apply Im_intro with x.
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
have fH_hP_r: Inhabited (
  Intersection fH (open_ball (point_set CMapt) um hP r)).  
apply closure_impl_meets_every_open_neighborhood with hP.
destruct hPP as [hP' InCfH_hP'].
simpl in hP.
rewrite/hP.
by rewrite/CfH.
apply open_ball_open.
by apply r_pos.
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

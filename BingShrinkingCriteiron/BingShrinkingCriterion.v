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

Section Topological_Lemmas.
(*** Some frequently used inequqlities ***)

(*
(* This can be proved with "auto with *". *)
Lemma pos_INR_Sn: forall n:nat, 0 < INR (S n).
Proof.
by move=> n; apply: lt_0_INR; apply: lt_0_Sn.
Qed.

(* This can be proved with "auto with *". *)
Lemma pos_inv_INR_Sn: forall n:nat, 0 < /INR (S n).
Proof.
by move=> n0; apply: Rinv_0_lt_compat; apply: pos_INR_Sn.
Qed.
*)

Lemma Rlt_inv_INR_S_contravar:
forall n m:nat, (n < m)%nat -> /INR (S m) < /INR (S n).
Proof.
move=> n m nltm.
apply: Rinv_lt_contravar; first by apply: Rmult_lt_0_compat; auto with *.
by apply: lt_INR; apply: lt_n_S.
Qed.

Lemma Rle_inv_INR_S_contravar:
forall n m:nat, (n <= m)%nat -> /INR (S m) <= /INR (S n).
Proof.
move=> n m nlem.
apply: Rinv_le_contravar; first by auto with *.
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
by exists (id_map XT) => //; apply: id_map_continuous.
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
exists dt => //.
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
pose eps := dt (xn n0) x - r.
have eps_pos: eps > 0 by apply: Rgt_minus.
case: (lim_x (open_ball T dt x eps)).
- exact: open_ball_open.
- constructor; by rewrite metric_zero.
- rewrite /= => x0 H0.
  suff: dt (xn n0) x < r + eps
    by apply: Rge_not_lt; rewrite /eps; fourier.
  pose m0 := max x0 n0.
  apply: Rle_lt_trans (_ : (dt (xn n0) (xn m0) + dt (xn m0) x) < _);
    first by apply: triangle_inequality.
  apply: Rplus_le_lt_compat (dtxn0n _ _) _; first by apply: Max.le_max_r.
  case: (H0 m0); first by apply: Max.le_max_l.
  by rewrite metric_sym.
Qed.

End Topological_Lemmas.


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
  apply: Rle_trans (_ : d' (f0 x) (y0 x)  + d' (y0 x) (g0 x) <= _);
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
  apply: Rge_trans (_ : d' (f0 x0) (g0 x0) >= _); last by case: d'_metric.
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
  apply: Rle_trans (_ : d' (f0 x2) (g0 x2) + d' (g0 x2) (h0 x2) <= _);
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
{ move=> x eps pos_eps.
  case: (cauchy_fn _ pos_eps) => [N cau_fn].
  exists N.
  move=> m n hm hn.
  apply: Rle_lt_trans (_ : um (fn m) (fn n) < _); first by apply: Rle_d'_um.
  by apply: cau_fn.
}
pose choice_R (x:X) (y:Y): Prop := net_limit (yn x) y.
have choice_f0: forall x:X, exists y:Y, (choice_R x y)
  by move=> x; apply: cpl_d'; apply: cauchy_yn.
have [f0 Hf0]: exists f0: X->Y,
  (forall x:X, choice_R x (f0 x)) by apply: choice.
have Bf0: bound (Im Full_set (fun x:X=> d' (y0 x) (f0 x))).
{ case: (cauchy_fn 1); first by apply: Rlt_0_1.
  move=> n0 Bd1.
  case: (proj2_sig (fn n0)) => [[ub Bfn0] _].
  exists (ub+1) => _ [x _ _ ->].
  apply: Rle_trans (_ : d' (y0 x) (proj1_sig (fn n0) x)
                        + d' (proj1_sig (fn n0) x) (f0 x) <= _);
    first by apply: triangle_inequality.
  apply: Rplus_le_compat.
  - apply: (Bfn0 (d' (y0 x) (proj1_sig (fn n0) x))).
    by exists x.
  - have d'um1: forall n:nat, (n >= n0)%nat ->
      d' (proj1_sig (fn n0) x) (proj1_sig (fn n) x) < 1.
    { move=> n hn.
      apply: Rle_lt_trans (_ : um (fn n0) (fn n) < _);
        first by apply: Rle_d'_um.
      by apply: Bd1.
    }
    apply: Rnot_lt_le => Fh.
    pose ep := d' (proj1_sig (fn n0) x) (f0 x) - 1.
    have hpos_ep: ep > 0 by apply: Rgt_minus.
    case: (Hf0 x (open_ball Y d' (f0 x) ep)).
    + exact: open_ball_open.
    + constructor.
      by rewrite metric_zero.
    + rewrite /= => x0 H1.
      pose m0 := max n0 x0.
      case: (H1 m0); first by apply: Max.le_max_r.
      have H3: d' (proj1_sig (fn n0) x) (yn x m0) < 1
        by apply: d'um1; apply: Max.le_max_l.
      apply: Rle_not_gt.
      rewrite metric_sym //.
      apply: Rle_move_pr2ml.
      apply: Rle_trans (_ : d' (proj1_sig (fn n0) x) (yn x m0)
                            + d' (yn x m0) (f0 x) <= _);
        first by apply: triangle_inequality.
      apply: Rlt_le.
      rewrite Rplus_comm.
      exact: Rplus_lt_compat_l.
}
have Cf0: @continuous Xt Yt f0.
{ apply: pointwise_continuity => /= x.
  apply: (metric_space_fun_continuity Xt Yt _ _ d d').
  - exact: MetricTopology_metrizable.
  - exact: MetricTopology_metrizable.
  - move=> eps eps_pos /=.
    case: (cauchy_fn (/4 * eps)); first by fourier.
    move=> N H.
    have f0fN: forall x:X,
      d' (f0 x) (proj1_sig (fn N) x) <= /4 * eps.
    { move=> x0.
      apply: Rnot_gt_le => H0.
      pose de := d' (f0 x0) (proj1_sig (fn N) x0) - /4 * eps.
      have de_pos: de > 0 by apply: Rgt_minus.
      case (Hf0 x0 (open_ball Y d' (f0 x0) de)).
      - exact: open_ball_open.
      - constructor.
        by rewrite metric_zero.
      - rewrite /= => x1 H1.
        pose N1 := max N x1.
        have f0ynx1 : d' (f0 x0) (yn x0 N1) < de
          by case: (H1 N1) => //; by apply: Max.le_max_r.
        have ynNynN1 : d' (yn x0 N1) (yn x0 N) < /4 * eps
          by apply: Rle_lt_trans (_ : um (fn N1) (fn N) < _);
             [apply: Rle_d'_um | apply: H => //; apply: Max.le_max_l].
        have: d' (f0 x0) (yn x0 N) < de + /4 * eps.
        + apply: Rle_lt_trans (_ : d' (f0 x0) (yn x0 N1)
                                   + d' (yn x0 N1) (yn x0 N) < _);
            first by apply: triangle_inequality.
          exact: Rplus_lt_compat.
        apply: Rge_not_lt.
        rewrite /de /yn.
        by fourier.
    }
    case: (proj2_sig (fn N)) => _.
    move/continuous_func_continuous_everywhere/(_ x).
    move/metric_space_fun_continuity_converse.
    case/(_ d d')/(_ _ _ (/2 * eps));
      [exact: MetricTopology_metrizable | exact: MetricTopology_metrizable |
       by fourier |].
    move=> delta [delta_pos HC].
    exists delta; split => // x' dxx'_le_delta.
    rewrite [x in _ < x](_ : eps = /4*eps + /2*eps + /4*eps); last by field.
    apply: Rle_lt_trans (_ : d' (f0 x) (proj1_sig (fn N) x')
                             + d'(proj1_sig (fn N) x') (f0 x') < _);
      first by apply: triangle_inequality.
    rewrite [d' _ (f0 x')]metric_sym //.
    apply: Rplus_lt_le_compat => //.
    apply: Rle_lt_trans
             (_ : d' (f0 x) (proj1_sig (fn N) x)
                  + d' (proj1_sig (fn N) x) (proj1_sig (fn N) x') < _);
      first by apply: triangle_inequality.
    apply: Rplus_le_lt_compat => //.
    by apply: HC.
}
exists (exist (fun g:X->Y => bound (Im Full_set
              (fun x:X=> d' (y0 x) (g x))) /\
              @continuous Xt Yt g) f0 (conj Bf0 Cf0)).
apply: (metric_space_net_limit CMapt um).
apply: MetricTopology_metrizable.
move=> eps eps_pos.
case: (cauchy_fn (/2*eps)); first by fourier.
move=> i0 H.
exists i0 => j i0j.
apply: Rle_lt_trans (_ : /2*eps < _).
- apply: Rle_um_all_d'; first by fourier.
  move=> x /=.
  rewrite -[proj1_sig (fn j) x]/((yn x) j).
  rewrite metric_sym //.
  rewrite /= in i0j.
  apply: (lim_range Y d' d'_metric (f0 x) (yn x) (/2*eps) j) => n le_j_n.
  + apply: Rle_trans (_ : um (fn j) (fn n) <= _); first by apply: Rle_d'_um.
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
pose g (y : point_set Yt) : point_set RTop := d' Y0 y.
pose ft (x : point_set Xt) : point_set RTop := g (f x).
have ft_conti: continuous ft.
{ apply: continuous_composition => //.
  apply: pointwise_continuity => y.
  apply: (metric_space_fun_continuity Yt RTop _ _ d' R_metric).
  - exact: MetricTopology_metrizable.
  - exact: RTop_metrization.
  - move=> eps eps_pos.
    exists eps; split => //.
    move=> y' d'yy'_eps.
    rewrite /R_metric /g.
    apply: Rabs_def1.
    + apply: Rlt_move_pr2ml.
      apply: Rle_lt_trans (_ : d' Y0 y + d' y y' < _);
        first by apply: triangle_inequality.
      rewrite Rplus_comm.
      exact: Rplus_lt_compat_r.
    + apply: Rlt_move_pl2mr.
      rewrite Rplus_comm.
      apply: Rlt_move_mr2pl.
      apply: Rle_lt_trans (_ : d' Y0 y' + d' y' y < _);
        first by apply: triangle_inequality.
      apply: Rplus_lt_compat_l.
      by rewrite metric_sym // Ropp_involutive.
}
apply: R_compact_subset_bounded.
have ->: Im Full_set (fun x : X => d' (y0 x) (f x)) = Im Full_set ft
  by apply: Extensionality_Ensembles; split;
     move=> _ [x _ _ ->]; exists x => //; rewrite y0Y0.
(* Require Import ContinuousFactorization. *)
(*have ft_img:
  forall x:point_set Xt, In (Im Full_set ft) (ft x).
move=>x.
by apply Im_intro with x.*)
pose ftr := continuous_surj_factorization ft.
apply: (compact_image ftr) => //.
- exact: continuous_surj_factorization_is_continuous.
- exact: continuous_surj_factorization_is_surjective.
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
{ apply: choice => n.
  have [gn Hgn]:
    Inhabited (Intersection (Complement (W r))
                            (open_ball CMap um fr (/ INR (S n)))).
  { apply: (closure_impl_meets_every_open_neighborhood _ _ fr) => //.
    - apply: open_ball_open.
      auto with *.
    - constructor.
      rewrite metric_zero; last by apply: um_metric.
      auto with *.
  }
  case: Hgn => {gn} gn CWgn [frgn].
  exists gn; split => //.
}
pose RA (k:nat) (Ak: X * X * Y * CMap): Prop :=
    (proj1_sig (snd Ak)) (fst (fst (fst Ak))) = (snd (fst Ak)) /\
    (proj1_sig (snd Ak)) (snd (fst (fst Ak))) = (snd (fst Ak)) /\
     d (fst (fst (fst Ak))) (snd (fst (fst Ak))) >= r /\
    um fr (snd Ak) < / INR (S k).
have [abcgn Habcgn]: exists Ak: nat -> X * X * Y * CMap,
   forall k:nat, (RA k (Ak k)).
{ apply: choice => k.
(********)
  pose nr := S O.
(********)
  have [ak [bk [Ck dakbk_r]]]: exists (ak bk:X),
      (proj1_sig (gn (max nr k)) ak) = (proj1_sig (gn (max nr k)) bk) /\
      d ak bk >= r.
  { apply: NNPP => Hnex.
    case: (Hgn (max nr k)).
    case=> ak bk Ck.
    apply: Rnot_ge_lt => dakbk_r.
    apply: Hnex.
    by exists ak, bk.
  }
  exists (ak, bk, (proj1_sig (gn (max nr k)) ak), (gn (max nr k))).
  repeat split=> //.
  case: (Hgn (max nr k)) => _ H0.
  apply: Rlt_le_trans (_ : / INR (S (Init.Nat.max nr k)) <= _) => //.
  apply: Rle_inv_INR_S_contravar.
  exact: Max.le_max_r.
}
pose a_net:Net nat_DS Xt:= (fun (n:nat) => fst (fst (fst (abcgn n)))).
have [lim_a H_lim_a]: exists a: point_set Xt, net_cluster_point a_net a
  by apply: compact_impl_net_cluster_point => //; apply: (inhabits O).
pose a_cond (n N:nat):=
  (n <= N)%nat /\ d lim_a (a_net N) < / INR (S n).
have [Na H_Na]: exists Na : nat -> nat, forall n, a_cond n (Na n).
{ apply: choice => n.
  case: (H_lim_a (open_ball X d lim_a (/INR (S n))) _ _ n).
  - apply: open_ball_open.
  - auto with *.
  - constructor.
    rewrite metric_zero => //.
    auto with *.
  - move=> x [H [H0]].
    by exists x.
}
pose b_net:Net nat_DS Xt := (fun (n:nat) => snd (fst (fst (abcgn (Na n))))).
have [lim_b H_lim_b]: exists b: point_set Xt, net_cluster_point b_net b
  by apply: compact_impl_net_cluster_point => //; apply: (inhabits O).
pose ab_cond (n N:nat) := (n <= N)%nat
  /\ (d lim_a (a_net (Na N)) < / INR (S n))
  /\ (d lim_b (b_net N) < / INR (S n)).
have [Nab H_Nab]: exists Nab : nat -> nat, forall n, ab_cond n (Nab n).
{ apply: choice => n.
  case: (H_lim_b (open_ball X d lim_b (/INR (S n))) _ _ n).
  - apply: open_ball_open.
  - auto with *.
  - constructor.
    rewrite metric_zero => //.
    auto with *.
  - move=> x [H [H0]].
    exists x; repeat split => //.
    apply: Rlt_le_trans (_ : /INR (S x) <= _); first by case: (H_Na x).
    exact: Rle_inv_INR_S_contravar.
}
(*******************)
pose aN (n:nat) : X :=  a_net (Na (Nab n)).
pose bN (n:nat) : X :=  b_net (Nab n).
pose cN (n:nat) : Y :=  snd (fst (abcgn (Na (Nab n)))).
pose gN (n:nat) : CMap := snd (abcgn (Na (Nab n))).
(********************)
have gNaN_cN : forall n:nat, proj1_sig (gN n) (aN n) = (cN n)
  by move=> n; case: (Habcgn (Na (Nab n))).
have gNbN_cN : forall n:nat, proj1_sig (gN n) (bN n) = (cN n)
  by move=> n; case: (Habcgn (Na (Nab n))) => _ [].
have daNbN_r : forall n:nat, d (aN n) (bN n) >= r
  by move=> n; case: (Habcgn (Na (Nab n))) => _ [_ []].
have umfrgN : forall n:nat, um fr (gN n) < / INR (S n).
{ move=> n.
  apply: Rlt_le_trans (_ : / INR (S (Na (Nab n))) <= _);
    first by case: (Habcgn (Na (Nab n))) => _ [_ []].
  apply: Rle_inv_INR_S_contravar.
  apply: le_trans (_ : (Nab n <= _)%nat); first by case: (H_Nab n).
  by case: (H_Na (Nab n)).
}
have dlimaaN: forall n:nat, d lim_a (aN n) < / INR (S n).
{ move=> n.
  apply: Rlt_le_trans (_ : / INR (S (Nab n)) <= _);
    first by case: (H_Na (Nab n)).
  apply: Rle_inv_INR_S_contravar.
  by case: (H_Nab n).
}
have dlimbbN: forall n:nat, d lim_b (bN n) < / INR (S n)
  by move=> n; case: (H_Nab n) => _ [].
have d_metrizes: metrizes Xt d
  by apply: MetricTopology_metrizable.
have d'_metrizes: metrizes Yt d'
  by apply: MetricTopology_metrizable.
have frab: (proj1_sig fr lim_a) = (proj1_sig fr lim_b).
{ apply: (metric_strict _ d') => //.
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
  pose del := Rmin dela delb.
  have [N [N_pos N_large]]:
    exists N:nat, (N > 0)%nat /\ /INR N < Rmin (/4*eps) del
    by apply: RationalsInReals.inverses_of_nats_approach_0;
       do !apply: Rmin_pos => //; fourier.
  have HinvN: / INR (S N) < / INR N.
  { apply: Rinv_lt_contravar.
    apply: Rmult_lt_0_compat; auto with *.
    exact: lt_INR.
  }
  suff: d' (proj1_sig fr lim_a) (proj1_sig fr lim_b) < eps
    by apply: Rlt_irrefl.
  rewrite (_ : eps = /4*eps + /4*eps + /4*eps + /4*eps); last by field.
  apply: Rle_lt_trans
           (_ : d' (proj1_sig fr lim_a) (proj1_sig fr (bN N))
                + d' (proj1_sig fr (bN N)) (proj1_sig fr lim_b) < _);
    first by apply: triangle_inequality.
  apply: Rplus_lt_compat; last first.
  - rewrite metric_sym //.
    apply: fr_conti_b.
    apply: Rlt_le_trans (_ : del <= _); last by apply: Rmin_r.
    apply: Rlt_le_trans (_ : Rmin (/4*eps) del <= _ ); last by apply: Rmin_r.
    apply: Rlt_trans (_ : / INR N < _) => //.
    exact: Rlt_trans (_ : / INR (S N) < _).
  apply: Rle_lt_trans
           (_ : d' (proj1_sig fr lim_a) (proj1_sig (gN N) (bN N))
                + d' (proj1_sig (gN N) (bN N)) (proj1_sig fr (bN N)) < _);
    first by apply: triangle_inequality.
  apply: Rplus_lt_compat; last first.
  - rewrite metric_sym //.
    apply: Rle_lt_trans (_ : um fr (gN N) < _); first by apply: Rle_d'_um.
    apply: Rlt_trans (_ : / INR (S N) < _) => //.
    apply: Rlt_trans (_ : / INR N < _) => //.
    apply: Rlt_le_trans (_ : Rmin (/ 4 * eps) del <= _) => //.
    exact: Rmin_l.
  apply: Rle_lt_trans
           (_ : d' (proj1_sig fr lim_a) (proj1_sig (gN N) (aN N))
                + d' (proj1_sig (gN N) (aN N)) (proj1_sig (gN N) (bN N)) < _);
    first by apply: triangle_inequality.
  rewrite gNaN_cN gNbN_cN metric_zero // Rplus_0_r.
  apply: Rle_lt_trans (_ : d' (proj1_sig fr lim_a) (proj1_sig fr (aN N))
                           + d' (proj1_sig fr (aN N)) (cN N) < _);
    first by apply: triangle_inequality.
  apply: Rplus_lt_compat.
  - apply: fr_conti_a.
    apply: Rlt_le_trans (_ : del <= _); last by apply: Rmin_l.
    apply: Rlt_le_trans (_ : Rmin (/4*eps) del <= _ ); last by apply: Rmin_r.
    apply: Rlt_trans (_ : / INR N < _) => //.
    exact: Rlt_trans (_ : / INR (S N) < _).
  - rewrite -gNaN_cN.
    apply: Rle_lt_trans (_ : um fr (gN N) < _); first by apply: Rle_d'_um.
    apply: Rlt_trans (_ : / INR (S N) < _) => //.
    apply: Rlt_trans (_ : / INR N < _) => //.
    apply: Rlt_le_trans (_ : Rmin (/ 4 * eps) del <= _) => //.
    exact: Rmin_l.
}
have dlimalimb_r: d lim_a lim_b < r
  by apply: fr_in_W.
pose eps2 := r - d lim_a lim_b.
have eps2_pos: eps2 > 0.
  by apply: Rgt_minus.
have [N [N_pos INR_e2]]: exists N:nat, (N > 0)%nat /\ / INR N < /2 * eps2.
  by apply: RationalsInReals.inverses_of_nats_approach_0; fourier.
apply: Rlt_not_ge (daNbN_r N).
have HinvSN: / INR (S N) < /2 * eps2.
{ apply: Rlt_trans (_ : / INR N < _) => //.
  apply: Rinv_lt_contravar.
  apply: Rmult_lt_0_compat; auto with *.
  exact: lt_INR.
}
rewrite (_ : r = /2 * eps2 + ((r - eps2) + /2 * eps2)); last by field.
apply: Rle_lt_trans (_ : d (aN N) lim_a + d lim_a (bN N) < _);
  first by apply: triangle_inequality.
apply: Rplus_lt_compat;
  first by rewrite (metric_sym _ d) //; apply: Rlt_trans (_ : / INR (S N) < _).
apply: Rle_lt_trans (_ : d lim_a lim_b + d lim_b (bN N) < _);
  first by apply: triangle_inequality.
apply: Rplus_le_lt_compat; last by apply: Rlt_trans (_ : / INR (S N) < _).
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
move=> Xt_compact Yt_compact Xt_Hdf Yt_Hdf f f_bijective f_continuous.
apply: invertible_open_map_is_homeomorphism => //;
  first by apply: bijective_impl_invertible.
move=> U U_open.
apply: closed_complement_open => //.
apply: compact_closed => //.
have CImUf: forall xP : {x: point_set Xt | In (Complement U) x},
    Complement (Im U f) (f (proj1_sig xP)).
{ move=> [x Hx].
  rewrite bijection_complement //.
  by exists x.
}
pose fP (xP: {x:point_set Xt | In (Complement U) x}) :=
  exist (Complement (Im U f)) (f (proj1_sig xP)) (CImUf xP).
apply: (@compact_image
          (SubspaceTopology (Complement U))
          (SubspaceTopology (Complement (Im U f)))
          fP).
- apply: closed_compact; first by apply: Xt_compact.
  by rewrite /= Complement_Complement.
- move=> V V_open.
  have [W' [W'_open V_inv_W']]: exists W:Ensemble (point_set Yt),
      open W /\ V = inverse_image (@subspace_inc Yt (Complement (Im U f))) W
    by apply: subspace_topology_topology.
  have ->: inverse_image fP V =
           inverse_image (@subspace_inc Xt (Complement U))
                         (inverse_image f W')
    by apply: Extensionality_Ensembles; split; rewrite V_inv_W' => [? [[]]].
  apply: subspace_inc_continuous.
  exact: f_continuous.
- case: f_bijective => f_inj f_surj.
  move=> [y0' Hy0'].
  case: (f_surj y0') => x0 H.
  rewrite/fP.
  have InCUx0: In (Complement U) x0
    by move=> InUx0; apply: Hy0'; exists x0.
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
move=> f f_conti f_surj f_BS eps eps_pos.
have f_bdd_conti: bound (Im Full_set (fun x:X=> d' (y0 x) (f x)))/\
                           @continuous Xt Yt f
  by split =>//; apply: continuous_bounded.
pose fP := exist (fun f: X->Y => bound (Im Full_set (fun x:X=> d' (y0 x) (f x)))
                                 /\ @continuous Xt Yt f) f f_bdd_conti.
pose fH : Ensemble (point_set CMapt) :=
  fun gP: CMap => exists hx: point_set Xt -> point_set Xt,
                  homeomorphism hx /\
                  forall x: point_set Xt, (proj1_sig gP) x = f (hx x).
have InfHfP: In fH fP
  by exists (id_map Xt); split=>//; apply: id_map_homeomorphism.
pose CfH := closure fH.
pose CfHt := SubspaceTopology CfH.
(* Caution: point_set CfHt = { gP:CfH | In CfH gP } *)
pose um_restriction (f1PP f2PP: point_set CfHt) :=
  um (proj1_sig f1PP) (proj1_sig f2PP).
have um_restriction_metric: metric um_restriction
  by apply: d_restriction_metric; apply: um_metric.
have CfHt_baire: baire_space CfHt.
{ apply: (BaireCategoryTheorem _ um_restriction) => //;
    first by exact: d_restriction_metrizes.
  have um_is_metric: metric um by apply: um_metric.
  have um_is_complete: complete um um_metric
    by apply: um_complete; apply: compact_complete; exact: Y_compact.
  apply: closed_subset_of_complete_is_complete => //.
  exact: closure_closed.
}
pose Wn: IndexedFamily nat (point_set CfHt) :=
  fun n:nat => inverse_image (subspace_inc CfH)  (W (/INR (S n))).
have WnOD: forall n:nat, open (Wn n) /\ dense (Wn n).
{ move=>n; split;
    first by apply: subspace_inc_continuous; apply: W_is_open; auto with *.
(********************************************)
  apply: meets_every_nonempty_open_impl_dense.
  move=> U U_open [gPP InUgPP].
  case: (subspace_topology_topology _ _ U) => // V [V_open U_iV].
  have [r [r_pos IcOB_V]]: exists r:R, r>0 /\
    Included (open_ball (point_set CMapt) um (proj1_sig gPP) r) V
    by apply: open_ball_in_open; move: InUgPP; by rewrite U_iV => -[].
  have [fh0 h1_fh0]: Inhabited (Intersection fH (open_ball (point_set CMapt) um (proj1_sig gPP) (r*/2))).
  { apply: (closure_impl_meets_every_open_neighborhood _ _ (proj1_sig gPP)).
    - by case: (gPP).
    - by apply: open_ball_open; fourier.
    - constructor.
      have ->: um (proj1_sig gPP) (proj1_sig gPP) = 0
        by apply: metric_zero; apply: um_metric.
      by fourier.
  }
  case: h1_fh0 => {fh0} fh0 [h0 [[h' h0_conti h'_conti h_h'h0 h_h0h'] h_fh0]] [umgPfh0].
  pose eps1 := Rmin (r*/2) (/ INR (S n)).
  have [delta [pos_delta h_delta]]: exists delta:R, delta > 0 /\
    forall x1 x2 : X, d x1 x2 < delta -> d (h' x1) (h' x2) < eps1.
  { apply: dist_uniform_on_compact => //.
    apply: Rmin_pos; by [fourier | auto with *].
  }
  case: (f_BS (Rmin delta (r*/2))); first by apply: Rmin_pos => //; fourier.
  move=> k [[k' k_conti k'_conti h_k'k h_kk'] [h1_k h2_k]].
  pose k'h (x: point_set Xt) := k' (h0 x).
  pose h'k (x: point_set Xt) := h' (k x).
  pose fk'h (x: point_set Xt) := f (k'h x).
  have k'h_homeo: homeomorphism k'h.
  { exists h'k.
    - exact: continuous_composition.
    - exact: continuous_composition.
    - by move=> x; rewrite /h'k /k'h h_kk' h_h'h0.
    - by move=> x; rewrite /k'h /h'k h_h0h' h_k'k.
  }
  have fk'h_conti: continuous fk'h
    by apply: continuous_composition => //; exact: continuous_composition.
  have fk'h_bdd_conti:
    bound (Im Full_set (fun x:X => d' (y0 x) (fk'h x))) /\
    continuous fk'h
  by split=> //; exact: continuous_bounded.
  pose fk'hP := exist
        (fun f: X->Y => bound (Im Full_set (fun x:X=> d' (y0 x) (f x)))/\
                        @continuous Xt Yt f) fk'h fk'h_bdd_conti.
  have InCfHfk'hP: In CfH fk'hP
    by apply: closure_inflationary; exists k'h; split.
  pose fk'hPP := exist (fun f0P: point_set CMapt => In CfH f0P) fk'hP InCfHfk'hP.
  exists fk'hPP; split.
  - constructor => x1 x2 fk'hx1_fk'hx2.
    rewrite /= /fk'h in fk'hx1_fk'hx2.
    have: d (k (k'h x1)) (k (k'h x2)) < delta
      by apply: Rlt_le_trans (_ : Rmin delta (r * / 2) <= _);
         [apply: h2_k | apply: Rmin_l].
    rewrite /k'h !h_kk' => /h_delta.
    rewrite !h_h'h0 => /Rlt_le_trans.
    apply.
    apply: Rmin_r.
  - rewrite U_iV.
    constructor.
    rewrite /fk'hPP /=.
    apply: IcOB_V.
    constructor.
    apply: Rle_lt_trans (_ : um (proj1_sig gPP) fh0 + um fh0 fk'hP < _);
      first by apply: triangle_inequality; by apply: um_metric.
    rewrite (_ : r = r * /2 + r* /2); last by field.
    apply: Rplus_lt_le_compat => //.
    apply: Rle_um_all_d'; first by fourier.
    move=> x.
    rewrite h_fh0 /= /fk'h /k'h -[X in d' (f X)]h_kk' metric_sym //.
    apply: Rlt_le.
    apply: Rlt_le_trans (_ : Rmin delta (r * / 2) <= _); first by apply: h1_k.
    exact: Rmin_r.
}
have IWn_dense: dense (IndexedIntersection Wn)
  by apply: CfHt_baire; apply: WnOD.
have InCfHfP: In CfH fP.
  by apply: closure_inflationary.
pose fPP := exist (fun gP : CMap => In CfH gP) fP InCfHfP.
pose OBeps := open_ball CMap um fP eps.
have [hPP H_h]: Inhabited (Intersection (IndexedIntersection Wn) (inverse_image (subspace_inc CfH) OBeps)).
{ apply: dense_meets_every_nonempty_open.
  - exact: IWn_dense.
  - apply: subspace_inc_continuous.
    exact: open_ball_open.
  - exists fPP.
    constructor.
    constructor.
    rewrite metric_zero //.
    exact: um_metric.
}
case: H_h => {hPP} _ [hPP Wn_h] [OB_h].
(***)
pose hP := proj1_sig hPP.
pose h := proj1_sig hP.
case: (proj2_sig hP) => _.
rewrite -/h => c_h.
move: OB_h.
rewrite /subspace_inc -/hP => -[umfh].
exists h.
split.
apply: bij_conti_is_homeo_for_compact_Hausdorff_spaces => //.
- exact: MetricTopology_Hausdorff.
- exact: MetricTopology_Hausdorff.
- split.
  + move=> x1 x2 hx1_hx2.
    apply: (metric_strict _ d) => //.
    apply: Rle_antisym; last by apply: Rge_le; apply: metric_nonneg.
    apply: Rnot_gt_le => H.
    case: (inverses_of_nats_approach_0 (d x1 x2)) => // n [n_pos].
    apply: Rle_not_gt.
    case: (Wn_h n).
    rewrite /W /In /subspace_inc -/hP -/h => h_Wn.
    apply: Rlt_le.
    apply: Rlt_trans (_ : / INR (S n) < _); first by apply: h_Wn.
    apply: Rinv_lt_contravar.
    apply: Rmult_lt_0_compat; auto with *.
    exact: lt_INR.
  + move=> y.
    apply: NNPP => h_nx.
    have InCImhy: In (Complement (Im Full_set h)) y.
    { case E: _ / => [x InXx y' y_hx].
      apply: h_nx.
      exists x.
      by rewrite E y_hx.
    }
    have CImh_open: open (@Complement (point_set Yt) (Im Full_set h)).
    { apply: closed_complement_open.
      rewrite Complement_Complement.
      apply: compact_closed; first by apply: MetricTopology_Hausdorff.
      have h_img: forall x:point_set Xt, In (Im Full_set h) (h x)
        by move=>x; exists x.
      pose hf := @continuous_factorization Xt Yt h (Im Full_set h) h_img.
      apply: (compact_image hf) => //;
        first by apply: factorization_is_continuous.
      case=> _ [x1 InF_x y1 y1_hx1].
      exists x1.
      exact: subset_eq_compatT.
    }
(*******************************)
    have [r [r_pos IncObCImh]]: exists r:R, r > 0 /\
      Included (open_ball (point_set Yt) d' y r) (Complement (Im Full_set h))
      by apply: open_ball_in_open.
    have fH_hP_r: Inhabited (
                    Intersection fH (open_ball (point_set CMapt) um hP r)).
    { apply: (closure_impl_meets_every_open_neighborhood _ _ hP).
      - rewrite /hP.
        by case: (proj2_sig hPP).
      - exact: open_ball_open.
      - constructor.
        rewrite metric_zero //.
        by apply: um_metric.
    }
    case: fH_hP_r => _ [fh1 [h1 [h1_homeo fh1_f_h1]] [umhPfh1_r]].
    have [x1 y_fh1x1]: exists x1:point_set Xt, y = f (h1 x1).
    { case: h1_homeo => h1' h1_cont h1'_cont h1'h1 h1h1'.
      case: (f_surj y) => x2 fx2_y.
      exists (h1' x2).
      by rewrite h1h1'.
    }
    have InObyr_hx1: In (open_ball (point_set Yt) d' y r) (h x1).
    { constructor.
      rewrite /h y_fh1x1 -fh1_f_h1 metric_sym //.
      apply: Rle_lt_trans (_ : um hP fh1 < _) => //.
      exact: Rle_d'_um.
    }
    have: In (Complement (Im Full_set h)) (h x1)
      by apply: IncObCImh.
    apply.
    by exists x1.
- move=> x.
  rewrite -[f]/(proj1_sig fP) /h.
  apply: Rle_lt_trans (_ : um fP hP < _) => //.
  exact: Rle_d'_um.
Qed. (*  Bing_Shrinking_Theorem *)

End BingShrinkingTheorem.

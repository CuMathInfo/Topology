Require Import Classical_Prop Classical_Pred_Type.
Require Import IndefiniteDescription ChoiceFacts.
From mathcomp
Require Import ssreflect ssrbool.
From Topology
Require Import MetricSpaces SubspaceTopology
ContinuousFactorization Homeomorphisms Compactness.

(******** eqProp *******)
Lemma cddo : forall T : Type, ConstructiveDefiniteDescription_on T.
Proof.
move=>T P E1xTPx. 
apply: (constructive_indefinite_description _).
case : E1xTPx => x [hPx Ax'Px_xx'].
  by exists x.
Qed.      

Lemma eqProp : forall P : Prop, {P} + {~P}.
Proof.
apply: (constructive_definite_descr_excluded_middle cddo) => P.  
exact: (classic P).
Qed.

(********************)
Open Scope R_scope.


Module Cellularity.
  Variable X Y : TopologicalSpace.
  
  Definition top_to_type (T : TopologicalSpace) : Type := point_set T.

  Local Coercion top_to_type : TopologicalSpace >-> Sortclass.  
(*** Preliminary Lemmas ***)
  Lemma Im_compat_Included {U V : Type} (A B : Ensemble U) (f : U -> V) :
    Included A B -> Included (Im A f) (Im B f).
  Proof.
    move => IncAB y InImAfy.
    have [x [InAx fx_y]] : exists x : U, In A x /\ f x = y by apply Im_inv in InImAfy.
    have InBx : In B x by apply (IncAB x).
      by apply (Im_intro _ _ B f x).
  Qed.

  Lemma ponnq_poq (p q : Prop) : p \/ (~ ~ q) -> p \/ q.
  Proof.
  case=> H.
    by apply: or_introl.
  apply NNPP in H.
    by apply or_intror.
  Qed.

  Lemma id_homeo : homeomorphism (fun x : X => x).
  Proof.
    exists (fun x : X => x).
    apply continuous_identity.
    apply continuous_identity.
    trivial.
    trivial.
  Qed.

  Lemma homeo_is_bijective : forall {Xt Yt : TopologicalSpace} (f : Xt -> Yt),
                       homeomorphism f -> bijective f.
  Proof.
  move=>X Y f [g _ _ gf_I fg_I].
  split.
  move => x1 x2 fx1fx2.
  have gfx1_gfx2 : g (f x1) = g (f x2) by rewrite fx1fx2.  
   by repeat rewrite gf_I in gfx1_gfx2.
   move=>y.
   exists (g y).
     by apply fg_I.
  Qed.

  Lemma Im_Complement_comm_for_bijection : forall {A B : Type} (f : A -> B) (D : Ensemble A),
       bijective f -> Complement (Im D f) = Im (Complement D) f.

  Proof.
  move => A B f D f_bij.
  case : f_bij => f_inj f_surj.  
  apply Extensionality_Ensembles.
  split.
  move=> y InCfDy.
  Print surjective. 
  have [x fx_y] : exists x : A, f x = y by apply (f_surj y).
  rewrite  -fx_y.
  suff InCDx : In (Complement D) x by apply (Im_intro _ _ (Complement D) f x InCDx).
  move=> InDx.
  have InfDy : In (Im D f) y.
  rewrite -fx_y.
    by apply (Im_intro _ _ D f x InDx).
  by apply (InCfDy InfDy). 
  move => x InfCDx.
  case : InfCDx => x0 InCDx0 y y_fx0 InfDy.
  destruct InfDy as [x1 InDx1 y1]. 
  rewrite H in y_fx0.
  have x1_x0 : x1 = x0 by apply (f_inj _ _ y_fx0).
  rewrite x1_x0 in InDx1.
    by apply (InCDx0 InDx1).
  Qed.

  
  Lemma homeo_maps_closed_to_closed :
    forall {X1 Y1 : TopologicalSpace} (h : X1 -> Y1) (F : Ensemble X1),
      homeomorphism h -> closed F -> closed (Im F h).
  Proof.
    move=> X1 Y1 h F h_homeo F_closed.
    red.
    rewrite Im_Complement_comm_for_bijection.
    by apply homeomorphism_is_open_map.
      by apply homeo_is_bijective.
  Qed.  
    
  (*** End Preliminary Lemmas ***)
  
  (*** We use the following form of Axiom of Choice ****)
Axiom FDC : FunctionalDependentChoice_on ({h : X -> X | homeomorphism h} * nat).
(******)

  
Definition abstract_cell (D : Ensemble X) : Prop :=
  Inhabited (interior D) /\ closed D /\
  forall (x : X) (U : Ensemble X), open U -> In U x -> Included U D -> 
      exists h : X -> X, homeomorphism h /\ h x = x /\
         Included (Im D h) U /\
         (forall y : X, In (Complement D) y -> h y = y).

(** homeo_image of abstract_cell is abstract_cell **)
(** i.e., abstract_cell is invariant under ambient homeomorphism **)

Lemma homeo_image_abstract_cell (D : Ensemble X) (h : X -> X) :
  abstract_cell D -> homeomorphism h -> abstract_cell (Im D h). 
Proof.
  move=> [IniD [D_closed D_acell]] h_homeo. 
    case : IniD => x IniDx. case : IniDx => U0 x0 HU0 InU0x0.
    case : HU0 => HU0. move: HU0 => [U0_open IncU0D]. split.
exists (h x0).
exists (Im U0 h).
constructor; split.
apply homeomorphism_is_open_map.
assumption.
assumption.
move=>x1 InImU0x1.
case:InImU0x1 => x2 InU0x2 y y_hx2.
exists x2.
  by apply IncU0D.
  assumption.
    by apply (Im_intro _ _ U0 h x0 InU0x0).
    split.
by apply homeo_maps_closed_to_closed.
move=>x1 U U_open InUx1 IncUImDh.    
case : h_homeo=>[g] h_conti g_conti gh_I hg_I.
have gU_open : open (Im U g).
apply homeomorphism_is_open_map.
apply: (intro_homeomorphism _ h g_conti h_conti  hg_I gh_I).
assumption. 
have IngUgx1 : In (Im U g) (g x1) by apply (@Im_intro X X U g x1 InUx1).
have IncgUD : Included (Im U g) D .
move=>z InImUgz. case : InImUgz =>x2 InUx2 w w_gx2. rewrite w_gx2.
have InhDx2 : In (Im D h) x2 by apply IncUImDh.
case : InhDx2 => x3 InDx3 y1 y1_x3. rewrite y1_x3.
by rewrite  gh_I.
have [h1 [h1_homeo [h1gx1_gx1 [IncIDh1IUg HCompl]]]] :
  exists h1 : X -> X, homeomorphism h1 /\ h1 (g x1) = (g x1) /\ Included (Im D h1) (Im U g) /\
  (forall y : X, In (Complement D) y -> h1 y = y)  by apply  (D_acell (g x1) (Im U g) gU_open IngUgx1 IncgUD).
pose h0 := fun (x : X) => h (h1 (g x)).
exists h0.
case h1_homeo => [g1] h1_conti g1_conti g1h1_I h1g1_I.
split.
pose g0 := fun (x:X) => h (g1 (g x)).
have g0_conti : continuous g0.
apply continuous_composition.
rewrite/g0.
apply continuous_composition.
assumption.
by apply continuous_composition.
apply continuous_identity.
have h0_conti : continuous h0.
rewrite/h0.
apply continuous_composition.
assumption.
apply continuous_composition.
assumption.
assumption.
have h0g0_I : forall x : X, h0 (g0 x) = x.
rewrite/h0 /g0.
move=> x2.
by rewrite gh_I h1g1_I hg_I.
have g0h0_I : forall x : X, g0 (h0 x) = x.
rewrite/h0 /g0.
move=> x2.
by rewrite gh_I g1h1_I hg_I.
by apply: (intro_homeomorphism _ g0 h0_conti g0_conti  g0h0_I h0g0_I).
split.
by rewrite/h0 h1gx1_gx1 hg_I.
split.
move=>w Inh0hDw.
case : Inh0hDw  => x2 InhDx2 y y_h0x2.
rewrite y_h0x2 /h0; clear w.
have  IngUh1gx2 : In (Im U g) (h1 (g x2)).
case: InhDx2=> x3 InDx3 y0 y0_hx3.
rewrite y0_hx3 gh_I; clear y0_hx3 y0  y_h0x2 x2 y.
apply IncIDh1IUg.
by exists x3.
case : IngUh1gx2 => x4 InUx4 w w_gx4.
by rewrite w_gx4  hg_I.
move=>y InChDy.
rewrite/ h0.
have InCDgy : In (Complement D) (g y).
suff Dgy_hDy : D (g y) -> (Im D h) y.
move=> Dgy.
repeat red in InChDy.
apply InChDy.
by apply Dgy_hDy.
move=>Dgy.
  by exists (g y).
have h1gy_gy : h1 (g y) = (g y) by apply (HCompl (g y) InCDgy).             
by rewrite h1gy_gy  hg_I.
Qed.
 

Definition abstract_cellular (K : Ensemble X) : Prop :=
  exists D : IndexedFamily nat X,
    (forall n : nat, abstract_cell (D n) /\  Included (D (S n)) (interior (D n)) ) /\
    IndexedIntersection D = K.

Definition point_cellular (D : Ensemble X)
  := forall x : X, In D x -> abstract_cellular (Singleton x).
  
Section Shrinking_cellular_Maps.

  Hypothesis X_point_cellular : point_cellular  Full_set.

  Lemma Cellular_with_one_sing_shrinkable (f : X -> Y) :
  surjective f ->
  forall y0 : Y, (forall x1 x2 : X,  f x1 = f x2 -> f x1 <> y0 -> x1 = x2)
                  /\ abstract_cellular (inverse_image f (Singleton y0))
  -> forall V : Ensemble Y, In V y0 -> open V ->
                            exists h : X -> Y, homeomorphism h /\
                                               (forall x : X, In (Complement V) (f x) -> h x = f x ). 
  Proof.
  move=> f_surj y0 [H_inj H_cell] V InVy0 Vopen.
  have [x0] : exists x0, (f x0) = y0  by apply f_surj. 
  have [Dn [Hn Hint]] : exists Dn : IndexedFamily nat X,
    (forall n : nat, abstract_cell (Dn n) /\  Included (Dn (S n)) (interior (Dn n)) ) /\
    IndexedIntersection Dn = Singleton x0 by apply (X_point_cellular x0).
  move=> fx0y0.
  have [En [Kn Kint]] : exists En : IndexedFamily nat X,
    (forall n : nat, abstract_cell (En n) /\ Included (En (S n)) (interior (En n)) ) /\
    IndexedIntersection En = (inverse_image f (Singleton y0)) by apply H_cell.                 
  
  pose IStep (kn kn' : {h : X->X | homeomorphism h} * nat) : Prop := (proj1_sig (fst kn)) x0 = x0 ->
    (proj1_sig (fst kn')) x0 = x0  /\  (snd kn') = S (snd kn) /\
    (forall x : X, In (Complement (En (snd kn))) x -> (proj1_sig (fst kn)) x = (proj1_sig (fst kn')) x) /\
    Included (Im (En (snd kn')) (proj1_sig (fst kn'))) (Dn (snd kn')).
  
  have IChoice : forall kn : {h:X->X | homeomorphism h} * nat, exists kn' :  {h:X->X | homeomorphism h} * nat, IStep kn kn'.
  move=> [[hn hn_homeo] n].
(* em *)
  have exc_middle := classic (hn x0 = x0).
  case : exc_middle.
(* hn x0 = x0 case *)
move => hnx0_x0.  
  have acellhnEn : abstract_cell (Im (En n) hn).
  apply homeo_image_abstract_cell.
  case : (Kn n) => [acell_En IncEn'intEn].
  exact acell_En.
  exact hn_homeo.
  case : acellhnEn => InhInthnEn [clImEnhn Exh].
  set U := Intersection (interior (Im (En n) hn)) (interior (Dn (S n))).
  have U_open : open U.
  rewrite /U - interior_intersection.
  apply interior_open.
  have InUx0 : In U x0.
  apply Intersection_intro.
  have Infinvy0_x0 : In (inverse_image f (Singleton y0)) x0.
  constructor.
    by rewrite fx0y0.
    have InEnsx0 : In (IndexedIntersection En) x0 by rewrite Kint.
    have InEn'x0 : In (En (S n)) x0.
    case : InEnsx0 => x InAx.
      by apply (InAx (S n)).
      have InintEnx0 : In (interior (En n)) x0.
case : (Kn n) => Enn_acell EnEn'.
by apply EnEn'.
have InhnEnx0 : In (En n) x0 by apply (interior_deflationary (En n)).  
have InImEnhnx0 : In (Im (En n) hn) x0 by apply (Im_intro _ _ (En n) hn x0).
have InIminEnhx0 : In (Im (interior (En n)) hn) (hn x0) by apply (Im_intro _ _ (interior (En n)) hn x0).
have IncImintEhImEh : Included (Im (interior (En n)) hn) (Im (En n) hn).
move=> t Init.
case : Init => t1 Inint1 t2 t2_hnt2.
rewrite t2_hnt2; clear t2 t2_hnt2.
have InEnt1 : In (En n) t1.
by apply interior_deflationary.
  by apply (Im_intro _ _ (En n) hn t1).

rewrite hnx0_x0 in InIminEnhx0.
have IminEn_open : open (Im (interior (En n)) hn).

apply homeomorphism_is_open_map.
assumption.
apply interior_open.
Print interior_maximal.
have Inc_ohn_homeo_int : Included (Im (interior (En n)) hn) (interior (Im (En n) hn)).
apply interior_maximal. 
assumption.
assumption.
have IncliIEIE : Included (Im (interior (En n)) hn) (interior (Im (En n) hn)).
apply (interior_maximal _ _ IminEn_open).
assumption.
by apply (IncliIEIE _ InIminEnhx0).
case : (Hn (S n)) => _ IncDSSniDSn.
apply IncDSSniDSn.
have IncIIDn_Dn : Included (IndexedIntersection Dn) (Dn (S (S n))).
move => t InIIDnt.
by case : InIIDnt.
rewrite Hint in IncIIDn_Dn.
by apply IncIIDn_Dn.
have IncUImEnnhn : Included U (Im (En n) hn).  
rewrite/U.
move=> t  InIntEDt.
suff InintImEnt : In (interior (Im (En n) hn)) t.
  by apply (interior_deflationary  (Im (En n) hn)).
  have In_and_In: (In (interior (Im (En n) hn)) t) /\ (In (interior (Dn (S n))) t) by apply: Intersection_inv. 
by case : InIntEDt =>x IniE _.

have [h [h_homeo [hx0_x0 [InchhnEnU HComp]]]] :  exists h: X -> X, homeomorphism h /\ (h x0) = x0 /\
            Included (Im (Im (En n) hn) h) U  /\ (forall y : X, In (Complement (Im (En n) hn)) y -> h y = y)
                                          by apply (Exh x0  U U_open InUx0 IncUImEnnhn).

(* construction of kn' *)
pose n' := (S n).
pose hn' := fun (x : X) => h (hn x).

case h_homeo => [g] h_conti g_conti gh_I hg_I.
case hn_homeo => [gn] hn_conti gn_conti gnhn_I hngn_I.
pose gn' := fun(x : X) => gn (g x).
have gn'hn'_I : forall x, gn' (hn' x) = x.
move=> x.
  by rewrite /hn' /gn' gh_I gnhn_I.
have hn'gn'_I : forall x, hn' (gn' x) = x.
move=> x.
  by rewrite /gn' /hn' hngn_I hg_I.
have hn'_conti : continuous hn' by apply (continuous_composition h hn h_conti hn_conti).
have gn'_conti : continuous gn' by apply (continuous_composition gn g gn_conti g_conti).
have hn'_homeo : homeomorphism hn' by apply (intro_homeomorphism _ gn' hn'_conti gn'_conti gn'hn'_I hn'gn'_I).  
pose kn' := (exist _ hn' hn'_homeo, n') : {k0 : X -> X | homeomorphism k0} * nat. 
exists kn'.
split.
simpl.
  by rewrite /hn' hnx0_x0 hx0_x0.
split.
  by [].
split.  
simpl.
move=> x InCEnnx.
rewrite /hn'.
have InCIEhnx : In (Complement (Im (En n) hn)) (hn x).
move=> InImEhnx.
have [x1 [InEx1 hnx1_hnx]] : exists x1 : X, In (En n) x1 /\ (hn x1) = (hn x) by apply Im_inv.
have x1_x : gn (hn x1) = gn (hn x) by rewrite hnx1_hnx.
repeat rewrite gnhn_I in x1_x.
  by rewrite x1_x in InEx1.
apply eq_sym.
  by apply HComp.
simpl.
have Imhn'_ImImhnh : Im (En n') hn' = Im (Im (En n') hn) h.
apply Extensionality_Ensembles; split.
move=> x InImEn'hn'x.
have [x1 [InEn'x1 hn'x1_x]] : exists x1 : X, In (En n') x1 /\ hn' x1 = x by apply Im_inv in InImEn'hn'x.
rewrite/hn' in hn'x1_x.
have InImEn'hnhnx1 : In (Im (En n') hn) (hn x1) by apply (Im_intro _ _ (En n') hn x1 InEn'x1).
  by apply (Im_intro _ _ (Im (En n') hn) h (hn x1)).
  move=> x InIIE'hnhx.
have [x1 [InImEn'hnx1 hx1_x]] : exists x1 : X, In (Im (En n') hn) x1 /\ h x1 = x by apply Im_inv in InIIE'hnhx.
have [x2 [InEn'x2 hnx2_x1]] : exists x2 : X, In (En n') x2  /\ hn x2 = x1 by  apply Im_inv in InImEn'hnx1.
apply (Im_intro _ _ (En n') hn' x2).
assumption.
by rewrite/hn' hnx2_x1.
rewrite Imhn'_ImImhnh.
SearchAbout Im.
rewrite/hn'. have Intmed : forall (y : X), In (Im (En n) hn) y -> exists z : X, In (En n) z /\ hn z = y. 
move=>y. by apply (Im_inv (En n) hn y).
have : Included (Im (Im (En n') hn) h) (Im (Im (En n) hn) h).
repeat apply Im_compat_Included.
rewrite/n'.
apply Inclusion_is_transitive with (interior (En n)).
by apply (proj2 (Kn n)).
by apply interior_deflationary.
move => IncIIEn'hnhIIEnhnh.
apply Inclusion_is_transitive with (Im (Im (En n) hn) h).
assumption.
apply Inclusion_is_transitive with U.
assumption.
rewrite/U.
apply Inclusion_is_transitive with (interior (Dn (S n))).
  by apply Intersection_decreases_r.
rewrite/n'.
  by apply interior_deflationary.
move=> hnx0_n_x0.
(* hn x0 <> x0 case *)
exists ((exist _ hn hn_homeo), (S n)).
move=> hnx0_x0.
by simpl in hnx0_x0.

(*** apply FDC **)

pose k0 := ((exist _ (fun x : X => x) id_homeo), O).
have [kn] : exists kn : nat -> {h : X -> X | homeomorphism h} * nat,
            (kn O) = k0 /\ (forall n : nat, IStep (kn n) (kn (S n))) by apply FDC.
(*****)

have x_to_n : forall x : X, In (En O) x -> f x <> y0 ->
                     exists n : nat, In (En n) x /\ ~ In (En (S n)) x. 
move=> x InE0x fxny0.
apply not_all_not_ex.
move=> nEnEn'.


have nEniEn' : forall n : nat, In (En n) x -> In (En (S n)) x.
move=>n.
apply or_to_imply.
apply ponnq_poq.
apply not_and_or.
apply nEnEn'.
clear nEnEn'.
have AnInEnx : forall n : nat, In (En n) x.
induction n.
assumption.
  by apply: nEniEn'.
  clear nEniEn'.
have InKx : In (inverse_image f (Singleton y0)) x.
rewrite  -Kint.
by apply indexed_intersection_intro.
case: InKx => InSy0fx.
apply Singleton_inv in InSy0fx.
apply eq_sym in InSy0fx.
by apply (fxny0 InSy0fx). 
move => [kn0_k0 AnISpknkn'].
Print uniqueness.
pose DefRelh (x : X) (y : Y) := (x = x0 /\ y = y0) \/ (In (Complement (Im ((En 1) x /\ y = f x)
                                                          \/ (exists n : nat, In (Intersection 
                  
move: (Intmed (hn x)). InImEhnx).
case InImEhnx. => x1 InEnx1 y y_hnx1.
pose hn' := fun (x : X) => match (eqProp ((En n) x)) with
                             | left _ => h (hn x) 
                             | right _ => hn x
                           end.
exists (exist hn' (S n)).
  Print FunctionalDependentChoice_on.
have em : homeomorphism (fst kn) \/ ~ homeomorphism (fst kn) by apply (classic _).
pose Tn := {kn : nat * (X->X) | (homeomorphism (snd kn)) /\ Included (Im (D'n (fst kn)) (snd kn)) (interior (Dn (fst kn)))}.
Check Tn.
Check (FunctionalDependentChoice_on Tn).
  pose IStep (kn kn' : Tn) : Prop := 
    forall x : X, In (Complement (D'n (fst (proj1_sig kn)))) x  -> (snd (proj1_sig kn)) x = (snd (proj1_sig kn')) x.
                   

End Shrinking_cellular_Maps.

Proof.
move=> y0 [Hi Hc] V InVy0 openV.  
                                                                      
                    
End Cellularity.

Section Def_rs_shrinkable.

  Variable X : TopologicalSpace.
  Variable B : Ensemble (point_set X).
  Hypothesis B_closed : closed B.
  Variable x : point_set X.

  (* s_shrinkable = stably shrinkable *)
  Definition s_shrinkable : Prop :=
    forall U: Ensemble (point_set X),
      open U -> In U x ->
      exists h : (point_set X) -> (point_set X),
        closed (Im B h) /\ open (Im (Complement B) h) /\
        exists V : Ensemble (point_set X),
          continuous h /\ Included (Im Full_set h) U /\
          homeomorphism (continuous_surj_factorization h) /\
          open V /\ In V x /\
          forall y : point_set X, In V y -> h y = y.

  (* r_shrinkable = relatively shrinkable *)
  Definition r_shrinkable : Prop :=
    forall (K U : Ensemble (point_set X)),
      compact (SubspaceTopology K) -> open U ->
      Intersection K B = Empty_set -> In U x ->
      exists h : point_set X -> point_set X, homeomorphism h /\ Included (Im Full_set h) U /\
                         forall b : point_set X, In B b -> (h b) = b.

End Def_rs_shrinkable.
  
Definition abstract_cell (D : TopologicalSpace) (B : Ensemble (point_set D)) : Prop :=
  forall x : point_set D, s_shrinkable D B x /\ r_shrinkable D B x.

Definition abstract_cellular (X : TopologicalSpace) (K : Ensemble (point_set X)) : Prop :=
  exists Dn : IndexedFamily nat (point_set X),
    exists Bn : IndexedFamily nat (point_set X),
      forall n : nat, 
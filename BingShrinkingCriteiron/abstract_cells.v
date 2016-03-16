From mathcomp
Require Import ssreflect ssrbool.
From Topology
Require Import MetricSpaces SubspaceTopology
     ContinuousFactorization Homeomorphisms Compactness.
Open Scope R_scope.

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

Require Export com. Import ImpNotations.
Require Export state. Import StateNotations.
Require Export aexp.
Require Export bexp.

From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Lia.

Inductive aval : aexp -> Prop :=
  | av_num : forall n, aval (ANum n).

Inductive astep (st : state) : aexp -> aexp -> Prop :=
  | AS_Id : forall (i : string),
      astep st i (st i)
  | AS_Plus1 : forall a1 a1' a2,
      astep st a1 a1' ->
      astep st <{ a1 + a2 }> <{ a1' + a2 }>
  | AS_Plus2 : forall v1 a2 a2',
      aval v1 ->
      astep st a2 a2' ->
      astep st <{ v1 + a2 }> <{ v1 + a2' }>
  | AS_Plus : forall (n1 n2 : nat),
      astep st <{ n1 + n2 }> (n1 + n2)
  | AS_Minus1 : forall a1 a1' a2,
      astep st a1 a1' ->
      astep st <{ a1 - a2 }> <{ a1' - a2 }>
  | AS_Minus2 : forall v1 a2 a2',
      aval v1 ->
      astep st a2 a2' ->
      astep st <{ v1 - a2 }> <{ v1 - a2' }>
  | AS_Minus : forall (n1 n2 : nat),
      astep st <{ n1 - n2 }> (n1 - n2)
  | AS_Mult1 : forall a1 a1' a2,
      astep st a1 a1' ->
      astep st <{ a1 * a2 }> <{ a1' * a2 }>
  | AS_Mult2 : forall v1 a2 a2',
      aval v1 ->
      astep st a2 a2' ->
      astep st <{ v1 * a2 }> <{ v1 * a2' }>
  | AS_Mult : forall (n1 n2 : nat),
      astep st <{ n1 * n2 }> (n1 * n2).

Reserved Notation " b '/' st 'b.>' b' "
                  (at level 40, st at level 39).

Inductive bstep (st : state) : bexp -> bexp -> Prop :=
| BS_Eq1 : forall a1 a1' a2,
    astep st a1 a1' ->
    <{ a1 = a2 }> / st b.> <{ a1' = a2 }>
| BS_Eq2 : forall v1 a2 a2',
    aval v1 ->
    astep st a2 a2' ->
    <{ v1 = a2 }> / st b.> <{ v1 = a2' }>
| BS_Eq : forall (n1 n2 : nat),
    <{ n1 = n2 }> / st b.>
    (if (n1 =? n2) then <{ true }> else <{ false }>)
| BS_LtEq1 : forall a1 a1' a2,
    astep st a1 a1' ->
    <{ a1 <= a2 }> / st b.> <{ a1' <= a2 }>
| BS_LtEq2 : forall v1 a2 a2',
    aval v1 ->
    astep st a2 a2' ->
    <{ v1 <= a2 }> / st b.> <{ v1 <= a2' }>
| BS_LtEq : forall (n1 n2 : nat),
    <{ n1 <= n2 }> / st b.>
    (if (n1 <=? n2) then <{ true }> else <{ false }>)
| BS_NotStep : forall b1 b1',
    b1 / st b.> b1' ->
    <{ ~ b1 }> / st b.> <{ ~ b1' }>
| BS_NotTrue : <{ ~ true }> / st b.> <{ false }>
| BS_NotFalse : <{ ~ false }> / st b.> <{ true }>
| BS_AndStep : forall b1 b1' b2,
    b1 / st b.> b1' ->
    <{ b1 && b2 }> / st b.> <{ b1' && b2 }>
| BS_AndTrueStep : forall b2 b2',
    b2 / st b.> b2' ->
    <{ true && b2 }> / st b.> <{ true && b2' }>
| BS_AndFalse : forall b2,
    <{ false && b2 }> / st b.> <{ false }>
| BS_AndTrueTrue : <{ true && true }> / st b.> <{ true }>
| BS_AndTrueFalse : <{ true && false }> / st b.> <{ false }>

where " b '/' st 'b.>' b' " := (bstep st b b').

Reserved Notation
  "'[' c ','  st ']' '.>' '[' c1 ',' st1 ']'"
  (at level 39, c custom com at level 99, c1 custom com at level 99,
    st constr, st1 constr at next level).

Inductive small_step : (com * state) -> (com * state) -> Prop :=
| SS_Skip : forall st,
    [skip, st] .> [skip, st]
| SS_AsgnStep : forall st i a1 a1',
  astep st a1 a1' ->
  [i := a1, st] .> [i := a1', st]
| SS_Asgn : forall st i (n : nat),
  [i := n, st] .> [skip, (i !-> n ; st)]
| SS_SeqStep : forall st c1 c1' st' c2,
  [c1, st] .> [c1', st'] ->
  [c1; c2, st] .> [c1'; c2, st']
| SS_SeqFinish : forall st c2,
  [skip; c2, st] .> [c2, st]
| SS_IfStep : forall st b1 b1' c1 c2,
  b1 / st b.> b1' ->
  [if b1 then c1 else c2 end, st]
  .>
  [if b1' then c1 else c2 end, st]
| SS_IfTrue : forall st c1 c2,
  [if true then c1 else c2 end, st] .> [c1, st]
| SS_IfFalse : forall st c1 c2,
  [if false then c1 else c2 end, st] .> [c2, st]
| SS_While : forall st b1 c1,
  [while b1 do c1 end, st]
  .>
  [if b1 then c1; while b1 do c1 end else skip end, st]
where "'[' c ',' st ']' '.>' '[' c1 ',' st1 ']'"
  := (small_step (c,st) (c1,st1)).

From Coq Require Import Relations.Relation_Definitions.

Inductive star {X : Type} (R : relation X) : relation X :=
| star_step : forall (x y : X), R x y -> star R x y 
| star_refl : forall (x : X), star R x x
| star_trans : forall (x y z : X),
                  R x y ->
                  star R y z ->
                  star R x z.

Theorem multi_R : forall (X : Type) (R : relation X) (x y : X),
    R x y -> (star R) x y.
Proof.
    intros X R x y H.
    apply star_trans
    with y. apply H. apply star_refl.
Qed.

Theorem multi_trans : forall (X : Type) (R : relation X) (x y z : X),
      star R x y ->
      star R y z ->
      star R x z.
Proof.
  intros X R x y z G H.
  induction G.
    - apply star_trans with y. assumption.
      assumption.
    - assumption.
    - apply star_trans with y. assumption.
      apply IHG. assumption.
Qed.

Notation "'[' c ','  st ']' '->*' '[' c1 ',' st1 ']'" :=
  (star small_step (c,st) (c1, st1))
  (at level 40, c custom com at level 99, c1 custom com at level 99,
    st constr, st1 constr at next level).

Require Import Coq.Program.Equality.

Theorem skip_some_skip_other : forall st1 st2,
    [skip, st1] ->* [skip, st2] ->
    st1 = st2.
Proof.
    intros. dependent induction H.
    - inversion H. reflexivity.
    - reflexivity.
    - apply IHstar. 
      inversion H. reflexivity.
      reflexivity. 
Qed.

(* Lemma 2.19 *)
Theorem decons_seq : forall c1 c2 st st2 st1, 
    [c1; c2, st] ->* [skip, st2] ->
    [c1, st] ->* [skip, st1] ->
    [c2, st1] ->* [skip, st2].
Proof.
    intros.
    dependent induction H.
    - inversion H; subst.
      apply skip_some_skip_other in H0.
      inversion H0.
      apply star_refl.
    - dependent destruction H.
      apply IHstar  with c1' st'; clear IHstar.
      reflexivity. reflexivity.
Admitted.

Require Export com. Import ImpNotations.
Require Export state. Import StateNotations.
Require Export aexp.
Require Export bexp.

From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Lia.

Inductive aval : aexp -> Prop :=
  | av_num : forall n, aval (ANum n).

Reserved Notation " a '/' st 'a.>' a' "
                  (at level 40, st at level 39).

Inductive astep (st : state) : aexp -> aexp -> Prop :=
  | AS_Id : forall (i : string),
      i / st a.> (st i)
  | AS_Plus1 : forall a1 a1' a2,
      a1 / st a.> a1' ->
      <{ a1 + a2 }> / st a.> <{ a1' + a2 }>
  | AS_Plus2 : forall v1 a2 a2',
      aval v1 ->
      a2 / st a.> a2' ->
      <{ v1 + a2 }> / st a.> <{ v1 + a2' }>
  | AS_Plus : forall (n1 n2 : nat),
      <{ n1 + n2 }> / st a.> (n1 + n2)
  | AS_Minus1 : forall a1 a1' a2,
      a1 / st a.> a1' ->
      <{ a1 - a2 }> / st a.> <{ a1' - a2 }>
  | AS_Minus2 : forall v1 a2 a2',
      aval v1 ->
      a2 / st a.> a2' ->
      <{ v1 - a2 }> / st a.> <{ v1 - a2' }>
  | AS_Minus : forall (n1 n2 : nat),
      <{ n1 - n2 }> / st a.> (n1 - n2)
  | AS_Mult1 : forall a1 a1' a2,
      a1 / st a.> a1' ->
      <{ a1 * a2 }> / st a.> <{ a1' * a2 }>
  | AS_Mult2 : forall v1 a2 a2',
      aval v1 ->
      a2 / st a.> a2' ->
      <{ v1 * a2 }> / st a.> <{ v1 * a2' }>
  | AS_Mult : forall (n1 n2 : nat),
      <{ n1 * n2 }> / st a.> (n1 * n2)

    where " a '/' st 'a.>' a' " := (astep st a a').

Reserved Notation " b '/' st 'b.>' b' "
                  (at level 40, st at level 39).

Inductive bstep (st : state) : bexp -> bexp -> Prop :=
| BS_Eq1 : forall a1 a1' a2,
    a1 / st a.> a1' ->
    <{ a1 = a2 }> / st b.> <{ a1' = a2 }>
| BS_Eq2 : forall v1 a2 a2',
    aval v1 ->
    a2 / st a.> a2' ->
    <{ v1 = a2 }> / st b.> <{ v1 = a2' }>
| BS_Eq : forall (n1 n2 : nat),
    <{ n1 = n2 }> / st b.>
    (if (n1 =? n2) then <{ true }> else <{ false }>)
| BS_LtEq1 : forall a1 a1' a2,
    a1 / st a.> a1' ->
    <{ a1 <= a2 }> / st b.> <{ a1' <= a2 }>
| BS_LtEq2 : forall v1 a2 a2',
    aval v1 ->
    a2 / st a.> a2' ->
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

Inductive cstep : (com * state) -> (com * state) -> Prop :=
| CS_AsgnStep : forall st i a1 a1',
  a1 / st a.> a1' ->
  [i := a1, st] .> [i := a1', st]
| CS_Asgn : forall st i (n : nat),
  [i := n, st] .> [skip, (i !-> n ; st)]
| CS_SeqStep : forall st c1 c1' st' c2,
  [c1, st] .> [c1', st'] ->
  [c1; c2, st] .> [c1'; c2, st']
| CS_SeqFinish : forall st c2,
  [skip; c2, st] .> [c2, st]
| CS_IfStep : forall st b1 b1' c1 c2,
  b1 / st b.> b1' ->
  [if b1 then c1 else c2 end, st]
  .>
  [if b1' then c1 else c2 end, st]
| CS_IfTrue : forall st c1 c2,
  [if true then c1 else c2 end, st] .> [c1, st]
| CS_IfFalse : forall st c1 c2,
  [if false then c1 else c2 end, st] .> [c2, st]
| CS_While : forall st b1 c1,
  [while b1 do c1 end, st]
  .>
  [if b1 then c1; while b1 do c1 end else skip end, st]
where "'[' c ',' st ']' '.>' '[' c1 ',' st1 ']'"
  := (cstep (c,st) (c1,st1)).

Definition relation (X : Type) := X -> X -> Prop.
Inductive multi {X : Type} (R : relation X) : relation X :=
| multi_refl : forall (x : X), multi R x x
| multi_step : forall (x y z : X),
                  R x y ->
                  multi R y z ->
                  multi R x z.

Notation "'[' c ','  st ']' '*>' '[' c1 ',' st1 ']'" :=
  (multi cstep (c,st) (c1, st1))
  (at level 40, c custom com at level 99, c1 custom com at level 99,
    st constr, st1 constr at next level).

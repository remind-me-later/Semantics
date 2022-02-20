Require Export state. Import StateNotations.
Require Export aexp.
Require Export bexp.

From Coq Require Import Bool.Bool.
From Coq Require Import Arith.EqNat. Import Nat.

Inductive com : Type :=
  | CNop
  | CAsgn (x : string) (a : aexp)
  | CConcat (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com)
  | CRepeat (b : bexp) (c : com).

Module ImpNotations.

Declare Custom Entry com.
Declare Scope com_scope.

Notation "<{ e }>" := e (at level 0, e custom com at level 99) : com_scope.
Notation "( x )" := x (in custom com, x at level 99) : com_scope.
Notation "x" := x (in custom com at level 0, x constr at level 0) : com_scope.

Coercion AId : string >-> aexp.
Coercion ANum : nat >-> aexp.
Notation "x + y" := (APlus x y) (in custom com at level 50, left associativity).
Notation "x - y" := (AMinus x y) (in custom com at level 50, left associativity).
Notation "x * y" := (AMult x y) (in custom com at level 40, left associativity).

Notation "'true'" := true (at level 1).
Notation "'true'" := BTrue (in custom com at level 0).
Notation "'false'" := false (at level 1).
Notation "'false'" := BFalse (in custom com at level 0).
Notation "x <= y" := (BLe x y) (in custom com at level 70, no associativity).
Notation "x = y" := (BEq x y) (in custom com at level 70, no associativity).
Notation "x && y" := (BAnd x y) (in custom com at level 80, left associativity).
Notation "'~' b" := (BNot b) (in custom com at level 75, right associativity).

Notation "'skip'" :=
         CNop (in custom com at level 0) : com_scope.
Notation "x := y" :=
         (CAsgn x y)
            (in custom com at level 0, x constr at level 0,
             y at level 85, no associativity) : com_scope.
Notation "x ; y" :=
         (CConcat x y)
           (in custom com at level 90, right associativity) : com_scope.
Notation "'if' x 'then' y 'else' z 'end'" :=
         (CIf x y z)
           (in custom com at level 89, x at level 99,
            y at level 99, z at level 99) : com_scope.
Notation "'while' x 'do' y 'end'" :=
         (CWhile x y)
            (in custom com at level 89, x at level 99, y at level 99) : com_scope.
Notation "'repeat' x 'until' y 'end'" :=
  (CRepeat y x)
      (in custom com at level 89, x at level 99, y at level 99) : com_scope.

Reserved Notation
  "'[' c ','  st ']' '~>' st'"
  (at level 40, c custom com at level 99,
    st constr, st' constr at next level).

End ImpNotations.

Import ImpNotations.
Open Scope com_scope.

(* variable shorthands *)
Definition w : string := "W".
Definition x : string := "X".
Definition y : string := "Y".
Definition z : string := "Z".

(* command evaluation *)
Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      [ skip, st ] ~> st
  | E_Assign : forall st a x,
      [ x := a, st ] ~> (x !-> aeval st a; st)
  | E_Concat : forall c1 c2 st st' st'',
      [ c1, st ] ~> st'' ->
      [ c2, st'' ] ~> st' ->
      [ c1 ; c2, st ] ~> st'
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      [ c1, st ] ~> st' ->
      [ if b then c1 else c2 end, st] ~> st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      [ c2, st ] ~> st' ->
      [ if b then c1 else c2 end, st] ~> st'
  | E_WhileFalse : forall st b c,
      beval st b = false ->
      [ while b do c end, st ] ~> st
  | E_WhileTrue : forall st st' st'' b c,
      beval st b = true ->
      [ c, st ] ~> st'' ->
      [ while b do c end, st'' ] ~> st' ->
      [ while b do c end, st ] ~> st'
  | E_RepeatTrue : forall st st' b c,
      [ c, st ] ~> st' ->
      beval st' b = true ->
      [ repeat c until b end, st ] ~> st'
  | E_RepeatFalse : forall st st' st'' b c,
      [ c, st ] ~> st'' ->
      beval st'' b = false ->
      [ repeat c until b end, st'' ] ~> st' ->
      [ repeat c until b end, st ] ~> st'
  where "'[' c ',' st ']' '~>' st'" := (ceval c st st').

Example ceval_example1:
  [ x := 2;
    if (x <= 1)
      then y := 3
      else z := 4
    end, 
    empty_st
  ] ~>
  (z !-> 4 ; x !-> 2).
Proof.
  apply E_Concat with (x !-> 2).
  - apply E_Assign. 

  - apply E_IfFalse.
    reflexivity.
    apply E_Assign.
Qed.

Definition cequiv (c1 c2 : com) : Prop :=
  forall (st st' : state),
    ([ c1, st ] ~> st') <-> ([ c2, st ] ~> st').

Theorem skip_left : forall c,
  cequiv
    <{ skip; c }>
    c.
Proof.
  intros. 
  split; intros.
  - inversion H. subst.
    inversion H2. subst.
    exact H5.
  - apply E_Concat with st.
    apply E_Skip.
    exact H.
Qed.

Theorem skip_right : forall c,
  cequiv <{ c ; skip }> c.
Proof.
  intros.
  split; intros.
  - inversion H. subst.
    inversion H5. subst. 
    exact H2.
  - apply E_Concat with st'.
    exact H. apply E_Skip.
Qed.

Theorem if_true: forall b c1 c2,
  bequiv b <{true}> ->
  cequiv
    <{ if b then c1 else c2 end }>
    c1.
Proof.
  intros b c1 c2 Hb.
  split; intros H.
  - inversion H. subst.
    + assumption.
    + unfold bequiv in Hb. simpl in Hb.
      rewrite Hb in H5.
      discriminate.
  - apply E_IfTrue; try assumption.
    unfold bequiv in Hb. simpl in Hb.
    apply Hb. 
Qed.

Theorem if_false: forall b c1 c2,
  bequiv b <{false}> ->
  cequiv
    <{ if b then c1 else c2 end }>
    c2.
Proof.
  intros b c1 c2 Hb.
  split; intros H.
  - inversion H. subst.
    + unfold bequiv in Hb. simpl in Hb.
      rewrite Hb in H5.
      discriminate.
    + assumption.
  - apply E_IfFalse.
    unfold bequiv in Hb. simpl in Hb.
    apply Hb. assumption. 
Qed.

Theorem while_unroll : forall b c,
  cequiv
    <{ while b do c end }>
    <{ if b then c ; while b do c end else skip end }>.
Proof.
  intros b c st st'.
  split; intros Hce.
  - inversion Hce; subst.
    + apply E_IfFalse. assumption. apply E_Skip.
    + apply E_IfTrue. assumption.
      apply E_Concat with st''. assumption. assumption.
  - inversion Hce; subst.
    + inversion H5; subst.
      apply E_WhileTrue with st''.
      assumption. assumption. assumption.
    + inversion H5; subst. apply E_WhileFalse. assumption.
Qed.

(* exercise 2.6, part 1 *)
Lemma concat_assoc: forall c c' c'',
  cequiv <{(c; c'); c''}> <{c; (c'; c'')}>.
Proof.
  intros c c' c'' st st'.  
  split; intros.
  - inversion H. subst.
    inversion H2. subst.
    apply E_Concat with st''0.
    assumption.
    apply E_Concat with st''.
    assumption. assumption.
  - inversion H. subst.
    inversion H5. subst.
    apply E_Concat with st''0.
    apply E_Concat with st''.
    assumption. assumption. assumption.
Qed.

(* exercise 2.6, part 2
Lemma concat_not_commutative: exists c c',
  ~(cequiv <{c; c'}> <{c'; c}>).
Proof.
  exists <{ x := 2 }>.
  exists <{ x := 1 }>.
  intros Hf.
  unfold cequiv in Hf.
  inversion H.
  
Qed *)

(* exercise 2.7 *)
Lemma repeat_unroll: forall b c, 
  let r := <{repeat c until b end}> in
  cequiv <{c; if b then skip else r end}> <{r}>.
Proof.
  intros b c r st st'.
  split; intros.
  - inversion H. subst.
    inversion H5. subst.
    inversion H8. subst.
    + apply E_RepeatTrue. assumption. assumption.
    + subst. apply E_RepeatFalse with st''.
      assumption. assumption. assumption.
  - inversion H. subst.
    + apply E_Concat with st'. assumption.
      apply E_IfTrue. assumption. apply E_Skip.
    + subst. apply E_Concat with st''. assumption.
      apply E_IfFalse. assumption. assumption.
Qed.

Lemma while_true_nonterm : forall b c st st',
  bequiv b <{true}> ->
  ~[ while b do c end, st ] ~> st'.
Proof.
  intros.
  intros Hf.
  remember <{ while b do c end }> as cw eqn:Heqcw.
  induction Hf;
  inversion Heqcw; subst; clear Heqcw.
  - unfold bequiv in H.
    rewrite H in H0. discriminate.
  - apply IHHf2. reflexivity.
Qed.

Theorem ceval_deterministic: forall c st st1 st2,
     [c, st] ~> st1 ->
     [c, st] ~> st2 ->
     st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2.
  induction E1; intros st2 E2; inversion E2; subst.
  - (* E_Skip *) reflexivity.
  - (* E_Asgn *) reflexivity.
  - (* E_Seq *)
    rewrite (IHE1_1 st''0 H1) in *.
    apply IHE1_2. assumption.
  - (* E_IfTrue, b evaluates to true *)
      apply IHE1. assumption.
  - (* E_IfTrue,  b evaluates to false (contradiction) *)
      rewrite H in H5. discriminate.
  - (* E_IfFalse, b evaluates to true (contradiction) *)
      rewrite H in H5. discriminate.
  - (* E_IfFalse, b evaluates to false *)
      apply IHE1. assumption.
  - (* E_WhileFalse, b evaluates to false *)
    reflexivity.
  - (* E_WhileFalse, b evaluates to true (contradiction) *)
    rewrite H in H2. discriminate.
  - (* E_WhileTrue, b evaluates to false (contradiction) *)
    rewrite H in H4. discriminate.
  - (* E_WhileTrue, b evaluates to true *)
    rewrite (IHE1_1 st''0 H3) in *.
    apply IHE1_2. assumption.
  - (* E_RepeatTrue, b evaluates to true *) 
    rewrite (IHE1 st2 H2) in *.
    reflexivity.
  - (* E_RepeatTrue, b evaluates to false (contradiction) *) 
    rewrite (IHE1 st'' H2) in *.
    rewrite H in H3. discriminate.
  - (* E_RepeatFalse, b evaluates to true (contradiction) *) 
    rewrite (IHE1_1 st2 H2) in *.
    rewrite H in H5. discriminate.
  - (* E_RepeatFalse, b evaluates to false *) 
    rewrite (IHE1_1 st''0 H2) in *.
    rewrite (IHE1_2 st2 H6) in *.
    reflexivity.
Qed.

(* exercise 2.8 *)
Theorem repeat_equiv_while : forall b c,
  let r := <{repeat c until b end}> in
  let w := <{c; while ~b do c end}> in
  cequiv <{r}> <{w}>.
Proof.
  intros. 
  split; intros.
  - inversion H; subst.
    + apply E_Concat with st'. assumption.
      apply E_WhileFalse. apply bev_not_true_iff_false.
      rewrite <- H5. apply bev_negb_involutive.
    + admit.
  - inversion H. subst.
    inversion H5. subst.
    + apply E_RepeatTrue. assumption.
      apply bev_not_true_iff_false in H6.
      rewrite <- H6. symmetry.
      apply bev_negb_involutive.
    + admit.
Admitted.

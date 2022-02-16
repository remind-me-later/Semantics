From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import Lia.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Strings.String.

(* Maps *)
Definition eqb_string (x y : string) : bool :=
  if string_dec x y then true else false.

Theorem eqb_string_refl : 
  forall s : string, true = eqb_string s s.
Proof.
  intros. unfold eqb_string.
  induction (string_dec s s) as [Hs_eq | Hs_not_eq].
  - reflexivity.
  - destruct Hs_not_eq. reflexivity.
Qed. 

Theorem eqb_string_true_iff : forall x y : string,
  eqb_string x y = true <-> x = y.
Proof.
  intros.
  unfold eqb_string.
  destruct (string_dec x y) as [Hs_eq | Hs_not_eq].
  - rewrite Hs_eq. split. reflexivity. reflexivity.
  - split.
    + intros. discriminate.
    + intros. exfalso. apply Hs_not_eq. apply H.
Qed.

Theorem eqb_string_false_iff : forall x y : string,
  eqb_string x y = false <-> x <> y.
Proof.
  intros. 
  rewrite <- eqb_string_true_iff.
  rewrite not_true_iff_false.
  reflexivity. 
Qed.

Definition total_map (A : Type) := string -> A.

Definition t_empty {A : Type} (v : A) : total_map A := 
  (fun _ => v).

Definition t_update {A : Type} (m : total_map A) (x : string) (v : A) :=
  fun x' => if eqb_string x x' then v else m x'.

Notation "'_' '!->' v" := (t_empty v)
  (at level 100, right associativity).

Notation "x '!->' v ';' m" := (t_update m x v)
  (at level 100, v at next level, right associativity).

(* Language *)
Inductive aexp : Type :=
  | ANum (n : nat)
  | AId (x : string)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).

Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).

Definition state := total_map nat.

Coercion AId : string >-> aexp.
Coercion ANum : nat >-> aexp.
Declare Custom Entry com.
Declare Scope com_scope.
Notation "<{ e }>" := e (at level 0, e custom com at level 99) : com_scope.
Notation "( x )" := x (in custom com, x at level 99) : com_scope.
Notation "x" := x (in custom com at level 0, x constr at level 0) : com_scope.
Notation "f x .. y" := (.. (f x) .. y)
                  (in custom com at level 0, only parsing,
                  f constr at level 0, x constr at level 9,
                  y constr at level 9) : com_scope.
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

Open Scope com_scope.

Fixpoint aeval (st : state) (a : aexp) {struct a} : nat :=
  match a with
  | ANum n => n
  | AId x => st x
  | <{a1 + a2}> => (aeval st a1) + (aeval st a2)
  | <{a1 - a2}> => (aeval st a1) - (aeval st a2)
  | <{a1 * a2}> => (aeval st a1) * (aeval st a2)
  end.

Fixpoint beval (st : state) (b : bexp) {struct b} : bool :=
  match b with
  | <{true}> => true
  | <{false}> => false
  | <{a1 = a2}> => (aeval st a1) =? (aeval st a2)
  | <{a1 <= a2}> => (aeval st a1) <=? (aeval st a2)
  | <{~ b1}> => negb (beval st b1)
  | <{b1 && b2}> => andb (beval st b1) (beval st b2)
  end.

Definition empty_st := (_ !-> 0).
Notation "x '!->' v" := (x !-> v ; empty_st) (at level 100).

Definition w : string := "W".
Definition x : string := "X".
Definition y : string := "Y".
Definition z : string := "Z".

Example aexp1 :
    aeval (x !-> 5) <{ 3 + (x * 2) }> = 13.
Proof. 
  reflexivity. 
Qed.

Example aexp2 :
    aeval (x !-> 5 ; y !-> 4) <{ z + (x * y) }> = 20.
Proof. 
  reflexivity. 
Qed.

Example bexp1 :
    beval (x !-> 5) <{ true && ~(x <= 4) }> = true.
Proof. 
  reflexivity.
Qed.

(* book definitions *)
Inductive aevalR : state -> aexp -> nat -> Prop :=
  | E_ANum (st: state) (n : nat) :
      aevalR st (ANum n) n
  | E_AId (st: state) (x: string) :
      aevalR st (AId x) (st x)
  | E_APlus (st: state) (e1 e2 : aexp) (n1 n2 : nat)
      (H1 : aevalR st e1 n1)
      (H2 : aevalR st e2 n2) :
      aevalR st <{e1 + e2}> (n1 + n2)
  | E_AMinus (st: state) (e1 e2 : aexp) (n1 n2 : nat)
      (H1 : aevalR st e1 n1)
      (H2 : aevalR st e2 n2) :
      aevalR st <{e1 - e2}> (n1 - n2)
  | E_AMult (st: state) (e1 e2 : aexp) (n1 n2 : nat)
      (H1 : aevalR st e1 n1)
      (H2 : aevalR st e2 n2) :
      aevalR st <{e1 * e2}> (n1 * n2).

Inductive bevalR : state -> bexp -> bool -> Prop :=
  | E_BTrue (st: state) :
      bevalR st <{true}> true
  | E_BFalse (st: state) :
      bevalR st <{false}> false
  | E_BEq (st: state) (e1 e2: aexp) (n1 n2 : nat) 
      (H1: aevalR st e1 n1)
      (H2: aevalR st e2 n2) :
      bevalR st <{e1 = e2}> (n1 =? n2)
  | E_BLe (st: state) (e1 e2: aexp) (n1 n2 : nat) 
    (H1: aevalR st e1 n1)
    (H2: aevalR st e2 n2) :
    bevalR st <{e1 <= e2}> (n1 <=? n2)
  | E_BNot (st: state) (e: bexp) (b: bool)
    (H1: bevalR st e b) :
    bevalR st <{~e}> (negb b)
  | E_BAnd (st: state) (e1 e2: bexp) (b1 b2 : bool) 
    (H1: bevalR st e1 b1)
    (H2: bevalR st e2 b2) :
    bevalR st <{e1 && e2}> (andb b1 b2).

(* prove relational definitions are equivalent to inductive ones*)
Theorem aeval_iff_aevalR : forall a n st,
  (aevalR st a n) <-> aeval st a = n.
Proof.
  intros; split.

  - intros.
    induction H.
    3, 4, 5: subst.
    all: reflexivity.

  - generalize dependent n.
    induction a; simpl.
    all: intros; subst; constructor.
    1, 3, 5: apply IHa1.
    4, 5, 6: apply IHa2.
    all: reflexivity.
Qed.

Theorem beval_iff_bevalR : 
  forall e b st, (bevalR st e b) <-> beval st e = b.
Proof.
  intros; split.

  - intros; induction H.
    1, 2: reflexivity.
    3, 4: subst; reflexivity.
    all: unfold beval.
    all: 
      apply (aeval_iff_aevalR e1 n1) in H1;
      apply (aeval_iff_aevalR e2 n2) in H2.
    all: induction H1; induction H2; reflexivity.
  
  - generalize dependent b.
    induction e; simpl; intros; subst. 
    1, 2: constructor.
    1, 2: constructor; apply aeval_iff_aevalR; reflexivity.
    1: constructor. apply IHe. reflexivity. 
    1: constructor.
    apply IHe1. reflexivity.
    apply IHe2. reflexivity.
Qed.

(* Commands *)
Inductive com : Type :=
  | CSkip
  | CAsgn (x : string) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com)
  | CRepeat (b : bexp) (c: com).

Notation "'skip'" :=
         CSkip (in custom com at level 0) : com_scope.
Notation "x := y" :=
         (CAsgn x y)
            (in custom com at level 0, x constr at level 0,
             y at level 85, no associativity) : com_scope.
Notation "x ; y" :=
         (CSeq x y)
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
  "[ c ,  st ] => st'"
  (at level 40, c custom com at level 99,
    st constr, st' constr at next level).

(* command evaluation *)
Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st st',
      st = st' ->
      [ skip, st ] => st'
  | E_Asgn : forall st a n x,
      aeval st a = n ->
      [ x := a, st ] => (x !-> n ; st)
  | E_Seq : forall c1 c2 st st' st'',
      [ c1, st ] => st'' ->
      [ c2, st'' ] => st' ->
      [ c1 ; c2, st ] => st'
  | E_If : forall st st' b c1 c2,
      beval st b = true /\
      [ c1, st ] => st' \/
      beval st b = false /\
      [ c2, st ] => st' ->
      [ if b then c1 else c2 end, st] => st'
  | E_While : forall st st' st'' b c,
      beval st b = true /\
      [ c, st ] => st'' /\
      [ while b do c end, st'' ] => st' \/
      beval st b = false /\
      st = st' ->
      [ while b do c end, st ] => st'
  | E_Repeat : forall st st' st'' b c,
      beval st b = true /\
      [ c, st ] => st'' /\
      [ repeat c until b end, st'' ] => st' \/
      beval st b = false /\
      [ c, st ] => st' ->
      [ repeat c until b end, st ] => st'
  where "[ c , st ] => st'" := (ceval c st st').

Example ceval_example1:
  [ x := 2;
    if (x <= 1)
      then y := 3
      else z := 4
    end, empty_st
  ] =>
  (z !-> 4 ; x !-> 2).
Proof.
  apply E_Seq with (x !-> 2).
  - apply E_Asgn. 
    reflexivity.

  - apply E_If.
    simpl.
    right. split. reflexivity.
    apply E_Asgn.
    reflexivity.
Qed.

Lemma if_skip_skip_equiv_skip : forall b st,
  [if b then skip else skip end, st] => st.
Proof.
  intros. apply E_If. induction beval.
  1: left; split.
  3: right; split. 
  1, 3: reflexivity.
  all: constructor; reflexivity.
Qed.

(* exercise 2.7 *)
Lemma while_equiv_repeat : forall b c st st',
  let r := <{repeat c until b end}> in
  [ r, st ] => st' <-> 
  [ c; if b then skip else r end, st ] => st'.
Proof.
  split.
  - intros. 
    induction H.
    + apply E_Seq with st'. induction H. constructor.


(* proposition 2.8 *)
Lemma while_equiv_if : forall b c st st',
  let w := <{while b do c end}> in
  [w, st] => st' <-> [ if b then c; w else skip end, st] => st'.
Proof.
  intros.
  induction w0.
  - split; intros. constructor.

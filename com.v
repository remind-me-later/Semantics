Require Export state. Import StateNotations.
Require Export aexp.
Require Export bexp.

From Coq Require Import Bool.Bool.

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
  "'[' c ','  st ']' '=' st'"
  (at level 40, c custom com at level 99,
    st constr, st' constr at next level).

End ImpNotations.

Import ImpNotations.
Open Scope com_scope.

Definition w : string := "W".
Definition x : string := "X".
Definition y : string := "Y".
Definition z : string := "Z".


(* command evaluation *)
Inductive ceval : com -> state -> state -> Prop :=
  | E_Nop : forall st,
      [ skip, st ] = st
  | E_Assign : forall st a n x,
      aeval st a = n ->
      [ x := a, st ] = (x !-> n ; st)
  | E_Concat : forall c1 c2 st st' st'',
      [ c1, st ] = st'' ->
      [ c2, st'' ] = st' ->
      [ c1 ; c2, st ] = st'
  | E_If : forall st st' b c1 c2,
      beval st b = true /\
      [ c1, st ] = st' \/
      beval st b = false /\
      [ c2, st ] = st' ->
      [ if b then c1 else c2 end, st] = st'
  | E_While : forall st st' st'' b c,
      beval st b = true /\
      [ c, st ] = st'' /\
      [ while b do c end, st'' ] = st' \/
      beval st b = false /\
      [skip, st] = st' ->
      [ while b do c end, st ] = st'
  | E_Repeat : forall st st' st'' b c,
      [ c, st ] = st'' /\
      beval st'' b = false /\
      [ repeat c until b end, st'' ] = st' \/
      [ c, st ] = st' /\
      beval st' b = true ->
      [ repeat c until b end, st ]= st'
  where "'[' c ',' st ']' '=' st'" := (ceval c st st').

Example ceval_example1:
  [ x := 2;
    if (x <= 1)
      then y := 3
      else z := 4
    end, 
    empty_st
  ] =
  (z !-> 4 ; x !-> 2).
Proof.
  apply E_Concat with (x !-> 2).
  - apply E_Assign. 
    reflexivity.

  - apply E_If.
    simpl.
    right. split. reflexivity.
    apply E_Assign.
    reflexivity.
Qed.

Lemma if_nop : forall b st,
  [if b then skip else skip end, st] = st.
Proof.
  intros. apply E_If. induction beval.
  1: left; split.
  3: right; split. 
  1, 3: reflexivity.
  all: constructor.
Qed.

Lemma repeat_equiv_c : forall b c (st st' st'': state),
  [c, st] = st' ->
  beval st' b = true ->
  [ repeat c until b end, st] = st'.
Proof.
  intros.
  simple apply E_Repeat with st'.
  rewrite H0.
  right. split.
  exact H. reflexivity.
Qed.

(* exercise 2.7 *)
Lemma unfold_repeat: forall b c st st' stf, 
  let r := <{repeat c until b end}> in
  [c, st] = st' ->      (* initial state goes to first *)
  st' = stf ->          (* final state may be first *)
  beval stf b = true -> (* final state evaluates to true *)
  [ r, st' ] = stf ->   (* induction hypothesis *)
  [ c; if b then skip else r end, st ] = stf <->
  [ r, st ] = stf.
Proof.
  intros. split; intros.
  - apply E_Repeat with stf.
    right. split.
    replace stf with st'.
    exact H. exact H1.
  - apply E_Concat with stf.
    rewrite <- H0. exact H.
    apply E_If. left. split.
    exact H1. constructor.
Qed.

(*
(* proposition 2.8 *)
Lemma while_equiv_if : forall b c st st',
  let w := <{while b do c end}> in
  [w, st] => st' <-> [ if b then c; w else skip end, st] => st'.
Proof. *)
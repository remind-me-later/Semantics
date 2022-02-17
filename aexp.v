Require Export state.
Import StateNotations.

From Coq Require Export Strings.String.

Inductive aexp : Type :=
  | ANum (n : nat)
  | AId (x : string)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).

(* Evaluation function, recursive definition *)
Fixpoint aeval (st : state) (a : aexp) {struct a} : nat :=
  match a with
  | ANum n => n
  | AId x => st x
  | APlus a1 a2 => (aeval st a1) + (aeval st a2)
  | AMinus a1 a2 => (aeval st a1) - (aeval st a2)
  | AMult a1 a2 => (aeval st a1) * (aeval st a2)
  end.

(* Examples *)
Example aexp1 :
  aeval ("x" !-> 5) (APlus (ANum 3) (AMult (AId "x") (ANum 2))) = 13.
Proof. 
  reflexivity. 
Qed.

Example aexp2 :
  aeval ("x" !-> 5 ; "y" !-> 4) (APlus (AId "z") (AMult (AId "x") (AId "y")) ) = 20.
Proof. 
  reflexivity. 
Qed.

(* Evaluation relational, recursive definition *)
Inductive aevalR : state -> aexp -> nat -> Prop :=
  | E_ANum (st: state) (n : nat) :
      aevalR st (ANum n) n
  | E_AId (st: state) (x: string) :
      aevalR st (AId x) (st x)
  | E_APlus (st: state) (e1 e2 : aexp) (n1 n2 : nat)
      (H1 : aevalR st e1 n1)
      (H2 : aevalR st e2 n2) :
      aevalR st (APlus e1 e2) (n1 + n2)
  | E_AMinus (st: state) (e1 e2 : aexp) (n1 n2 : nat)
      (H1 : aevalR st e1 n1)
      (H2 : aevalR st e2 n2) :
      aevalR st (AMinus e1 e2) (n1 - n2)
  | E_AMult (st: state) (e1 e2 : aexp) (n1 n2 : nat)
      (H1 : aevalR st e1 n1)
      (H2 : aevalR st e2 n2) :
      aevalR st (AMult e1 e2) (n1 * n2).

(* prove relational definition is equivalent to recursive *)
Theorem aeval_iff_aevalR : forall a n st,
  aevalR st a n <-> aeval st a = n.
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

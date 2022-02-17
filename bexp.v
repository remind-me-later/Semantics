Require Export state. 
Import StateNotations.
Require Export aexp.

From Coq Require Import Arith.EqNat. Import Nat.

Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).

Fixpoint beval (st : state) (b : bexp) {struct b} : bool :=
match b with
| BTrue => true
| BFalse => false
| BEq a1 a2 => (aeval st a1) =? (aeval st a2)
| BLe a1 a2 => (aeval st a1) <=? (aeval st a2)
| BNot b1 => negb (beval st b1)
| BAnd b1 b2 => andb (beval st b1) (beval st b2)
end.
  
Example bexp1 :
    beval ("x" !-> 5) (BAnd BTrue (BNot (BLe (AId "x") (ANum 4)))) = true.
Proof. 
  reflexivity.
Qed.

Inductive bevalR : state -> bexp -> bool -> Prop :=
  | E_BTrue (st: state) :
      bevalR st BTrue true
  | E_BFalse (st: state) :
      bevalR st BFalse false
  | E_BEq (st: state) (e1 e2: aexp) (n1 n2 : nat) 
      (H1: aevalR st e1 n1)
      (H2: aevalR st e2 n2) :
      bevalR st (BEq e1 e2) (n1 =? n2)
  | E_BLe (st: state) (e1 e2: aexp) (n1 n2 : nat) 
    (H1: aevalR st e1 n1)
    (H2: aevalR st e2 n2) :
    bevalR st (BLe e1 e2) (n1 <=? n2)
  | E_BNot (st: state) (e: bexp) (b: bool)
    (H1: bevalR st e b) :
    bevalR st (BNot e) (negb b)
  | E_BAnd (st: state) (e1 e2: bexp) (b1 b2 : bool) 
    (H1: bevalR st e1 b1)
    (H2: bevalR st e2 b2) :
    bevalR st (BAnd e1 e2) (andb b1 b2).

Theorem beval_iff_bevalR : forall e b st,
  bevalR st e b <-> beval st e = b.
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
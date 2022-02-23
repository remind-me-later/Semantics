From Coq Require Import Bool.Bool.
From Coq Require Import Strings.String.
From Coq Require Import Setoids.Setoid.
From Coq Require Import Logic.FunctionalExtensionality.

Definition total_map (A : Type) := string -> A.

Definition t_empty {A : Type} (v : A) : total_map A := 
  (fun _ => v).

Definition t_update {A : Type} (m : total_map A) (x : string) (v : A) :=
  fun x' => if eqb x x' then v else m x'.

Module MapNotations.

Notation "'_' '!->' v" := (t_empty v)
  (at level 100, right associativity).
Notation "x '!->' v ';' m" := (t_update m x v)
  (at level 100, v at next level, right associativity).

End MapNotations.

Import MapNotations.

Lemma t_apply_empty : forall (A : Type) (x : string) (v : A),
  (_ !-> v) x = v.
Proof.
  intros.
  unfold t_empty.
  reflexivity.
Qed.

Lemma t_update_eq : forall (A : Type) (m : total_map A) x v,
  (x !-> v ; m) x = v.
Proof.
  intros.
  unfold t_update.
  rewrite eqb_refl.
  reflexivity.
Qed.

Theorem t_update_neq : forall (A : Type) (m : total_map A) x1 x2 v,
  x1 <> x2 -> (x1 !-> v ; m) x2 = m x2.
Proof.
  intros.
  unfold t_update.
  rewrite <- eqb_neq in H.
  rewrite H.
  reflexivity.
Qed.

Lemma t_update_shadow : forall (A : Type) (m : total_map A) x v1 v2,
  (x !-> v2 ; x !-> v1 ; m) = (x !-> v2 ; m).
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold t_update.
  induction (x =? x0)%string; 
  reflexivity.
Qed.

Theorem t_update_same : forall (A : Type) (m : total_map A) x,
  (x !-> m x ; m) = m.
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold t_update.
  destruct (eqb_eq x x0).
  induction (x =? x0)%string.
  rewrite H; reflexivity.
  reflexivity.
Qed.

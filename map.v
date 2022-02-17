From Coq Require Import Bool.Bool.
From Coq Require Import Strings.String.

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

Module MapNotations.

Notation "'_' '!->' v" := (t_empty v)
  (at level 100, right associativity).
Notation "x '!->' v ';' m" := (t_update m x v)
  (at level 100, v at next level, right associativity).

End MapNotations.


From Coq Require Import Bool.Bool.
From Coq Require Import Strings.String.
From Coq Require Import Setoids.Setoid.

Definition eqb_string (x y : string) : bool :=
  if string_dec x y then true else false.

Theorem eqb_string_refl : forall s : string,
  true = eqb_string s s.
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

Definition map_equiv {A : Type} (m m': total_map A) (x : string) :=
  m x = m' x.

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
  rewrite <- eqb_string_refl.
  reflexivity.
Qed.

Theorem t_update_neq : forall (A : Type) (m : total_map A) x1 x2 v,
  x1 <> x2 -> (x1 !-> v ; m) x2 = m x2.
Proof.
  intros.
  unfold t_update.
  rewrite <- eqb_string_false_iff in H.
  rewrite H.
  reflexivity.
Qed.

(* functional extensionality? *)
Lemma t_update_shadow : forall (A : Type) (m : total_map A) x y v1 v2,
  map_equiv (x !-> v2 ; x !-> v1 ; m) (x !-> v2 ; m) y.
Proof.
  intros.
  unfold map_equiv.
  unfold t_update.
  induction (eqb_string x y);
  reflexivity.
Qed.

Lemma eqb_stringP : forall x y : string,
  reflect (x = y) (eqb_string x y).
Proof.
  intros.
  apply iff_reflect.
  rewrite eqb_string_true_iff.
  reflexivity.
Qed.

Theorem t_update_same : forall (A : Type) (m : total_map A) x y,
  map_equiv (x !-> m x ; m) m y.
Proof.
  intros.
  unfold map_equiv.
  unfold t_update.
  destruct (eqb_stringP x y).
  induction e.
  reflexivity.
  reflexivity.
Qed.

Require Export map. 

Definition state := total_map nat.
Definition empty_st := t_empty 0.

Module StateNotations.

Notation "x '!->' v" := (t_update empty_st x v) (at level 100).
Notation "x '!->' v ';' m" :=  (t_update m x v)
  (at level 100, v at next level, right associativity).

End StateNotations.

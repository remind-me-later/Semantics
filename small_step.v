Require Export com. Import ImpNotations.
Require Export state. Import StateNotations.
Require Export aexp.
Require Export bexp.

Reserved Notation
  "'[' c ','  st ']' '.>' st'"
  (at level 40, c custom com at level 99,
    st constr, st' constr at next level).

(* small step evaluation *)
Fixpoint ceval_step (st : state) (c : com) (i: nat) : option state :=
  match i with
  | O => None
  | S i' =>
    match c with
      | <{ skip }> =>
          Some st
      | <{ l := a1 }> =>
          Some (l !-> aeval st a1 ; st)
      | <{ c1 ; c2 }> =>
        match ceval_step st c1 i' with
        | Some st' => ceval_step st' c2 i'
        | None => None
        end
      | <{ if b then c1 else c2 end }> =>
          if (beval st b)
            then ceval_step st c1 i'
            else ceval_step st c2 i'
      | <{ while b1 do c1 end }> =>
          if beval st b1
          then match ceval_step st c1 i' with
              | Some st' => ceval_step st' c i'
              | None => None
              end
          else Some st
      | <{ repeat c1 until b1 end }> =>
          let stm := ceval_step st c1 i' in
          match stm with 
          | Some st' =>
            if beval st' b1 then
              stm
            else
              ceval_step st' c i'
          | None => None
          end
    end
  end.

Theorem step_c_skip_equiv_c : forall c k st, 
  ceval_step st <{c; skip}> k = ceval_step st <{c}> k.
Admitted.

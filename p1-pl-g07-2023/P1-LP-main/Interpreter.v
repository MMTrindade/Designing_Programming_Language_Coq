(** * An Evaluation Function for Imp *)


(** Taken from the chapter Imp:
  https://softwarefoundations.cis.upenn.edu/lf-current/ImpCEvalFun.html

    It might be a good idea to read the chapter before or as you
    develop your solution.
*)

From Coq Require Import Lia.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.PeanoNat.
Import Nat.
From Coq Require Import Arith.EqNat.
From FirstProject Require Import Imp Maps.

(* Let's import the result datatype from the relational evaluation file *)
From FirstProject Require Import RelationalEvaluation.

(** We can improve the readability of this version by introducing a
    bit of auxiliary notation to hide the plumbing involved in
    repeatedly matching against optional states. *)

(*
Notation "'LETOPT' x <== e1 'IN' e2"
   := (match e1 with
         | Some x => e2
         | None => None
       end)
   (right associativity, at level 60).
*)

(** 2.1. TODO: Implement ceval_step as specified. To improve readability,
               you are strongly encouraged to define auxiliary notation.
               See the notation LETOPT commented above (or in the ImpCEval chapter).*)

Fixpoint ceval_step (st : state) (c : com) (i : nat): option (state * result) := (*(<---Editted 18/05 MMTrind)*)
  match i with
  | O => None
  | S i' =>
    match c with
    | CSkip => Some (st, SContinue)
    | CBreak => Some (st, SBreak)
    | CAsgn x a => Some ((x !-> aeval st a; st), SContinue)
    | CSeq c1 c2 =>
       match ceval_step st c1 i' with
      | Some (st1, SContinue) => ceval_step st1 c2 i'
        (*match ceval_step st1 c2 i' with
        | Some (st2, result) => Some (st2, result)
        | None => None
        end*)
      | Some (st1, SBreak) => Some (st1, SBreak)
      | None => None
       end
    | CIf b c1 c2 =>
      if beval st b then
        ceval_step st c1 i'
      else
        ceval_step st c2 i'
    | CWhile b c =>
      if beval st b then
        match ceval_step st c i' with
        | Some (st', SBreak) => Some (st', SContinue)
        | Some (st', SContinue) => ceval_step st' (CWhile b c) i'
        | result => result
        end
      else
        Some (st, SContinue)
    end
  end.


  (* TODO *)
(* The following definition is taken from the book and it can be used to
   test the step-indexed interpreter. *)

Definition test_ceval (st:state) (c:com) :=
  match ceval_step st c 500 with
  | None    => None
  | Some (st, _) => Some (st X, st Y, st Z)
  end.

Example example_test_ceval :
     test_ceval empty_st

     <{ X := 2;
        if (X <= 1)
        then Y := 3
        else Z := 4
        end }>

     = Some (2, 0, 4).
Proof. reflexivity. Qed.




(** 
  2.2. TODO: Prove the following three properties.
             Add a succint explanation in your own words of why `equivalence1` and `inequivalence1` are valid.*)
(**)
Theorem equivalence1: forall st c,
(exists i0,
forall i1, i1>=i0 ->
ceval_step st <{ break; c }> i1
=
ceval_step st <{ break; skip }> i1
).

Proof.
  simpl. intros.
  exists 1. 
  intros i1 H.
  induction i1.
  - lia.
  - induction i1.
    -- reflexivity.
    -- reflexivity.
Qed.

(*2.2 Explanation of equivalence1: The theorem shows that it doesn't make any difference to replace the 
command c by a skip after a break, because when executing the program with a greater index 
than i0, that stablishes the amount of steps of execution, the result of the 
execution won't change anymore, guaranteeing equivalence for the execution of both commands.

It is valid because if a program executes break, it terminates and the next commands won't
be executed, leading to the same final result. By analyzing the semantics, it's also possible
to infer that both result types will be SBreak, that are equivalent*)

Theorem inequivalence1: forall st c,
(exists i0,
forall i1, i1>=i0 ->
ceval_step st <{ break; c }> i1
<>
ceval_step st <{ skip }> i1
).
Proof.
  intros.
  exists 2.
  intros i1 H.
  induction i1.
  - lia.
  - induction i1.
    -- lia.
    -- simpl. intro H'.
      induction (ceval_step st <{ break }> (S i1)) eqn:HB; inversion H'.
Qed.

(*2.2 Explanation of inequivalence1: The theorem shows that when executing the ceval_step
for two different commands <{ break; c }> and <{ skip }>, there's a limit-index i0, that
for any pair of executions using the same index number, i1 > i0, it will lead to different results,
or non equivalent results.

It is valid because if the first program executes break, it terminates and the next commands won't
be executed. This result will have a type SBreak. Meanwhile, the second program executing skip
doesn't necessarily terminate, and could possibly continue the execution, leading to a possible different
result. Besides that, its result won't have the type SBreak, like in the first case, being non equivalent.*)


Theorem p1_equivalent_p2: forall st,
  (exists i0,
    forall i1, i1>=i0 ->
      ceval_step st p1 i1 = ceval_step st p2 i1
  ).

Proof.
  intros.
  unfold p1, p2.
  exists 6.
  intros.
  destruct i1; try lia.
  destruct i1; try lia.
  destruct i1; try lia.
  destruct i1; try lia.
  destruct i1; try lia.
  destruct i1; try lia.
  simpl. 
  rewrite t_update_shadow.
  reflexivity.
Qed.

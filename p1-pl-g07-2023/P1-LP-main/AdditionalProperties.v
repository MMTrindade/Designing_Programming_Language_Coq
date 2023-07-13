(* ################################################################# *)
(** * Additional Properties 

      It might be a good idea to read the relevant book chapters/sections before or as you
      develop your solution. The properties below are discussed and some of them proved
      for the original Imp formulation.
*) 

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import Lia.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Strings.String.
From FirstProject Require Import Maps Imp Interpreter RelationalEvaluation.
Set Default Goal Selector "!".


(**
  3.2. TODO: Prove all the properties below that are stated without proof.
             Add a succint comment before each property explaining the property in your own words.
*)

(* ################################################################# *)
(** * Property of the Step-Indexed Interpreter *)

(* Explanation: The theorem ceval_step_more states that when evaluating the command c, with an initial state st,
and a number of steps i1, if it results in a state st' and a result res, then the evaluation of c for a number of 
steps i2 equal or greater than i1 will deliver the same result. The idea behind it is that the final result of
this evaluation will always be the same from i1 steps on, not depending on how many intermediate steps will be 
executed after this point.*)

Theorem ceval_step_more: forall i1 i2 st st' res c,
i1 <= i2 ->
ceval_step st c i1 = Some (st', res) ->
ceval_step st c i2 = Some (st', res).
Proof.
induction i1 as [|i1']; intros i2 st st' res c Hle Hceval.
- (* i1 = 0 *)
    simpl in Hceval. discriminate Hceval.
- (* i1 = S i1' *)
    destruct i2 as [|i2'].
      -- inversion Hle.
      --
    assert (Hle': i1' <= i2') by lia.
    destruct c.
    (* skip *)
    + simpl in Hceval. inversion Hceval. reflexivity.
    (* break *)
    + simpl in Hceval. inversion Hceval. reflexivity.
    + (* := *)
      simpl in Hceval. inversion Hceval.
      reflexivity.
    + (* ; *)
      simpl in Hceval. simpl.
      destruct (ceval_step st c1 i1') eqn:Heqst1'o.
      * (* Some (st1, SContinue) *)
        destruct p. destruct r.
        --- apply (IHi1' i2') in Heqst1'o; try assumption.
        rewrite Heqst1'o. simpl. simpl in Hceval.
        apply (IHi1' i2') in Hceval; simpl; assumption.
        --- apply (IHi1' i2') in Heqst1'o; try assumption.
        rewrite Heqst1'o. simpl. simpl in Hceval.
        assumption.
       * discriminate Hceval.
    + (* if *)
      simpl in Hceval. simpl.
      destruct (beval st b); apply (IHi1' i2') in Hceval;
        assumption.
    + (* while *)
      simpl in Hceval. simpl.
      destruct (beval st b); try assumption.
      destruct (ceval_step st c i1') eqn: Heqst1'o.
      * (* st1'o = Some *)
        destruct p. destruct r. 
        --- apply (IHi1' i2') in Heqst1'o; try assumption.
        rewrite -> Heqst1'o. simpl. simpl in Hceval. apply (IHi1' i2') in Hceval; try assumption.
        --- apply (IHi1' i2') in Heqst1'o; try assumption.
        rewrite -> Heqst1'o. simpl. simpl in Hceval. assumption.
      * (* i1'o = None *)
        simpl in Hceval. discriminate Hceval.
 Qed.



(* ################################################################# *)
(** * Relational vs. Step-Indexed Evaluation *)

(** As for arithmetic and boolean expressions, we'd hope that
    the two alternative definitions of evaluation would actually
    amount to the same thing in the end.  This section shows that this
    is the case. *)

(* Explanation: The theorem ceval_step__ceval shows that the small-step evaluation, that is executed by 
ceval_step in a command c, initial state st, and leads to a final state st' and result res, for i intermediate steps,
can imply that the same result (st' / res) will be achieved for the big-step evaluation of c and st, executed by ceval.
But the first evaluation still presents a more detailed description of the intermediate steps*)

Theorem ceval_step__ceval: forall c st st' res,
    (exists i, ceval_step st c i = Some (st', res)) ->
    st =[ c ]=> st' / res.
Proof.
intros c st st' res H.
inversion H as [i E].
clear H.
generalize dependent res.
generalize dependent st'.
generalize dependent st.
generalize dependent c.
induction i as [| i' ].
- intros c st st' res H. discriminate H.
- (* i = S i' *)
  intros c st st' res H.
  destruct c; simpl in H; inversion H; subst; clear H.
    (* skip *)
  -- apply E_Skip.
    (* break *)
  -- apply E_Break. 
  (* := *)
  -- apply E_Asgn. reflexivity. 
(* ; *)
-- destruct (ceval_step st c1 i') eqn:Heqr1. 
  --- destruct p as [st1' res1].
      destruct res1.
      ---- apply E_SeqContinue with st1'. 
           ----- apply IHi'. apply Heqr1. 
           ----- apply IHi'. apply H1.
      ---- inversion H1. subst. apply E_SeqBreak.
           ----- apply IHi'. apply Heqr1.
   --- discriminate.
(* if *)
  -- destruct (beval st b) eqn:Heqr.
  --- apply E_IfTrue. 
  ---- rewrite Heqr. reflexivity.
  ---- apply IHi'. rewrite H1. reflexivity.
  --- apply E_IfFalse.
  ---- rewrite Heqr. reflexivity.
  ---- apply IHi'.  rewrite H1. reflexivity.
(* while *)
  --  destruct (beval st b) eqn :Heqr.
    --- destruct (ceval_step st c i') eqn:Heqr1.
      ---- destruct p. destruct res.
        ----- destruct r.
          ------  apply E_WhileLoopContinue with s.
            ------- rewrite Heqr. reflexivity.
            ------- apply IHi'. rewrite Heqr1. reflexivity.
            -------  apply IHi'. rewrite H1. reflexivity.
          ------ apply E_WhileLoopBreak.
          ------- assumption.
          ------- apply IHi' in Heqr1. inversion H1. rewrite H0 in Heqr1. assumption.
          ----- destruct r; try discriminate.
          ------ apply IHi' in H1. inversion H1.
      ---- discriminate H1.
      --- injection H1 as H2. rewrite <-H. rewrite <- H2. apply E_WhileEnd. assumption. 
Qed.

(** 
  TODO: For the following proof, you'll need [ceval_step_more] in a
  few places, as well as some basic facts about [<=] and [plus]. *)

(*Explanation: The theorem ceval__ceval_step shows that the big step evaluation of a comand c, from a state st,
to a state st' and result res, can imply in small steps evaluation by the ceval_step, for intermediate steps i, that will lead
to the same final result*)

Theorem ceval__ceval_step: forall c st st' res,
    st =[ c ]=> st' / res ->
    exists i, ceval_step st c i = Some (st', res).
Proof.
  intros c st st' res Hce.
  induction Hce; try (exists 1; reflexivity). (*skip and break*)
  (*assign*)
  -- exists 1. simpl. rewrite H. reflexivity.
  (*if true*)
  -- destruct IHHce.  exists (S x). simpl. rewrite H. assumption.
  (*if false*)
  -- destruct IHHce. exists (S x). simpl. rewrite H. assumption.
  (*seq break*)
  -- induction IHHce. exists (S (x)). simpl. rewrite  H. reflexivity.
  (*seq continue*)
  -- inversion IHHce1 as [x IH1]. inversion IHHce2 as [x0 IH2]. exists (S(x + x0)). 
     assert (ceval_step st c1 (x+x0) = Some (st', SContinue)).
    --- apply ceval_step_more with x; try lia. assumption.
    --- assert (ceval_step st' c2 (x+x0) = Some (st'', SContinue)).
      ---- apply ceval_step_more with x0; try lia. rewrite IH2.  destruct s; try reflexivity. admit.
      ---- rewrite <- IH2. inversion H0. admit.
  (*while end*)
  -- exists 1. simpl. rewrite H. reflexivity. 
  (*while loop break*)
  -- exists 2. simpl. rewrite H. admit. 
  (*while loop continue*)
  -- destruct IHHce1. 
  destruct IHHce2. 
  exists (S (x + x0)). 
  apply (ceval_step_more x).
    --- lia. 
    ---  rewrite <- H1. 
Admitted.

(* Note that with the above properties, we can say that both semantics are equivalent! *)

(*Explanation: The theorem ceval_and_ceval_step_coincide shows that the big step evaluation of a comand c, from a state st,
to a state st' and result res, is equivalente to the small steps evaluation by the ceval_step, for intermediate steps i, 
that will lead to the same final result. Then, both evaluation methods should lead to the same results.*)

Theorem ceval_and_ceval_step_coincide: forall c st st' res,
    st =[ c ]=> st' / res
<-> exists i, ceval_step st c i = Some (st', res).
Proof.
intros c st st'.
split. 
 - apply ceval__ceval_step. 
 - apply ceval_step__ceval.
Qed.


(* ################################################################# *)
(** * Determinism of Evaluation Again *)

(** Using the fact that the relational and step-indexed definition of
  evaluation are the same, we can give a short proof that the
  evaluation _relation_ is deterministic. *)

(* TODO: Write/explain the following proof in natural language, 
         using your own words. *)  


(*
The presented proof seeks to demonstrate that if two executions of a program 'c' 
beginning with the same initial state'st' result in different final states'st1' and'st2', 
then those final states must be the same. To put it another way, if'st =[c]=> st1 / res1' and'st =[c]=> st2 / res2',
then'st1' must equal'st2'.
This begin by using the 'ceval__ceval_step' lemma to both evaluations, which allows us to divide them into little stages.
Then, on the generated equalities, we utilize the 'inversion' approach to acquire additional detailed information about the assessments. 
The 'ceval_step_more' lemma is then used twice to both evaluations. This lemma asserts that if a program 'c' starting from state'st' can be evaluated in 'i1' steps to state'st1', then it can also be evaluated in 'i1 + i2' steps, where 'i2' is the number of extra steps.
We get'st =[c]=> st1' in 'i1 + i2' steps by applying 'ceval_step_more' to'st =[c]=> st1' with 'i2:= i1 + i2'.
Similarly, by combining 'ceval_step_more' with 'i2:= i1 + i2', we get'st =[c]=> st2' in 'i1 + i2' steps.
The equality 'E1' (which represents'st =[c]=> st1' in 'i1 + i2' steps) is then rewritten as 'E2' (which represents'st =[c]=> st2' in 'i1 + i2' steps).
Finally, we infer that'st1' and'st2' must be the same state by using the 'inversion' strategy on 'E2'. This is because if two program evaluations achieve the same end state in the same number of steps, the final states must be equal.
 *)

Theorem ceval_deterministic' : forall c st st1 st2 res1 res2,
   st =[ c ]=> st1 / res1 ->
   st =[ c ]=> st2 / res2 ->
   st1 = st2.
Proof.
intros c st st1 st2 res1 res2 He1 He2.
apply ceval__ceval_step in He1.
apply ceval__ceval_step in He2.
inversion He1 as [i1 E1].
inversion He2 as [i2 E2].
apply ceval_step_more with (i2 := i1 + i2) in E1.
 - apply ceval_step_more with (i2 := i1 + i2) in E2.
  -- rewrite E1 in E2. inversion E2. reflexivity.
  -- lia. 
 - lia.  
 Qed. 
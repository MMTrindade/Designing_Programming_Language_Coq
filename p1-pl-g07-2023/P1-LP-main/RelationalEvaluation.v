(** * Imp: Simple Imperative Programs *)

(** Taken from the chapter Imp:
  https://softwarefoundations.cis.upenn.edu/lf-current/Imp.html

    It might be a good idea to read the chapter before or as you
    develop your solution.
*)

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import Lia.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Strings.String.
From FirstProject Require Import Maps Imp.
Set Default Goal Selector "!".

(** Next, we need to define the behavior of [break].  Informally,
    whenever [break] is executed in a sequence of commands, it stops
    the execution of that sequence and signals that the innermost
    enclosing loop should terminate.  (If there aren't any
    enclosing loops, then the whole program simply terminates.)  The
    final state should be the same as the one in which the [break]
    statement was executed.

    One important point is what to do when there are multiple loops
    enclosing a given [break]. In those cases, [break] should only
    terminate the _innermost_ loop. Thus, after executing the
    following...

       X := 0;
       Y := 1;
       while 0 <> Y do
         while true do
           break
         end;
         X := 1;
         Y := Y - 1
       end

    ... the value of [X] should be [1], and not [0].

    One way of expressing this behavior is to add another parameter to
    the evaluation relation that specifies whether evaluation of a
    command executes a [break] statement: *)

Inductive result : Type :=
  | SContinue
  | SBreak.

Reserved Notation "st '=[' c ']=>' st' '/' s"
     (at level 40, c custom com at level 99, st' constr at next level).

(** Intuitively, [st =[ c ]=> st' / s] means that, if [c] is started in
    state [st], then it terminates in state [st'] and either signals
    that the innermost surrounding loop (or the whole program) should
    exit immediately ([s = SBreak]) or that execution should continue
    normally ([s = SContinue]).

    The definition of the "[st =[ c ]=> st' / s]" relation is very
    similar to the one we gave above for the regular evaluation
    relation ([st =[ c ]=> st']) -- we just need to handle the
    termination signals appropriately:

    - If the command is [skip], then the state doesn't change and
      execution of any enclosing loop can continue normally.

    - If the command is [break], the state stays unchanged but we
      signal a [SBreak].

    - If the command is an assignment, then we update the binding for
      that variable in the state accordingly and signal that execution
      can continue normally.

    - If the command is of the form [if b then c1 else c2 end], then
      the state is updated as in the original semantics of Imp, except
      that we also propagate the signal from the execution of
      whichever branch was taken.

    - If the command is a sequence [c1 ; c2], we first execute
      [c1].  If this yields a [SBreak], we skip the execution of [c2]
      and propagate the [SBreak] signal to the surrounding context;
      the resulting state is the same as the one obtained by
      executing [c1] alone. Otherwise, we execute [c2] on the state
      obtained after executing [c1], and propagate the signal
      generated there.

    - Finally, for a loop of the form [while b do c end], the
      semantics is almost the same as before. The only difference is
      that, when [b] evaluates to true, we execute [c] and check the
      signal that it raises.  If that signal is [SContinue], then the
      execution proceeds as in the original semantics. Otherwise, we
      stop the execution of the loop, and the resulting state is the
      same as the one resulting from the execution of the current
      iteration.  In either case, since [break] only terminates the
      innermost loop, [while] signals [SContinue]. *)

(** 3.1. TODO: Based on the above description, complete the definition of the
               [ceval] relation. *)


Inductive ceval : com -> state -> result -> state -> Prop :=
  | E_Skip : forall st,
      st =[ CSkip ]=> st / SContinue
  | E_Break : forall st,
      st =[ CBreak ]=> st / SBreak
  | E_Asgn : forall st x a n,
      aeval st a = n ->
      st =[ CAsgn x a ]=> (t_update st x n) / SContinue
  | E_IfTrue : forall st b c1 c2 st' s,
      beval st b = true ->
      st =[ c1 ]=> st' / s ->
      st =[ CIf b c1 c2 ]=> st' / s
  | E_IfFalse : forall st b c1 c2 st' s,
      beval st b = false ->
      st =[ c2 ]=> st' / s ->
      st =[ CIf b c1 c2 ]=> st' / s
  | E_SeqBreak : forall st c1 c2 st',
      st =[ c1 ]=> st' / SBreak ->
      st =[ CSeq c1 c2 ]=> st' / SBreak
  | E_SeqContinue : forall st c1 c2 st' st'' s,
      st =[ c1 ]=> st' / SContinue ->
      st' =[ c2 ]=> st'' / s ->
      st =[ CSeq c1 c2 ]=> st'' / s
  | E_WhileEnd  : forall st b c,
      beval st b = false ->
      st =[ CWhile b c ]=> st / SContinue
  | E_WhileLoopBreak : forall st st' b c,
      beval st b = true ->
      st =[ c ]=> st' / SBreak ->
      st =[ CWhile b c ]=> st' / SContinue
  | E_WhileLoopContinue  : forall st st' st'' b c,
      beval st b = true ->
      st =[ c ]=> st' / SContinue ->
      st' =[ CWhile b c ]=> st'' / SContinue ->
      st =[ CWhile b c ]=> st'' / SContinue
  where "st '=[' c ']=>' st' '/' s" := (ceval c st s st').



(** 
  3.2. TODO: Prove the following six properties of your definition of [ceval].
             Note that your semantics needs to satisfy these properties: if any of 
             these properties becomes unprovable, you should revise your definition of `ceval`. 
             Add a succint comment before each property explaining the property in your own words.
*)

(* Comment : 
  Due to the inclusion of the break statement,
 the execution of c is ignored, and consequently the end state st' is the same as the starting state st.
*)
               
               
Theorem break_ignore : forall c st st' s,
     st =[ break; c ]=> st' / s ->
     st = st'.


Proof. 
    intros.
    inversion H; subst.
    - inversion H5. reflexivity.
    - inversion H2.
Qed.

 (* Comment : 
   If the while loop executes without encountering a break statement,
the end result state s must be SContinue,
 indicating that the loop condition , at somepoint,  evaluated to false, causing the loop to stop naturally.
*)
               

Theorem while_continue : forall b c st st' s,
  st =[ while b do c end ]=> st' / s ->
  s = SContinue.
Proof.
   intros.
  inversion H. 
  - reflexivity.
  -  reflexivity.
  -  reflexivity.
Qed.

    (* Comment : 
  If the loop condition b evaluates to true in the initial state st,
and executing statement c from state st results in state st' with control state SBreak, 
then performing the full while loop beginning from state st results in state st' with result state SContinue.
This ensures that the result state is appropriately designated as SContinue when a loop finishes on a break statement.
*)

  
Theorem while_stops_on_break : forall b c st st',
  beval st b = true ->
  st =[ c ]=> st' / SBreak ->
  st =[ while b do c end ]=> st' / SContinue.
Proof.
    intros.
  inversion H0; subst; apply E_WhileLoopBreak;
    try apply H;
    try apply H0.
Qed.

    
    (* Comment : 
If we have two statements, c1 and c2, and executing c1 from state st results in state st'
 with result state SContinue, and executing c2 from state st' results in state st'' with result state SContinue, 
then executing the sequence c1 ; c2 starting from state st will result in state st'' with result state SContinue.
*)
  
Theorem seq_continue : forall c1 c2 st st' st'',
  st =[ c1 ]=> st' / SContinue ->
  st' =[ c2 ]=> st'' / SContinue ->
  st =[ c1 ; c2 ]=> st'' / SContinue.
Proof.
  intros .
  apply E_SeqContinue with (st':=st'); assumption.
Qed.

  
  (* Comment : 
 If we have two statements, c1 and c2, and executing c1 from state st results in state st' with control state SBreak,
then running the sequence c1 ; c2 starting from state st will also result in state st' with control state SBreak.
This indicates that c2 is not performed since the program ends in c1 and 
the second statement is not reached with this execution.
*)
  
Theorem seq_stops_on_break : forall c1 c2 st st',
  st =[ c1 ]=> st' / SBreak ->
  st =[ c1 ; c2 ]=> st' / SBreak.
Proof.
  intros.
  apply E_SeqBreak; assumption.
Qed.
 
  
  (* Comment : 
  If we have a while loop with condition b and body c, and executing the while loop starting from
state st results in state st' with control state SContinue, and the loop condition b evaluates to true in state st', 
then there exists a state st'' such that executing the body c from state st'' results in state st''
with control state SBreak.It assures that if a break statement is met during the execution of the loop body,
 and we know that this language does not support infinitive loops, then this theorem proves that
 we will have an SBreak state at some point in the program.
*)

   
Theorem while_break_true : forall b c st st',
  st =[ while b do c end ]=> st' / SContinue ->
  beval st' b = true ->
  exists st'', st'' =[ c ]=> st' / SBreak.

Proof.
  intros.
  remember <{ while b do c end }> as loop.
  induction H; try inversion Heqloop; try subst.
  - rewrite H0 in H. inversion H.
  - exists st. apply H1.
  - apply IHceval2.
    * reflexivity.
    * apply H0.
Qed.


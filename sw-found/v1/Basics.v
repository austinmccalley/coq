(* Define a type of days *)
Inductive day : Type :=
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.

(* Define a function which matches a day and returns the next day *)
Definition next_weekday (d:day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => monday
  | saturday => monday
  | sunday => monday
  end.

  (* Calculate the next week day after Friday *)
Compute (next_weekday friday).

(* We can then compound expressions *)
Compute (next_weekday (next_weekday saturday)).

(* Expect a result to be true -- a test of sorts *)
Example test_next_weekday: (next_weekday (next_weekday saturday)) = tuesday.

(* We can ask Coq to verify it like such *)
Proof. simpl. reflexivity. Qed.

(* Define the standard type bool of booleans with members true and false *)
Inductive bool : Type := 
  | true
  | false.

(* Define negation *)
Definition negb (b:bool) : bool :=
    match b with 
    | true => false
    | false => true
    end.

(* Define anding two bools *)
Definition andb (b1: bool) (b2: bool) : bool := 
    match b1 with
    | true => b2
    | false => false
    end.

(* Define or-ing two bools *)
Definition orb (b1: bool) (b2: bool) : bool := 
    match b1 with
    | true => true
    | false => b2
    end.

Example test_orb1: (orb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb2: (orb false false) = false.
Proof. simpl. reflexivity. Qed.
Example test_orb3: (orb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb4: (orb true true) = true.
Proof. simpl. reflexivity. Qed.

(* infix syntax for boolean ops *)
Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).

Example test_orb5: false || false || true = true.
Proof. simpl. reflexivity. Qed.

(* Conditional expressions *)
Definition negb' (b:bool) : bool := 
    if b then false
    else true.

Definition andb' (b1: bool) (b2: bool) : bool := 
    if b1 then b2
    else false.

Definition orb' (b1: bool) (b2: bool) : bool := 
    if b1 then true
    else b2.


    (* 
    The command Admitted can be used as a placeholder for an incomplete proof. We use it in exercises to indicate the parts that we're leaving for you -- i.e., your job is to replace Admitteds with real proofs.
Remove "Admitted." and complete the definition of the following function; then make sure that the Example assertions below can each be verified by Coq. (I.e., fill in each proof, following the model of the orb tests above, and make sure Coq accepts it.) The function should return true if either or both of its inputs are false.
Hint: if simpl will not simplify the goal in your proof, it's probably because you defined nandb without using a match expression. Try a different definition of nandb, or just skip over simpl and go directly to reflexivity. We'll explain this phenomenon later in the chapter.
    *)
Definition nandb (b1:bool) (b2:bool) : bool :=
    if b1 && b2 then false
    else true.

Example test_nandb1: (nandb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb2: (nandb false false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb3: (nandb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb4: (nandb true true) = false.
Proof. simpl. reflexivity. Qed.


Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
    if (b1 && b2) && b3 then true
    else false.

Example test_andb31: (andb3 true true true) = true.
Proof. simpl. reflexivity. Qed.
Example test_andb32: (andb3 false true true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb33: (andb3 true false true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb34: (andb3 true true false) = false.
Proof. simpl. reflexivity. Qed.

Check true.
Check (negb true).
Check negb.


(* 
In particular, the definitions of rgb and color say which constructor expressions belong to the sets rgb and color:
red, green, and blue belong to the set rgb;
black and white belong to the set color;
if p is a constructor expression belonging to the set rgb, then primary p (pronounced "the constructor primary applied to the argument p") is a constructor expression belonging to the set color; and
constructor expressions formed in these ways are the only ones belonging to the sets rgb and color.
*)
Inductive rgb : Type :=
  | red
  | green
  | blue.
Inductive color : Type :=
  | black
  | white
  | primary (p : rgb).

Definition monochrome (c : color) : bool :=
  match c with
  | black => true
  | white => true
  | primary p => false
  end.

Definition isred (c: color) : bool := 
    match c with
    | black => false
    | white => false
    | primary red => true
    | primary _ => false
    end.

Module Playground.
  Definition b : rgb := blue.
End Playground.
Definition b : bool := true.
Check Playground.b : rgb.
Check b : bool. 


Module TuplePlayground.
Inductive bit : Type :=
  | B0
  | B1.
Inductive nybble : Type :=
  | bits (b0 b1 b2 b3 : bit).

Check (bits B1 B0 B1 B0)
  : nybble.

Definition all_zero (nb : nybble) : bool :=
  match nb with
  | (bits B0 B0 B0 B0) => true
  | (bits _ _ _ _) => false
  end.

Compute (all_zero (bits B1 B0 B1 B0)).
(* ===> false : bool *)
Compute (all_zero (bits B0 B0 B0 B0)).
(* ===> true : bool *)
End TuplePlayground.

Module NatPlayground.
Inductive nat : Type :=
  | O
  | S (n : nat).

  Inductive nat' : Type :=
  | stop
  | tick (foo : nat').

  Definition pred (n : nat) : nat :=
  match n with
  | O => O
  | S n' => n'
  end.

End NatPlayground.

Check (S (S (S (S O)))).
(* ===> 4 : nat *)
Definition minustwo (n : nat) : nat :=
  match n with
  | O => O
  | S O => O
  | S (S n') => n'
  end.
Compute (minustwo 4).
(* ===> 2 : nat *)

Check S : nat -> nat.
Check pred : nat -> nat.
Check minustwo : nat -> nat.

(* Recursion === Fixpoint *)
Fixpoint even (n:nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => even n'
  end.
Definition odd (n:nat) : bool :=
  negb (even n).
Example test_odd1: odd 1 = true.
Proof. simpl. reflexivity. Qed.
Example test_odd2: odd 4 = false.
Proof. simpl. reflexivity. Qed.
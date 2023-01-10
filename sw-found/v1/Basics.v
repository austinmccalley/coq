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

Module NatPlayground2.

Fixpoint plus (n : nat) (m : nat) : nat :=
    match n with
    | O => m
    | S n' => S (plus n' m)
    end.

Fixpoint mut (n m : nat) : nat :=
    match n with
    | O => O
    | S n' => plus m (mut n' m)
    end.

Example test_mult1: (mut 3 3) = 9.
Proof. simpl. reflexivity. Qed.

Fixpoint minus (n m : nat) : nat :=
    match n, m with
    | O, _ => O
    | S _, O => n
    | S n', S m' => minus n' m'
    end.

End NatPlayground2.

Fixpoint exp (base power : nat) : nat :=
  match power with
  | O => S O
  | S p => mult base (exp base p)
  end.
Example test_exp1: (exp 3 3) = 27.
Proof. simpl. reflexivity. Qed.

Fixpoint factorial (n : nat) : nat := 
 match n with
 | O => 1
 | S n' => mult n (factorial n')
 end.

Example test_factorial1: (factorial 3) = 6.
Proof. simpl. reflexivity. Qed.
Example test_factorial2: (factorial 5) = (mult 10 12).
Proof. simpl. reflexivity. Qed.

Notation "x + y" := (plus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x - y" := (minus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x * y" := (mult x y)
                       (at level 40, left associativity)
                       : nat_scope.
Check ((0 + 1) + 1) : nat.

Fixpoint eqb (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => eqb n' m'
            end
  end.

Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => leb n' m'
      end
  end.
Example test_leb1: leb 2 2 = true.
Proof. simpl. reflexivity. Qed.
Example test_leb2: leb 2 4 = true.
Proof. simpl. reflexivity. Qed.
Example test_leb3: leb 4 2 = false.
Proof. simpl. reflexivity. Qed.

Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.
Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.
Example test_leb3': (4 <=? 2) = false.
Proof. simpl. reflexivity. Qed.

(* Less than resulting in a bool *)
Definition ltb (n m : nat) : bool :=
  match (n <=? m) with
  | true => negb (n =? m)
  | false => false
  end.

Notation "x <? y" := (ltb x y) (at level 70) : nat_scope.

Example test_ltb1: (ltb 2 2) = false.
Proof. simpl. reflexivity. Qed.
Example test_ltb2: (ltb 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_ltb3: (ltb 4 2) = false.
Proof. simpl. reflexivity. Qed.

Theorem plus_O_n : forall n : nat, 0 + n = n.
Proof.
  intros n. simpl. reflexivity. Qed.
Theorem plus_O_n' : forall n : nat, 0 + n = n.
Proof.
  intros n. reflexivity. Qed.

Theorem plus_O_n'' : forall n : nat, 0 + n = n.
Proof.
  intros m. reflexivity. Qed.

Theorem plus_1_l : forall n:nat, 1 + n = S n.
Proof.
  intros n. reflexivity. Qed.

Theorem mult_0_l : forall n:nat, 0 * n = 0.
Proof.
  intros n. reflexivity. Qed.

Theorem plus_id_example : forall n m : nat,
(* The arrow is prnounced "implies" *)
  n = m ->
  n + n = m + m.

Proof.
  (* move both quanitifers into the context *)
  intros n m.
  (* move the hypothesis into the context *)
  intros H.
  (* rewrite the goal using the hypothesis *)
  rewrite -> H.
  reflexivity. Qed.

(* Exercise plus_id_exercise *)
Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof.
  intros n m o.
  intros H.
  intros H'.
  rewrite -> H.
  rewrite -> H'.
  reflexivity. Qed.

Theorem mult_n_0_m_0 : forall p q : nat,
 (p * 0) + (q * 0) = 0.
 Proof.
  intros p q.
  rewrite <- mult_n_O.
  rewrite <- mult_n_O.
  reflexivity. Qed.

Theorem plus_1_neq_0_firsttry : forall n : nat,
  (n + 1) =? 0 = false.
Proof.
  intros n.  destruct n as [| n'] eqn:E.
  - reflexivity.
  - reflexivity. Qed.

Theorem negb_involutive : forall b : bool,
  negb (negb b) = b.
Proof.
  intros b. destruct b eqn:E.
  - reflexivity.
  - reflexivity. Qed.

Theorem andb_commutative : forall b c, andb b c = andb c b.
Proof.
  intros b c. destruct b eqn:Eb.
  - destruct c eqn:Ec.
    + reflexivity.
    + reflexivity.
  - destruct c eqn:Ec.
    + reflexivity.
    + reflexivity.
Qed.

Theorem andb_commutative' : forall b c, andb b c = andb c b.
Proof.
  intros b c. destruct b eqn:Eb.
  { destruct c eqn:Ec.
    { reflexivity. }
    { reflexivity. } }
  { destruct c eqn:Ec.
    { reflexivity. }
    { reflexivity. }
  }
Qed.

Theorem andb3_exchange : forall b c d, andb (andb b c) d = andb (andb b d) c.
Proof.
  intros b c d. destruct b eqn:Eb.
  - destruct c eqn:Ec.
    + destruct d eqn:Ed.
      * reflexivity.
      * reflexivity.
    + destruct d eqn:Ed.
      * reflexivity.
      * reflexivity.
  - destruct c eqn:Ec.
    + destruct d eqn:Ed.
      * reflexivity.
      * reflexivity.
    + destruct d eqn:Ed.
      * reflexivity.
      * reflexivity.
Qed.

Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
  intros b c H.
  destruct c.
    - reflexivity.
    - rewrite <- H.
      destruct b.
      + reflexivity.
      + reflexivity.
Qed.


Theorem plus_1_neq_0' : forall n : nat,
  (n + 1) =? 0 = false.
Proof.
  intros [|n].
    - reflexivity.
    - reflexivity.
Qed.

Theorem andb_commutative'' : forall b c, andb b c = andb c b.
Proof.
  intros [] [].
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
Qed.

Theorem zero_nbeq_plus_1 : forall n : nat,
  0 =? (n + 1) = false.
Proof.
  intros [|n].
    - reflexivity.
    - reflexivity.
Qed.


Theorem identity_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = x) ->
  forall (b : bool), f (f b) = b.
Proof.
  intros f H b.
  rewrite -> H.
  rewrite -> H.
  reflexivity.
Qed.



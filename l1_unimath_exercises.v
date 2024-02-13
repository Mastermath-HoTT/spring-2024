Require Export UniMath.Foundations.All.

(*The above line imports the definition of ~×~ and ~UU~ that we use below.*)

(* Example 1 *)

(* Show that Q follows from P ∧ (P → Q) *)

Theorem modusPonens {P Q : UU} (h : P × (P → Q)) : Q.
Proof.
  induction h.
  exact (pr2 pr1).
Qed.

Search dirprod.

Print modusPonens.

 (* or we could do *)

Theorem modusPonensAgain {P Q : UU} (h : P × (P → Q)) : Q.
Proof.
  induction h as [p f].
  (* Above, we used ~induction h~ and it made up names for the two new terms. Here we assert which names we want.*)
  pose proof ( f p ) as q.
  (* Here we can give a nice name to a derivable term and add it to the hypotheses.*)
  exact q.
Qed.

(* Example 2 *)

(* Show that (P ∧ Q) → P *)

Theorem firstProjection {P Q : UU} : (P × Q) → P.
Proof.
  intro.
  induction X.
  exact pr1.
Defined.

(* or we could do *)

Theorem firstProjectionAgain {P Q : UU} : (P × Q) → P.
Proof.
  intros [p _].
  assumption.
Qed.

(* Example 3 *)

(* Show that Q ∧ P follows from P ∧ Q *)

Theorem commute {P Q : UU} (c : Q × P) : P × Q.
Proof.
  induction c as [q p].
  exact (p,,q).
  (* In Unimath, you write terms of a product type as ~(?,,?)~ unfortunately.*)
Qed.

(* Exercise 4 *)

(* Show that multiplication of types is associative. *)

Theorem assoc {P Q R : UU} (c : (P × Q) × R ) : P × (Q × R).
Proof.
Admitted.

(* ~Admitted.~ tells Coq that you are not going to leave this proof empty for now, so I will use it in places where I want you to add a proof. *)

(* Exercise 5 *)

(* Show that functions can be composed.*)

Theorem comp {P Q R : UU} (f : P → Q) (g : Q → R) : P → R.
Proof.
Admitted.

(* Exercise 6 *)

(* A weird version of modus ponens. *)

Theorem weirdModusPonens {P Q : UU} : ((P → Q) × P → (P × Q)).
Proof.
Admitted.

(* Exercise 7 *)

(* Define the identity function. *)

(* Here's one way to do it. *)

Definition lambdaIdentity (P : UU) : P → P :=
  λ x , x.

(* This definition does *not* use tactic/proof mode. Notice how there is no ~Proof.~ or ~Qed.~. Here we construct a `lambda term' by hand. Actually everything is a lambda term in Coq, and the tactic mode just helps you to build them up. You can see what lambda term you've built up by typing ~Print ?.~ *)

Print lambdaIdentity.

Print modusPonens.

(* Now define the identity function using tactic/proof mode and check if it's the same as ~lambdaIdentity~ by using ~Print.~*)

Definition identity (P : UU) : P → P.
Proof.
Admitted.

Print identity.
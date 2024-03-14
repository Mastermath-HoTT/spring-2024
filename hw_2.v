Require Export UniMath.Foundations.All.

(* Exercise 1 *)

(* Formulate the following statements from Rijke in type theory (you do not have to prove them). The answer to the first one (a) is given as an example. *)

(* 1a. Theorem 9.3.4 *)

Definition Eq_Σ {A : UU} {B : A → UU}: (∑ x : A, B x) → (∑ x : A, B x) → UU.
Proof.
  Admitted.

Definition pair_eq {A : UU} {B : A → UU} (s t : ∑ x : A, B(x)) : (s = t) → Eq_Σ s t.
Proof.
  Admitted.

Theorem Thm_9_3_4 {A : UU} {B : A → UU} (s t : ∑ x : A, B(x)) : isweq (pair_eq s t).
Proof.
  Admitted.

(* 1b. Exercise 9.2a *)

(* 1c. Exercise 9.4a *)

(* 1d. Exercise 9.9a *)

(**************************************************************)

(* For the following exercises you can use the following results from previous exercise sessions without proofs. 
  You can also use `isweq_iso` and `funextsec` from the library.*)

Theorem hlevel_cumulative  {n : nat} {T : UU} (h : isofhlevel n T) : isofhlevel (S n) T.
Proof.
  Admitted.

Lemma contr_to_path {C : UU} (h : iscontr C) (x y : C) : x = y.
Proof.
  Admitted.

(* From here on, all `Admitted.`s should be filled in with proofs. As always, don't change the statements of any Theorems below, but you can always prove extra Lemmas to help. *)

(* Exercise 2 *)

(* Show that the definitions of proposition are equivalent. *)

Theorem prop_thm {P : UU} : (isaprop P) ≃ (∏ x y : P, x = y).
Proof.
  Admitted.

(* Exercise 3 *)

(* Proposition 12.1.4 from Rijke: An equivalence between propositions is (logically equivalent to) a logical equivalence. *)

Theorem Prop_12_1_4 (P Q : hProp) : (P ≃ Q) <-> (P <-> Q).
Proof.
  Admitted.

(* Exercise 4 *)

(* Show that the dependent product type former commutes with `isaprop`.*)

Theorem prop_commutes_Π {A : UU} {B : A → UU} (p : ∏ x : A, isaprop (B x)) : isaprop (∏ x : A, (B x)).
Proof.
  Admitted.

(* Exercise 5 *)

(* Show that isweq f (is-contr f in Rijke) is a proposition. *)

Theorem isweq_is_prop {A B : UU} (f : A → B) : isaprop (isweq f).
Proof.
  Admitted.

(* Exercise 6 *)

(* An equivalence between propositions is (equivalent to) a logical equivalence. *)

Theorem equiv_of_prop {P Q : hProp} : (P ≃ Q) ≃ (P <-> Q).
Proof.
  Admitted.
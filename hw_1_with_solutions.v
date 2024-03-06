Require Export UniMath.Foundations.All.

(* Exercise 1 *)

Theorem comp_app { P Q R : UU } (f : P → Q) (g : Q → R) (p : P) : R.
Proof.
  pose proof (f p) as q.
  pose proof (g q) as r.
  exact r.
Defined.

(* Exercise 2 *)

Theorem curried_proj {P Q R : UU} : (P → (Q × R)) → (P → Q).
Proof.
  intro f.
  intro p.
  pose proof (f p) as qr.
  induction qr as [q _].
  exact q.
Defined.

(* Exercise 3 *)

Theorem exp : nat → nat → nat.
Proof.
  intros n m.
  induction m.
  - (* We define n^0 to be 1.*)
    exact 1.
  - (* We define n^(Sm) to be n^m * n. *)
    exact (IHm * n).
Defined.

Compute (exp 5 1).

Compute (exp 3 2).

(* Exercise 4 *)

Search (∏ X Y : UU, ∏ f : X → Y, ∏ x y : X, x = y → (f x) = (f y)).

(* This command searches the library for functions of this kind. You should see in the output that ~maponpaths~ is of this kind. You can then print ~maponpaths~ (i.e. write "Print maponpaths.") to see the definition.

You can use this to find other lemmas from the library. You can use any facts without proof from the library about addition and multiplication as well as ~maponpaths~.*)

Theorem exp_hom {l m n : nat} : exp l (m + n) = (exp l m) * (exp l n).
Proof.
  induction m.
  - (* We show l^(m + 0) = l^m = l^m * l^0 *)
    simpl.
    apply (idpath).
  - (* We show l^(m + Sn) = l^(m + n)*l = l^m + l^Sn*)
    simpl.
    rewrite IHm.
    rewrite natmultassoc.
    rewrite natmultassoc.
    apply maponpaths.
    rewrite natmultcomm.
    apply idpath.
Defined.

(* Exercise 5 *)

Lemma path_combination {A : UU} {a a' b : A} (p : a = b) (q: a' = b) : a = a'.
Proof.
    induction p.
    induction q.
    apply idpath.
Defined.

(* Exercise 6 *)

Lemma path_combination_fact {A : UU} {a b : A} (p : a = b) : idpath a = path_combination p p.
Proof.
    induction p.
    simpl.
    apply idpath.
Defined.
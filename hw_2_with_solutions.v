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

Definition const (b : bool) : bool → bool.
Proof.
  Admitted.

Theorem Ex_9_5a (b : bool) (h : isweq (const b)) : ∅.
Proof.
  Admitted.

(* 1c. Exercise 9.4a *)

Definition sections {A B : UU} (f : A → B) : UU :=
  ∑ s : B → A, f ∘ s ~ idfun B.

Theorem Ex_9_4a {A B X: UU} {h : A → B} {f: A → X} {g : B → X} (H : f ~ g ∘ h) (s : sections f) : (f ∘ (pr1 s) ~ (idfun X)) × ((sections f) <-> (sections g)).
Proof.
  Admitted.

(* 1d. Exercise 9.9a *)

Definition is_finitely_cyclic {X : UU} (f : X → X) : UU.
Proof.
  Admitted.

Theorem Ex_9_9a {X : UU} (f : X → X) : is_finitely_cyclic f → isweq f.
Proof.
  Admitted.

Theorem hlevelprop (n : nat) (A : UU) : isaprop (isofhlevel n A).
Proof.
  Admitted.

(**************************************************************)

(* For the following exercises you can use the following results from previous exercise sessions without proofs. 
  You can also use `isweq_iso` and `funextsec` from the libr ary.*)

Theorem hlevel_cumulative  {n : nat} {T : UU} (h : isofhlevel n T) : isofhlevel (S n) T.
Proof.
  Admitted.

Lemma contr_to_path {C : UU} (h : iscontr C) (x y : C) : x = y.
Proof.
  Admitted.

(* From here on, all `Admitted.`s should be filled in. *)

(* Exercise 2 *)

(* Show that the definitions of proposition are equivalent. *)

Theorem prop_thm_a {P : UU} : (isaprop P) → (∏ x y : P, x = y).
Proof.
  intro PProp.
  intros p q.
  set (c := PProp p q).
  simpl in c.
  induction c as [cntr _].
  exact cntr.
Defined.

Lemma path_comp_lem {A : UU} {a b : A} (p : a = b) : idpath a = p @ !p.
Proof.
  induction p.
  simpl.
  apply idpath.
Defined.

Theorem prop_thm_b {P : UU} : (∏ x y : P, x = y) → 
(isaprop P).
Proof.
  intro paths.
  unfold isaprop.
  unfold isofhlevel.
  intros p q.
  set (newpaths := λ x y : P, (paths x p) @ !(paths y p)).
  use tpair.
  - exact (newpaths p q).
  - simpl.
    intro e.
    induction e.
    unfold newpaths.
    use path_comp_lem.
Defined.

Theorem prop_thm {P : UU} : (isaprop P) ≃ (∏ x y : P, x = y).
Proof.
  use tpair.
  - exact prop_thm_a.
  - use isweq_iso.
    + exact prop_thm_b.
    + intro p.
      assert (H : ∏ x y : isaprop P, x = y).
      {
        set (H1 := hlevelprop 1 P).
        exact (prop_thm_a H1).
      }
      exact (H (prop_thm_b (prop_thm_a p)) p).
    + intro paths.
      unfold prop_thm_a.
      simpl.
      apply funextsec.
      unfold homot.
      intro p.
      apply funextsec.
      intro q.
      set (Pprop := prop_thm_b paths).
      set (paths_contr := Pprop p q).
      simpl in paths_contr.
      exact (contr_to_path paths_contr (paths p p @ ! paths q p) (paths p q) ).
Defined.

(* Exercise 3 *)

(* Proposition 12.1.4 from Rijke: An equivalence between propositions is (logically equivalent to) a logical equivalence. *)

Theorem Prop_12_1_4 (P Q : hProp) : (P ≃ Q) <-> (P <-> Q).
Proof.
  split.
  - intro e.
    induction e as [f c].
    split.
    + exact f.
    + intro q.
      unfold isweq in c.
      set (cq := c q).
      induction cq as [h _].
      induction h as [p _].
      exact p.
  - intro b.
    induction b as [f g].
    induction P as [P PProp].
    induction Q as [Q QProp].
    simpl in *.
    use tpair.
    + exact f.
    + use isweq_iso.
      * exact g.
      * intro p.
        set (PProp2 := prop_thm_a PProp).
        exact (PProp2 (g (f p)) p).
      * intro q.
        set (QProp2 := prop_thm_a QProp).
        exact (QProp2 (f (g q)) q).
Defined.

(* Exercise 4 *)

(* Show that the dependent product type former commutes with `isaprop`.*)

Theorem prop_commutes_Π {A : UU} {B : A → UU} (p : ∏ x : A, isaprop (B x)) : isaprop (∏ x : A, (B x)).
Proof.
  apply prop_thm_b.
  intros f g.
  apply funextsec.
    intro a.
    set (Ba_is_prop := p a).
    set (Ba_is_prop' := prop_thm_a Ba_is_prop).
    exact (Ba_is_prop' (f a) (g a)).
Defined.

(* Exercise 5 *)

(* Show that isweq f (is-contr f in Rijke) is a proposition. *)

Theorem isweq_is_prop {A B : UU} (f : A → B) : isaprop (isweq f).
Proof.
  unfold isaprop.
  unfold isofhlevel.
  intros w1 w2.
  assert (H : isaprop (isweq f)).
  {
    apply prop_commutes_Π.
    exact (λ y, (hlevelprop 0 (hfiber f y))).
  }
  exact (H w1 w2).
Defined.

(* Exercise 6 *)

(* An equivalence between propositions is (equivalent to) a logical equivalence. *)

Lemma prop_functions_is_prop (P Q : hProp) : isaprop (P → Q).
Proof.
  induction P as [P Pisprop].
  induction Q as [Q Qisprop].
  simpl.
  apply prop_thm_b.
  intros f g.
  use funextsec.
  intro p.
  set (Qisprop' := prop_thm_a Qisprop).
  exact (Qisprop' (f p) (g p)).
Defined.

Lemma prop_prod_is_prop (P Q : hProp) : isaprop (P × Q).
Proof.
  induction P as [P Pisprop].
  induction Q as [Q Qisprop].
  simpl.
  apply prop_thm_b.
  intros x y.
  induction x as [p1 q1].
  induction y as [p2 q2].
  set (Pisprop' := prop_thm_a Pisprop).
  set (Qisprop' := prop_thm_a Qisprop).
  set (p := Pisprop' p1 p2).
  set (q := Qisprop' q1 q2).
  induction p.
  induction q.
  apply idpath.
Defined.

Lemma prop_logeq_is_prop (P Q : hProp) : isaprop (P <-> Q).
Proof.
  set (F := (prop_functions_is_prop P Q)).
  set (G := (prop_functions_is_prop Q P)).
  apply (prop_prod_is_prop ((P → Q) ,, F) ((Q → P) ,, G)).
Defined.

Lemma prop_eq_is_prop (P Q : hProp) : isaprop (P ≃ Q).
Proof.
  set (H := (prop_functions_is_prop P Q)).
  set (I := prop_thm_a H).
  induction P as [P Pisprop].
  induction Q as [Q Qisprop].
  simpl in *.
  apply prop_thm_b.
  intros f g.
  induction f as [f f_weq].
  induction g as [g g_weq].
  set (e := I f g).
  induction e.
  set (J := isweq_is_prop f).
  set (K := prop_thm_a J).
  set (e := K f_weq g_weq).
  induction e.
  apply idpath.
Defined.

Theorem equiv_of_prop {P Q : hProp} : (P ≃ Q) ≃ (P <-> Q).
Proof.
  set (H := Prop_12_1_4 P Q).
  set (E := ((P ≃ Q),,prop_eq_is_prop P Q)).
  set (B := ((P <-> Q),,prop_logeq_is_prop P Q)).
  set (I := Prop_12_1_4 E B).
  set (J := pr2 I).
  simpl in *.
  exact (J H).
Defined.
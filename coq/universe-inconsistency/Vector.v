Require Import Equality.


Set Implicit Arguments.


Inductive Fin : nat -> Type :=
  | First : forall n, Fin (S n)
  | Next  : forall n, Fin n -> Fin (S n).

Lemma Fin_0_inv (A : Type) : Fin 0 -> A.
inversion 1.
Qed.


Definition vector (A : Type) (n : nat) := Fin n -> A.


Definition vcast (A : Type) n (v : vector A n) m (H : n = m) : vector A m :=
  match H in (_ = m) return vector A m with
  | refl_equal => v
  end.

(** Introduce a [vcast] in a binary predicate on [A].

   This lemma introduces a universe inconsistency in Coq trunk 2010-08-10
   but not in Coq 8.3 beta0-1.

   In Coq 8.2pl1 the [dependent destruction] tactic fails. *)
Lemma vcast_intro :
  forall (A : Type) R n m (v1 v2 : vector A m) (H1 H2 : m = n) i,
    (forall i, R (v1 i) (v2 i)) ->
    R (vcast v1 H1 i) (vcast v2 H2 i).
Proof.
intros A R n m v1 v2 H1 H2 i H.
dependent destruction H1.
(** Still consistent universe... *)
dependent destruction H2.
(** Universe inconsistency *)
apply H.
Qed.

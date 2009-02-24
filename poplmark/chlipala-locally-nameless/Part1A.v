(** POPLmark challenge, Part 1A *)

Require Import Arith Binding.

Set Implicit Arguments.


(** * The type language *)

Inductive ty : Set :=
  | Free : var -> ty
  | Bound : nat -> ty
  | Top : ty
  | Arrow : ty -> ty -> ty
  | Forall : ty -> ty -> ty.
(** This should be generated semi-automatically. *)

Notation "@ n" := (Free n) (at level 30).
Notation "# n" := (Bound n) (at level 30).
Infix "-->" := Arrow (right associativity, at level 31).
Notation "'All' t1 , t2" := (Forall t1 t2) (at level 32).

(** Define a type of contexts specialized to contain [ty]s. *)
Definition context : Set := context ty.
(** This should be generated automatically. *)

(** Syntactic notation for context binding *)
Notation "G ,, x <: t" := (Bind G x t) (left associativity, at level 40).

(** Look up a particular binding in a context *)
Notation "[ x <: t ] \in G" := (inContext x t G) (at level 50).

(** Check that a variable is in a context's domain *)
Notation "x \in G" := (inDom x G) (at level 50).

(** Substitution for type variables in types *)
Fixpoint subst (x : nat) (t b : ty) {struct b} : ty :=
  match b with
    | #x' =>
      if eq_nat_dec x x'
	then t
	else b
    | b1 --> b2 => (subst x t b1) --> (subst x t b2)
    | All b1, b2 => All (subst x t b1), subst (S x) t b2
    | _ => b
  end.
(** This should be generated automatically. *)

(** Shorthand notation for substitution *)
Notation "{ x := t }" := (subst x t) (at level 33).
(** This should be generated automatically. *)

(** Well-formedness of types: all free variables are in the context's domain *)
Reserved Notation "G |-- t 'ok'" (at level 50).
(** This should be generated automatically. *)

Inductive wfTy : context -> ty -> Prop :=
  | WF_Free : forall G x,
    x \in G
    -> G |-- @x ok
  | WF_Top : forall G,
    G |-- Top ok
  | WF_Arrow : forall G t1 t2,
    G |-- t1 ok
    -> G |-- t2 ok
    -> G |-- (t1 --> t2) ok
  | WF_Forall : forall G t1 t2,
    G |-- t1 ok
    -> (forall x, ~(x \in G)
      -> G,, x <: t1 |-- {O := @x}t2 ok)
    -> G |-- (All t1, t2) ok
where "G |-- t 'ok'" := (wfTy G t).
(** This should be generated automatically. *)

Hint Constructors wfTy.
(** This should be generated automatically. *)

(** Well-formedness of contexts: no variables are repeated and every variable's associated type is well formed given the context up to that point *)
Notation "|-- G 'ok'" := (wfContext wfTy G) (at level 50).
(** This should be generated automatically. *)


(** * Subtyping judgment *)

Reserved Notation "G |-- t1 <: t2" (at level 50).

Inductive subTy : context -> ty -> ty -> Prop :=
  | SA_Top : forall G t,
    |-- G ok
    -> G |-- t ok
    -> G |-- t <: Top
  | SA_Refl_TVar : forall G x,
    |-- G ok
    -> x \in G
    -> G |-- @x <: @x
  | SA_Trans_TVar : forall G x u t,
    [x <: u] \in G
    -> G |-- u <: t
    -> G |-- @x <: t
  | SA_Arrow : forall G s1 s2 t1 t2,
    G |-- t1 <: s1
    -> G |-- s2 <: t2
    -> G |-- (s1 --> s2) <: (t1 --> t2)
  | SA_All : forall G s1 s2 t1 t2,
    G |-- t1 <: s1
    -> (forall x, ~(x \in G)
      -> G,, x <: t1 |-- {O := @x}s2 <: {O := @x}t2)
    -> G |-- (All s1, s2) <: (All t1, t2)
where "G |-- t1 <: t2" := (subTy G t1 t2).

Hint Constructors subTy.


(** * Lemma A.1 (Reflexivity) *)

(** Lemma A.1 *)
Lemma reflexivity : forall G, |-- G ok
  -> forall t, G |-- t ok
  -> G |-- t <: t.
  induction 2; eauto 6.
  (** Prove by induction on the 2nd hypothesis, followed by logic programming up to depth 6. *)
Qed.


(** * Lemma A.2 (Permutation and Weakening) *)

(** "[D] is valid permutation of [G]." *)
Notation "G ~= D" := (permute wfTy G D) (at level 50).
(** This should be generated automatically. *)

(** Permutations don't affect well-formedness of types *)
Lemma permute_wfTy : forall G t,
  G |-- t ok
    -> forall D, G ~= D
      -> D |-- t ok.
  induction 1; intuition (eauto 10).
Qed.

(** Use this lemma automatically in logic programming. *)
Hint Resolve permute_wfTy.

(** The basic way to prove that a type remains well-formed in a modified context *)
Lemma preweaken_wfTy : forall G t,
  G |-- t ok
  -> forall D, (forall x, x \in G -> x \in D)
  -> D |-- t ok.
  induction 1; intuition eauto 7.
Qed.

Hint Resolve preweaken_wfTy.

(** The context of any correct typing judgment is well-formed. *)
Lemma subTy_wfContext : forall G s t,
  G |-- s <: t
    -> |-- G ok.
  induction 1; auto.
Qed.

(** Two helper lemmas to deal with limitations in Coq's automated first-order reasoning *)
Lemma proj1_wfTy : forall G t P,
  G |-- t ok /\ P
    -> G |-- t ok.
  intuition.
Qed.

Lemma proj2_wfTy : forall G t P,
  P /\ G |-- t ok
    -> G |-- t ok.
  intuition.
Qed.

(** The two types in any correct typing judgment are well-formed. *)
Lemma subTy_wfTy : forall G s t,
  G |-- s <: t
    -> (G |-- s ok)
      /\ (G |-- t ok).
  Hint Resolve proj1_wfTy proj2_wfTy.

  induction 1; intuition eauto 6.
Qed.

(** The combined form above was necessary to have a strong enough induction hypothesis, but we want to break it into two separate lemmas for easier use later. *)
Lemma subTy_wfTy1 : forall G s t,
  G |-- s <: t
    -> G |-- s ok.
  generalize subTy_wfTy; firstorder.
Qed.

Lemma subTy_wfTy2 : forall G s t,
  G |-- s <: t
    -> G |-- t ok.
  generalize subTy_wfTy; firstorder.
Qed.

Hint Resolve subTy_wfContext subTy_wfTy1 subTy_wfTy2.

Lemma permutation : forall G s t,
  G |-- s <: t
    -> forall D, G ~= D
      -> D |-- s <: t.
  induction 1; intuition; eauto; eauto 10.
Qed.

Lemma weakening : forall G s t,
  G |-- s <: t
    -> forall D, |-- G ++ D ok
      -> G ++ D |-- s <: t.
  Hint Extern 1 (_ ++ _,, _ <: _ |-- _ <: _) =>
    match goal with
      | [ |- ?G ++ ?D,, ?x <: ?t |-- _ <: _ ] =>
	apply permutation with (G,, x <: t ++ D);
	  eauto 7
    end.
  (** This [Hint] command advises the automated proving machinery to try a special strategy if it encounters a subtyping goal where the context has the form (G ++ D,, x <: t): use the permutation lemma that we just proved to move around the parts of the context. *)

  induction 1; intuition eauto.
Qed.

(** Weakening by a single binding *)
Lemma weakening1 : forall G s t,
  G |-- s <: t
    -> forall x u, |-- G,, x <: u ok
      -> G,, x <: u |-- s <: t.
  do 6 intro.
  replace (G,, x <: u) with (G ++ (Empty _,, x <: u)); trivial.
  intro.
  apply weakening; auto.
Qed.

(** Weakening specialized to the form associated with the Narrowing lemma *)
Lemma narrowing_weakening : forall G t t',
  G |-- t <: t'
    -> forall x t'' D, |-- G,, x <: t'' ++ D ok
      -> G,, x <: t'' ++ D |-- t <: t'.
  intros.
  eapply weakening; eauto.
  eapply weakening1; eauto.
Qed.

Hint Resolve narrowing_weakening.


(** * Specialized proof automation tactics *)

(** ** Using injectivity of the [ty] constructors *)

Ltac ty_injections :=
  repeat match goal with
	   | [ H : @ _ = @ _ |- _ ] => injection H; clear H; intros
	   | [ H : _ --> _ = _ --> _ |- _ ] => injection H; clear H; intros
	   | [ H : All _, _ = All _, _ |- _ ] => injection H; clear H; intros
	 end.
(** For instance, if we ever see a hypothesis [t1 --> t2 = s1 --> s2], we want to replace it with hypotheses [t1 = s1] and [t2 = s2]. *)

(** ** Replacing known subtypes of [Top] with [Top] *)

(** Slightly ugly form of the [Top_sub] lemma to follow, chosen to work properly with the [induction] tactic *)
Lemma Top_sub' : forall G T T',
  G |-- T <: T'
    -> T = Top
    -> T' = Top.
  induction 1; intuition; try discriminate.
Qed.

(** Any subtype of [Top] is [Top] *)
Lemma Top_sub : forall G T,
  G |-- Top <: T
    -> T = Top.
  generalize Top_sub'; firstorder.
Qed.

(** Replace all types known to be [Top], clearing the now-irrelevant subtyping judgments that led us to do so. *)
Ltac discover_Top :=
  repeat match goal with
	   | [ H : _ |-- Top <: _ |- _ ] =>
	     generalize (Top_sub H); clear H; intro
	 end.

(** ** The overall simplification tactic *)

Ltac ty_simpl :=
  repeat progress (ty_injections; discover_Top; binding_simpl).
(** As long as we're modifying the goal, continue using injectivity, [Top]-replacement, and the [Binding] module's simplification tactic. *)


(** * Lemma A.3 (Transitivity and Narrowing) *)

(** Replacing a type binding in a context doesn't affect type well-formedness. *)
Lemma narrowing_wfTerm : forall G x t1 D t,
  G,, x <: t1 ++ D |-- t ok
    -> forall t2, G,, x <: t2 ++ D |-- t ok.
  intros; eapply narrowing_wfTerm; eauto.
Qed.
(** This should be generated automatically. *)

Hint Resolve narrowing_wfTerm.
(** This should be generated automatically. *)

(** Here's the Narrowing part of the Transitivity/Narrowing lemma, with transitivity assumed for the current type. *)
Lemma narrowing' : forall Q,
  (forall (G : context) (S T : ty),
    (G |-- S <: Q) -> (G |-- Q <: T) -> G |-- S <: T) ->
  forall (G G' : context) (M N : ty),
    (G' |-- M <: N) ->
    forall (x : var) (D : context) (P : ty),
      G' = (G,, x <: Q ++ D) -> (G |-- P <: Q) -> G,, x <: P ++ D |-- M <: N.
  induction 2; intros; ty_simpl;
  (** We'll proceed by induction on the [G' |-- M <: N] derivation and simplify each case before... *)
    try (apply SA_All;
      [auto
	| intros; rewrite <- weaken_bind_assoc; eauto]);
    (** For the SA_All case, we give more detail of the proof, in particular, use the associativity of context operations to rewrite a context advantageously. *)
    try match goal with
	  | [ _ : [_ <: _] \in _,, _ <: _ ++ _ |- _,, ?x0 <: _ ++ _ |-- @?x <: _ ] =>
	    destruct (var_eq_dec x x0); ty_simpl;
	      [eapply SA_Trans_TVar; eauto 6
		| eauto]
	end;
    (** For the SA_Trans_TVar case, we proceed by case analysis on whether the two variables involved are equal. *)
    eauto 6.
    (** The remaining cases are solved automatically. *)
Qed.

Hint Resolve narrowing'.

(** Syntactic size function for types *)
Fixpoint tySize (t : ty) : nat :=
  match t with
    | Arrow t1 t2 => S (tySize t1 + tySize t2)
    | Forall t1 t2 => S (tySize t1 + tySize t2)
    | _ => 1
  end.
(** This should be generated automatically. *)

(** Subsitution of a free variable doesn't change type size. *)
Lemma tySize_subst : forall x' b x, tySize({x := @x'}b) = tySize b.
  induction b; simpl; intuition.
  destruct (eq_nat_dec x n); auto.
Qed.
(** This should be generated automatically. *)

(** A syntactic induction principle for types that considers alpha-variation *)
Theorem ty_ind_syntactic : forall P : ty -> Prop,
  (forall v : var, P (@ v)) ->
  (forall n : nat, P (#n)) ->
  P Top ->
  (forall t : ty, P t -> forall t0 : ty, P t0 -> P (t --> t0)) ->
  (forall t : ty, P t -> forall t0 : ty, (forall x, P ({0 := @x}t0)) -> P (All t, t0)) ->
  forall t : ty, P t.
  intros.

  assert (forall n t, tySize t <= n -> P t).
  clear t.
  induction n.
  destruct t; simpl; intros; wrong; omega.
  destruct t; simpl; intros; auto.

  apply H2; apply IHn; omega.

  apply H3.
  apply IHn; omega.
  intro; apply IHn.
  rewrite tySize_subst; omega.
  
  eauto.
Qed.
(** This should be generated automatically. *)

(** A useful hint to get the Transitivity proof to take advantage of Narrowing *)
Lemma use_narrowing : forall G x t1 t2,
  G ++ Empty _ |-- {0 := @x} t1 <: {0 := @x} t2
  -> G |-- {0 := @x} t1 <: {0 := @x} t2.
  trivial.
Qed.

Hint Resolve use_narrowing.

(** The big lemma!  It's formulated using both seemingly pointless equalities, which are necessary to make [induction] work; and an implication for the second conjunct that assumes the first conjunct, to avoid the need to re-prove it. *)
Lemma transitivity_and_narrowing : forall Q,
  (forall G S T Q', G |-- S <: Q'
    -> Q' = Q
    -> G |-- Q <: T
      -> G |-- S <: T)
  /\ ((forall G S T, G |-- S <: Q
    -> G |-- Q <: T
      -> G |-- S <: T)
  -> forall G G' M N, G' |-- M <: N
    -> forall x D P, G' = (G,, x <: Q ++ D)
      -> G |-- P <: Q
	-> G,, x <: P ++ D |-- M <: N).
  induction Q using ty_ind_syntactic; split; eauto; induction 1; intuition; ty_simpl; eauto;
    match goal with
      | [ H : _ |-- _ --> _ <: _ |- _ ] =>
	inversion H; subst; eauto
        (** Here, we are inverting a proof of the form [G |-- t1 --> t2 <: s]. *)
      | [ H : _ |-- All _, _ <: _ |- _ ] =>
	inversion H; subst; eauto;
	  apply SA_All; intuition eauto;
	    match goal with
	      | [ H : forall x : var, _ /\ _, x : var |- _ ] =>
		generalize (H x); intuition; eauto 7
		(** We need to instantiate explicitly one part of the inductive hypothesis to make the conjunction inside accessible to automatic propositional reasoning. *)
	    end
    end.
Qed.

Theorem transitivity : forall Q G S T,
  G |-- S <: Q
    -> G |-- Q <: T
      -> G |-- S <: T.
  generalize transitivity_and_narrowing; firstorder.
Qed.

Lemma narrowing : forall Q G M N x D P, G,, x <: Q ++ D |-- M <: N
  -> G |-- P <: Q
    -> G,, x <: P ++ D |-- M <: N.
  intros.
  generalize (transitivity_and_narrowing Q).
  firstorder; eauto.
Qed.

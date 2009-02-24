(** Generic variable binding support *)

Require Import Arith Omega.
Require Import Max.

Set Implicit Arguments.

Definition var := nat.
Definition var_eq_dec := eq_nat_dec.

Ltac wrong := assert False; [idtac | tauto].

Section Contexts.
  Variable term : Set.

  Inductive context : Set :=
    | Empty : context
    | Bind : context -> var -> term -> context.

  Notation "G , x <: t" := (Bind G x t) (left associativity, at level 40).


  (** * Well-formedness *)

  Inductive inContext : var -> term -> context -> Prop :=
    | In_Eq : forall x t G, inContext x t (G, x <: t)
    | In_Neq : forall x t G x' t', inContext x t G
      -> inContext x t (G, x' <: t').

  Hint Constructors inContext.

  Notation "[ x <: t ] \in G" := (inContext x t G) (at level 50).

  Definition inDom x G := exists t, [x <: t] \in G.

  Notation "x \in G" := (inDom x G) (at level 50).

  Variable wfTerm : context -> term -> Prop.
  Notation "G |-- t 'ok'" := (wfTerm G t) (at level 50).

  Reserved Notation "|-- G 'ok'" (at level 50).

  Inductive wfContext : context -> Prop :=
    | WF_Empty : |-- Empty ok
    | WF_Bind : forall G x t,
      |-- G ok
      -> ~(x \in G)
      -> G |-- t ok
      -> |-- (G, x <: t) ok
  where "|-- G 'ok'" := (wfContext G).

  Hint Constructors wfContext.


  (** * Permutation and weakening *)

  Inductive insertInto : var -> term -> context -> context -> Prop :=
    | II_Head : forall x t G,
      G |-- t ok
      -> insertInto x t G (G, x <: t)
    | II_Skip : forall x t G x' t' G',
      insertInto x t G G'
      -> insertInto x t (G, x' <: t') (G', x' <: t').

  Hint Constructors insertInto.

  Inductive permute : context -> context -> Prop :=
    | PM_Empty : permute Empty Empty
    | PM_Bind : forall G x t G' G'',
      permute G G'
      -> insertInto x t G' G''
      -> permute (G, x <: t) G''.

  Hint Constructors permute.

  Lemma insertInto_inContext : forall x t G G',
    insertInto x t G G'
    -> forall x' t', [x' <: t'] \in (G, x <: t)
      -> [x' <: t'] \in G'.
    induction 1; intuition.

    inversion H0; subst; eauto.
    inversion H4; subst; eauto.
  Qed.

  Lemma permute_inContext : forall G D,
    permute G D
    -> forall x t, [x <: t] \in G
      -> [x <: t] \in D.
    induction 1; intuition.
    apply insertInto_inContext with x t G'; trivial.

    inversion H1; subst; auto.
  Qed.

  Lemma permute_inDom : forall G D,
    permute G D
    -> forall x, x \in G
      -> x \in D.
    unfold inDom.
    generalize permute_inContext.
    firstorder.
  Qed.

  Lemma permute_inDom_neg : forall G D,
    permute G D
    -> forall x, ~x \in D
      -> ~x \in G.
    generalize permute_inDom.
    firstorder.
  Qed.

  Hint Resolve permute_inContext permute_inDom permute_inDom_neg.

  Lemma insertInto_inContext' : forall x t G G',
    insertInto x t G G'
    -> forall x' t', [x' <: t'] \in G'
      -> [x' <: t'] \in (G, x <: t).
    induction 1; intuition.
    
    inversion H0; subst; eauto.
    generalize (IHinsertInto _ _ H4); intro Hin.
    inversion Hin; subst; auto.
  Qed.

  Lemma permute_inContext' : forall G D,
    permute G D
    -> forall x t, [x <: t] \in D
      -> [x <: t] \in G.
    induction 1; intuition.
    generalize (insertInto_inContext' H0 H1); intro Hin.
    
    inversion Hin; subst; auto.
  Qed.

  Lemma permute_inDom' : forall G D,
    permute G D
    -> forall x, x \in D
      -> x \in G.
    unfold inDom.
    generalize permute_inContext'.
    firstorder.
  Qed.

  Hint Resolve permute_inDom'.

  Hypothesis preweaken_wfTerm : forall G t,
    G |-- t ok
      -> forall D, (forall x, x \in G -> x \in D)
	-> D |-- t ok.

  Lemma permute_wfTy : forall G t,
    G |-- t ok
      -> forall D, permute G D
	-> D |-- t ok.
    eauto.
  Qed.

  Hint Resolve permute_wfTy.
  
  Lemma inDom_Bind : forall x t G,
    [x <: t] \in G
    -> forall x' t', [x <: t] \in G, x' <: t'.
    eauto.
  Qed.

  Lemma inContext_Bind : forall x G,
    x \in G
    -> forall x' t', x \in G, x' <: t'.
    generalize inDom_Bind.
    firstorder.
  Qed.

  Lemma inContext_Bind_neg : forall x G x' t',
    ~(x \in G, x' <: t')
    -> ~(x \in G).
    intros.
    intro.
    apply H.
    apply inContext_Bind; trivial.
  Qed.

  Hint Resolve inContext_Bind inContext_Bind_neg.

  Fixpoint weaken (G1 G2 : context) {struct G2} : context :=
    match G2 with
      | Empty => G1
      | G2', x <: t => (weaken G1 G2'), x <: t
    end.

  Infix "++" := weaken (left associativity, at level 40).

  Lemma weaken_inContext : forall G x t,
    [x <: t] \in G
    -> forall D, |-- (G ++ D) ok
      -> [x <: t] \in (G ++ D).
    induction D; simpl; auto.
    inversion 1; subst; auto.
  Qed.

  Lemma weaken_inDom : forall G x,
    x \in G
    -> forall D, |-- (G ++ D) ok
      -> x \in (G ++ D).
    generalize weaken_inContext; firstorder.
  Qed.

  Hint Resolve weaken_inContext weaken_inDom.

  Lemma permute_refl : forall G,
    |-- G ok
      -> permute G G.
    induction 1; eauto.
  Qed.

  Hint Resolve permute_refl.

  Lemma weaken_wfTy : forall G t,
    G |-- t ok
      -> forall D, |-- (G ++ D) ok
	-> G ++ D |-- t ok.
    eauto.
  Qed.

  Hint Resolve weaken_wfTy.

  Lemma insertInto_inContext2 : forall x t G G',
    insertInto x t G G'
    -> forall x' t', [x' <: t'] \in G
      -> [x' <: t'] \in G'.
    induction 1; intuition.

    inversion H0; subst; eauto.
  Qed.

  Hint Resolve insertInto_inContext2.

  Lemma insertInto_inDom : forall x t G G',
    insertInto x t G G'
    -> forall x', x' \in G
      -> x' \in G'.
    intros.
    destruct H0.
    red.
    eauto.
  Qed.

  Lemma insertInto_wfTy : forall x t G G',
    insertInto x t G G'
    -> |-- G ok
    -> forall t', G |-- t' ok
    -> G' |-- t' ok.
    eauto 6.
  Qed.

  Lemma insertInto_wfContext : forall x t G G',
    insertInto x t G G'
    -> |-- G ok
    -> ~x \in G
    -> |-- G' ok.
    induction 1; auto.
    inversion 1; subst.
    intro Hin.
    constructor; eauto.
    intro.
    destruct H1 as [t'' Ht''].
    generalize (insertInto_inContext' H Ht''); intro Hin'.
    inversion Hin'; subst.
    apply Hin; exists t'; auto.
    apply H5.
    exists t''; auto.
    
    eapply insertInto_wfTy; eauto.
  Qed.

  Hint Resolve insertInto_wfContext.

  Lemma permute_wfContext : forall G D,
    permute G D
    -> |-- G ok
    -> |-- D ok.
    induction 1; inversion 1; subst; eauto.
    eapply insertInto_wfContext; eauto.
  Qed.

  Hint Resolve permute_wfContext.

  Lemma split_inDom : forall x G y t,
    x \in G, y <: t
    -> x = y \/ (x \in G).
    intros.
    destruct H as [t' Ht'].
    inversion Ht'; subst; auto.
    right.
    exists t'; auto.
  Qed.

  Lemma head_inDom : forall x G t,
    x \in G, x <: t.
    intros.
    exists t; auto.
  Qed.

  Lemma cons_inDom : forall x G y t,
    x \in G
    -> x \in G, y <: t.
    intros.
    destruct H as [t' Ht'].
    exists t'; auto.
  Qed.

  Hint Resolve head_inDom cons_inDom.

  Lemma multiSwap : forall G x t D,
    |-- G ++ D ok
    -> ~x \in G ++ D
    -> G |-- t ok
    -> permute (G, x <: t ++ D) (G ++ D, x <: t).
    induction D; simpl; intuition.

    apply PM_Bind with (G ++ D, x <: t).
    inversion H; subst.
    apply IHD; eauto.
  
    inversion H; subst.
    eauto.
  Qed.

  Hint Resolve multiSwap.

  Lemma multiSwap' : forall G x t D,
    |-- G ++ D ok
    -> ~x \in G ++ D
    -> G |-- t ok
    -> permute (G ++ D, x <: t) (G, x <: t ++ D).
    induction D; simpl; intuition.

    apply PM_Bind with (G ++ D, v <: t0); auto.

    apply II_Skip.
    clear IHD H H0.
    induction D; simpl; intuition.
  Qed.

  Hint Resolve multiSwap'.

  Lemma move_wfContext : forall G t,
    G |-- t ok
    -> forall D, |-- G ++ D ok
    -> forall x, ~x \in G ++ D
    -> |-- G, x <: t ++ D ok.
    induction D; simpl; intuition.

    inversion H0; subst.
    constructor; eauto.
    intro.
    assert (v \in G ++ D, x <: t).
    apply permute_inDom with (G, x <: t ++ D); auto.

    destruct (split_inDom H3); subst; auto.

    apply preweaken_wfTerm with (G ++ D); intuition.
    apply permute_inDom with (G ++ D, x <: t); auto.
  Qed.

  Hint Resolve move_wfContext.

  Lemma weaken_inContext2 : forall x t G D,
    [x <: t] \in G ++ D
    -> [x <: t] \in G \/ [x <: t] \in D.
    induction D; simpl; intuition.
    inversion H; subst; eauto.
    intuition.
  Qed.

  Lemma weaken_inDom2 : forall x G D,
    x \in G ++ D
    -> x \in G \/ x \in D.
    generalize weaken_inContext2; firstorder.
  Qed.

  Lemma weaken_inContext3 : forall x t G D,
    [x <: t] \in G
    -> [x <: t] \in G ++ D.
    induction D; simpl; intuition.
  Qed.

  Lemma weaken_inDom3 : forall x G D,
    x \in G
    -> x \in G ++ D.
    generalize weaken_inContext3; firstorder.
  Qed.

  Lemma weaken_inContext4 : forall x t G D,
    [x <: t] \in D
    -> [x <: t] \in G ++ D.
    induction D; simpl; intuition.
    inversion H.
    inversion H; simpl; eauto.
  Qed.

  Lemma weaken_inDom4 : forall x G D,
    x \in D
    -> x \in G ++ D.
    generalize weaken_inContext4; firstorder.
  Qed.

  Hint Resolve weaken_inDom2 weaken_inDom3 weaken_inDom4.

  Lemma narrowing_wfTerm : forall G x t1 D t,
    G, x <: t1 ++ D |-- t ok
      -> forall t2, G, x <: t2 ++ D |-- t ok.
    intros.
    apply preweaken_wfTerm with (G, x <: t1 ++ D); intuition.
    destruct (weaken_inDom2 _ _ H0); eauto.
    destruct (split_inDom H1); subst; eauto.
  Qed.

  Hint Resolve narrowing_wfTerm.

  Lemma narrowing_inDom : forall v G x t1 D,
    v \in G, x <: t1 ++ D
    -> forall t2, v \in G, x <: t2 ++ D.
    induction D; simpl; intuition;
      destruct (split_inDom H); subst; eauto.
  Qed.

  Hint Resolve narrowing_inDom.

  Lemma narrowing_wfContext : forall G x t1 D,
    |-- G, x <: t1 ++ D ok
      -> forall t2, G |-- t2 ok
	-> |-- G, x <: t2 ++ D ok.
    intros.
    
    induction D; simpl in *; intuition.
    inversion H; subst; auto.
    
    inversion H; subst.
    constructor; eauto.
  Qed.

  Hint Resolve narrowing_wfContext.

  Lemma notBound_weaken : forall G x t D,
    |-- G, x <: t ++ D ok
      -> ~x \in G.
    induction D; simpl; intuition;
      inversion H; auto.
  Qed.

  Hint Resolve notBound_weaken.

  Lemma inContext_contra : forall x t G,
    [x <: t] \in G
    -> ~x \in G
    -> False.
    intros.
    apply H0.
    red.
    eauto.
  Qed.

  Hint Resolve inContext_contra.

  Lemma inContext_inDom : forall x t G,
    [x <: t] \in G
    -> x \in G.
    intros.
    red; eauto.
  Qed.

  Lemma wfContext_invert1 : forall G x t,
    |-- G, x <: t ok
      -> |-- G ok.
    inversion 1; trivial.
  Qed.
  
  Hint Resolve wfContext_invert1.

  Lemma squeeze_inContext : forall v G t D,
    [v <: t] \in G, v <: t ++ D.
    induction D; simpl; intuition.
  Qed.

  Lemma squeeze_inDom : forall v G t D,
    v \in G, v <: t ++ D.
    generalize squeeze_inContext; firstorder.
  Qed.

  Hint Resolve squeeze_inDom.

  Lemma narrowing_eq : forall x t D G t',
    |-- G, x <: t' ++ D ok
    -> [x <: t] \in G, x <: t' ++ D
    -> t = t'.
    induction D; simpl; intuition.
    
    inversion H0; subst; trivial.
    wrong.
    inversion H; eauto.

    inversion H0; subst; eauto.
    wrong.
    inversion H; subst.
    auto.
  Qed.

  Lemma weaken_bind_assoc : forall D G v t,
    G ++ (D, v <: t) = G ++ D, v <: t.
    induction D; simpl; intuition.
  Qed.

  Lemma wfContext_invert_weaken : forall D G,
    |-- G ++ D ok
      -> |-- G ok.
    induction D; intuition.
    rewrite weaken_bind_assoc in H.
    eauto.
  Qed.

  Hint Resolve wfContext_invert_weaken.

  Lemma narrowing_neq : forall x t G x' t' D,
    [x <: t] \in G, x' <: t' ++ D
    -> x <> x'
    -> forall t'', [x <: t] \in G, x' <: t'' ++ D.
    induction D; simpl; intuition;
      inversion H; subst; intuition.
  Qed.

  Hint Resolve narrowing_neq.

  Lemma switchBase_inDom : forall x G x' t D,
    (forall x0, x0 \in G -> x0 \in D)
    -> x \in G, x' <: t
    -> x \in D, x' <: t.
    intros.
    destruct (split_inDom H0); subst; eauto.
  Qed.

  Lemma switchTerm_inDom : forall x G x' t t',
    x \in G, x' <: t
    -> x \in G, x' <: t'.
    intros.
    destruct (split_inDom H); subst; eauto.
  Qed.

  Lemma switchWeaken_inDom' : forall D x G,
    x \in G ++ D
    -> forall G', (forall x, x \in G -> x \in G')
    -> x \in G' ++ D.
    induction D; simpl; intuition.
    destruct (split_inDom H); subst; eauto.
  Qed.

  Lemma switchWeaken_inDom : forall D x x' t G,
    x \in G, x' <: t ++ D
    -> forall t', x \in G, x' <: t' ++ D.
    intros.
    eapply switchWeaken_inDom'; eauto.
    intros.
    destruct (split_inDom H0); subst; eauto.
  Qed.
End Contexts.

Infix "++" := weaken (left associativity, at level 40).

Hint Constructors inContext wfContext insertInto permute.

Hint Resolve permute_inContext.
Hint Resolve weaken_inContext weaken_inContext2 weaken_inContext3 weaken_inContext4.

Hint Resolve permute_inDom weaken_inDom inContext_inDom.
Hint Resolve switchTerm_inDom switchBase_inDom switchWeaken_inDom.

Hint Resolve permute_wfContext move_wfContext wfContext_invert_weaken.

Hint Resolve multiSwap multiSwap'.

Hint Resolve narrowing_wfContext narrowing_neq.

Ltac narrowing_eq :=
  repeat match goal with
	   | [ H : inContext ?x0 ?u (Bind ?G ?x0 ?v ++ ?D) |- _ ] =>
	     assert (u = v);
	       [eapply narrowing_eq; eauto; fail
		 | subst; clear H]
	 end.

Ltac binding_simpl := repeat progress (simpl in *; narrowing_eq; subst; try discriminate).

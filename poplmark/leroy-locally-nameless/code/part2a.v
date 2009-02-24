(** This chapter addresses part 2A of the POPLmark challenge, namely the proof
  of soundness of the $F_{<:}$ type systems without records. *)

Require Import Arith.
Require Import ZArith.
Require Import List.
Require Import extralibrary.
Require Import part1a.

(** * Terms *)

(** We now define the syntax of $F_{<:}$ terms and basic syntactic notions such
  as free variables, substitutions, and well-formedness of terms.
  We follow the same approach used for types in chapter 2.  *)

(** ** Syntax and syntactic operations *)

(** The syntax of terms is defined as follows. 
  As in types, bound variables are represented by de Bruijn indices,
  while free variables are represented by names.  Bound term variables
  and bound type variables are numbered independently.  In a
  lambda-abstraction [TFun t a], the term variable [Var 0] is bound in
  [a].  In a type abstraction [TApp t a], the type variable [TVar 0]
  is bound in [a]. *)

Inductive term: Set :=
  | Param: name -> term
  | Var: nat -> term
  | Fun: type -> term -> term
  | App: term -> term -> term
  | TFun: type -> term -> term
  | TApp: term -> type -> term.

(** The free names of a term include both type names and term names. *)

Fixpoint fv_term (a: term) : list name :=
  match a with
  | Param v => v :: nil
  | Var n => nil
  | Fun t a1 => fv_type t ++ fv_term a1
  | App a1 a2 => fv_term a1 ++ fv_term a2
  | TFun t a1 => fv_type t ++ fv_term a1
  | TApp a1 t => fv_term a1 ++ fv_type t
  end.

(** There are 4 substitution operations over terms,
  depending on whether we are substituting a named variable ([psubst_])
  or a de Bruijn variable ([vsubst_]), and whether we are substituting
  a term for a term variable ([_term]) or a type for a type variable
  ([_tety]). *)

Fixpoint vsubst_term (a: term) (x: nat) (b: term) {struct a} : term :=
  match a with
  | Param v => Param v
  | Var n =>
      match compare_nat n x with
      | Nat_less _ => Var n
      | Nat_equal _ => b
      | Nat_greater _ => Var (pred n)
      end
  | Fun t a1 => Fun t  (vsubst_term a1 (S x) b)
  | App a1 a2 => App (vsubst_term a1 x b) (vsubst_term a2 x b)
  | TFun t a1 => TFun t (vsubst_term a1 x b)
  | TApp a1 t => TApp (vsubst_term a1 x b) t
  end.

Fixpoint psubst_term (a: term) (x: name) (b: term) {struct a} : term :=
  match a with
  | Param v => if eq_name v x then b else Param v
  | Var n => Var n
  | Fun t a1 => Fun t (psubst_term a1 x b)
  | App a1 a2 => App (psubst_term a1 x b) (psubst_term a2 x b)
  | TFun t a1 => TFun t (psubst_term a1 x b)
  | TApp a1 t => TApp (psubst_term a1 x b) t
  end.

Fixpoint vsubst_tety (a: term) (x: nat) (b: type) {struct a} : term :=
  match a with
  | Param v => Param v
  | Var n => Var n
  | Fun t a1 => Fun (vsubst_type t x b)  (vsubst_tety a1 x b)
  | App a1 a2 => App (vsubst_tety a1 x b) (vsubst_tety a2 x b)
  | TFun t a1 => TFun (vsubst_type t x b) (vsubst_tety a1 (S x) b)
  | TApp a1 t => TApp (vsubst_tety a1 x b) (vsubst_type t x b)
  end.

Fixpoint psubst_tety (a: term) (x: name) (b: type) {struct a} : term :=
  match a with
  | Param v => Param v
  | Var n => Var n
  | Fun t a1 => Fun (psubst_type t x b)  (psubst_tety a1 x b)
  | App a1 a2 => App (psubst_tety a1 x b) (psubst_tety a2 x b)
  | TFun t a1 => TFun (psubst_type t x b) (psubst_tety a1 x b)
  | TApp a1 t => TApp (psubst_tety a1 x b) (psubst_type t x b)
  end.

(** Here are the two ``freshening'' operations that replace the bound variable
  0 with a term or type name, respectively. *)

Definition freshen_term (a: term) (x: name) : term :=
  vsubst_term a 0 (Param x).

Definition freshen_tety (a: term) (x: name) : term :=
  vsubst_tety a 0 (Tparam x).

(** Substitutions and freshening play well with free variables. *)

Hint Resolve fv_type_vsubst_type.

Lemma fv_term_vsubst_term:
  forall x a n b, In x (fv_term a) -> In x (fv_term (vsubst_term a n b)).
Proof.
  induction a; simpl; intros; auto;
  try contradiction;
  elim (in_app_or _ _ _ H); eauto. 
Qed. 

Lemma fv_term_vsubst_tety:
  forall x a n b, In x (fv_term a) -> In x (fv_term (vsubst_tety a n b)).
Proof.
  induction a; simpl; intros; auto;
  try contradiction;
  elim (in_app_or _ _ _ H); eauto. 
Qed. 

Lemma fv_term_freshen_term:
  forall x a y, In x (fv_term a) -> In x (fv_term (freshen_term a y)).
Proof.
  intros; unfold freshen_term; apply fv_term_vsubst_term; auto.
Qed.

Lemma fv_term_freshen_tety:
  forall x a y, In x (fv_term a) -> In x (fv_term (freshen_tety a y)).
Proof.
  intros; unfold freshen_tety; apply fv_term_vsubst_tety; auto.
Qed.

(** Swaps of two names in a term. *)

Fixpoint swap_term (u v: name) (a: term) {struct a} : term :=
  match a with
  | Param x => Param (swap u v x)
  | Var n => Var n
  | Fun t a1 => Fun (swap_type u v t) (swap_term u v a1)
  | App a1 a2 => App (swap_term u v a1) (swap_term u v a2)
  | TFun t a1 => TFun (swap_type u v t) (swap_term u v a1)
  | TApp a1 t => TApp (swap_term u v a1) (swap_type u v t)
  end.

(** Swaps commute with the free variables operation. *)

Lemma in_fv_term_swap:
  forall u v x a,
  In x (fv_term a) <-> In (swap u v x) (fv_term (swap_term u v a)).
Proof.
  induction a; simpl; eauto.
  intuition. subst n. tauto.
  left. eapply swap_inj; eauto.
  tauto.
  generalize (in_fv_type_swap u v x t); eauto.
  generalize (in_fv_type_swap u v x t); eauto.
  generalize (in_fv_type_swap u v x t); eauto.
Qed.

Hint Resolve swap_type_not_free.

Lemma swap_term_not_free:
  forall u v a, ~In u (fv_term a) -> ~In v (fv_term a) -> swap_term u v a = a.
Proof.
  induction a; simpl; intros; decEq; eauto 6.
  unfold swap; repeat rewrite eq_name_false; tauto.
Qed.

(** Swaps are self-inverse. *)

Hint Resolve swap_inv swap_type_inv.

Lemma swap_term_inv: forall u v a, swap_term u v (swap_term u v a) = a.
Proof.
  induction a; simpl; decEq; auto. 
Qed.

(** Swaps commute with substitutions and freshening. *)

Lemma vsubst_term_swap:
  forall u v a n b,
  swap_term u v (vsubst_term a n b) =
  vsubst_term (swap_term u v a) n (swap_term u v b).
Proof.
  intros u v.
  induction a; simpl; intros; try (decEq; eauto).
  case (compare_nat n n0); intros; auto.
Qed.

Lemma vsubst_tety_swap:
  forall u v a n b,
  swap_term u v (vsubst_tety a n b) =
  vsubst_tety (swap_term u v a) n (swap_type u v b).
Proof.
  intros u v.
  generalize vsubst_type_swap; intro.
  induction a; simpl; intros; try (decEq; eauto).
Qed.

Lemma freshen_term_swap:
  forall u v a x,
  swap_term u v (freshen_term a x) =
  freshen_term (swap_term u v a) (swap u v x).
Proof.
  intros; unfold freshen_term. 
  change (Param (swap u v x)) with (swap_term u v (Param x)).
  apply vsubst_term_swap. 
Qed.

Lemma freshen_tety_swap:
  forall u v a x,
  swap_term u v (freshen_tety a x) =
  freshen_tety (swap_term u v a) (swap u v x).
Proof.
  intros; unfold freshen_tety. 
  change (Tparam (swap u v x)) with (swap_type u v (Tparam x)).
  apply vsubst_tety_swap. 
Qed.

(** ** Well-formedness of terms *)

(** A term is well-formed in a typing environment if:
  - all types contained within are well-formed as per [wf_type];
  - all names [n] appearing free in a [Param n] subterm are of kind [TERM]
    and are bound in the environment;
  - it does not contain free de Bruijn variables.
*)

Inductive wf_term: typenv -> term -> Prop :=
  | wf_term_param: forall e x,
      kind x = TERM -> In x (dom e) ->
      wf_term e (Param x)
  | wf_term_fun: forall e t a,
      wf_type e t ->
      (forall x,
       kind x = TERM ->
       ~In x (fv_term a) -> ~In x (dom e) ->
       wf_term ((x, t) :: e) (freshen_term a x)) ->
      wf_term e (Fun t a)
  | wf_term_app: forall e a1 a2,
      wf_term e a1 -> wf_term e a2 ->
      wf_term e (App a1 a2)
  | wf_term_tfun: forall e t a,
      wf_type e t ->
      (forall x,
       kind x = TYPE ->
       ~In x (fv_term a) -> ~In x (dom e) ->
       wf_term ((x, t) :: e) (freshen_tety a x)) ->
      wf_term e (TFun t a)
  | wf_term_tapp: forall e a t,
      wf_term e a -> wf_type e t ->
      wf_term e (TApp a t).

(** A term well formed in [e] has all its free names in the domain of [e]. *)

Lemma fv_wf_term: forall x e t, wf_term e t -> In x (fv_term t) -> In x (dom e).
Proof.
  induction 1; simpl; intros.
  replace x with x0. auto. tauto.
  (* fun *)
  elim (in_app_or _ _ _ H2); intro.
  eapply fv_wf_type; eauto.
  destruct (fresh_name TERM (x :: fv_term a ++ dom e)) as [y [F K]].
  assert (In x (dom ((y, t) :: e))). 
    apply H1; eauto. apply fv_term_freshen_term. auto. 
  simpl dom in H4. eauto.
  (* app *)
  elim (in_app_or _ _ _ H1); auto.
  (* tfun *)
  elim (in_app_or _ _ _ H2); intro.
  eapply fv_wf_type; eauto.
  destruct (fresh_name TYPE (x :: fv_term a ++ dom e)) as [y [F K]].
  assert (In x (dom ((y, t) :: e))). 
    apply H1; eauto. apply fv_term_freshen_tety. auto. 
  simpl dom in H4; eauto.
  (* tapp *)
  elim (in_app_or _ _ _ H1); intro.
  auto.
  eapply fv_wf_type; eauto.
Qed.

(** Well-formedness is stable under swaps. *)

Lemma wf_term_swap:
  forall u v, kind u = kind v -> 
  forall e a, wf_term e a -> wf_term (swap_env u v e) (swap_term u v a).
Proof.
  intros u v SAMEKIND.
  induction 1; simpl; intros.
  apply wf_term_param. 
    rewrite swap_kind; auto.
    generalize (in_dom_swap u v x e); tauto.
  apply wf_term_fun.
    apply wf_type_swap; auto. 
    intros. set (x' := swap u v x).
    assert (swap u v x' = x). unfold x'; apply swap_inv.
    replace ((x, swap_type u v t) :: swap_env u v e)
       with (swap_env u v ((x', t) :: e)).
    replace (freshen_term (swap_term u v a) x)
       with (swap_term u v (freshen_term a x')).
    apply H1. unfold x'; rewrite swap_kind; auto.
    generalize (in_fv_term_swap u v x' a). rewrite <- H5 in H3. tauto.
    generalize (in_dom_swap u v x' e). rewrite <- H5 in H4. tauto.
    rewrite freshen_term_swap. congruence.
    simpl. congruence.
  apply wf_term_app; auto.
  apply wf_term_tfun.
    apply wf_type_swap; auto. 
    intros. set (x' := swap u v x).
    assert (swap u v x' = x). unfold x'; apply swap_inv.
    replace ((x, swap_type u v t) :: swap_env u v e)
       with (swap_env u v ((x', t) :: e)).
    replace (freshen_tety (swap_term u v a) x)
       with (swap_term u v (freshen_tety a x')).
    apply H1. unfold x'; rewrite swap_kind; auto.
    generalize (in_fv_term_swap u v x' a). rewrite <- H5 in H3. tauto.
    generalize (in_dom_swap u v x' e). rewrite <- H5 in H4. tauto.
    rewrite freshen_tety_swap. congruence.
    simpl. congruence.
  apply wf_term_tapp; auto. apply wf_type_swap; auto.
Qed.

(** A term well-formed in [e] remains well-formed if extra bindings are added to [e]. *)

Lemma wf_term_env_incr:
  forall e a, wf_term e a -> forall e', incl (dom e) (dom e') -> wf_term e' a.
Proof.
  generalize wf_type_env_incr; intro.
  induction 1; simpl; intros.
  constructor; auto.
  constructor; eauto. intros. apply H2; eauto. simpl; apply incl_cons2; auto. 
  constructor; auto.
  constructor; eauto. intros. apply H2; eauto. simpl; apply incl_cons2; auto.
  constructor; eauto.
Qed.

(** Here are two admissible rules that prove the well-formedness of [Fun] and [TFun]
  abstractions.  These rules are similar to the [wf_term_fun] and
  [wf_term_tfun] rules, but with a premise of the form ``there exists
  a name'' instead of the original ``for all names''.  *)

Lemma wf_term_fun':
  forall e x t a,
  wf_type e t ->
  kind x = TERM -> ~In x (fv_term a) -> ~In x (dom e) ->
  wf_term ((x, t) :: e) (freshen_term a x) ->
  wf_term e (Fun t a).
Proof.
  intros. apply wf_term_fun. auto. intros. 
  assert (kind x = kind x0). congruence.
  generalize (wf_term_swap x x0 H7 _ _ H3). 
  rewrite freshen_term_swap. simpl. rewrite swap_left. 
  rewrite (swap_type_not_free x x0 t); auto.
  rewrite (swap_term_not_free x x0 a); auto.
  intro. eapply wf_term_env_incr; eauto. simpl. 
  rewrite swap_env_dom; auto. 
  generalize (fv_wf_type x e t H); tauto.
  generalize (fv_wf_type x0 e t H); tauto. 
Qed.
 
Lemma wf_term_tfun':
  forall e x t a,
  wf_type e t ->
  kind x = TYPE -> ~In x (fv_term a) -> ~In x (dom e) ->
  wf_term ((x, t) :: e) (freshen_tety a x) ->
  wf_term e (TFun t a).
Proof.
  intros. apply wf_term_tfun. auto. intros. 
  assert (kind x = kind x0). congruence.
  generalize (wf_term_swap x x0 H7 _ _ H3). 
  rewrite freshen_tety_swap. simpl. rewrite swap_left. 
  rewrite (swap_type_not_free x x0 t); auto.
  rewrite (swap_term_not_free x x0 a); auto.
  intro. eapply wf_term_env_incr; eauto. simpl. 
  rewrite swap_env_dom; auto. 
  generalize (fv_wf_type x e t H); tauto.
  generalize (fv_wf_type x0 e t H); tauto. 
Qed.

(** ** Properties of term substitutions *)

(** To prove the usual properties of term substitutions, we follow the
  same approach as for type substitutions, starting with a
  characterization of terms that have no free de Bruijn variables, or
  all such variables below some threshold. *)

Fixpoint term_vars_below (a: term) (nterm ntype: nat) {struct a} : Prop :=
  match a with
  | Param x => True
  | Var n => n < nterm
  | Fun t b => type_vars_below t ntype /\ term_vars_below b (S nterm) ntype
  | App b c => term_vars_below b nterm ntype /\ term_vars_below c nterm ntype
  | TFun t b => type_vars_below t ntype /\ term_vars_below b nterm (S ntype)
  | TApp b t => term_vars_below b nterm ntype /\ type_vars_below t ntype
  end.

Lemma term_vars_below_vsubst_term:
  forall a nterm ntype a',
  term_vars_below (vsubst_term a nterm a') nterm ntype -> 
  term_vars_below a (S nterm) ntype.
Proof.
  induction a; simpl; intros; firstorder.
  destruct (compare_nat n nterm); simpl in H; omega. 
Qed.

Lemma term_vars_below_vsubst_tety:
  forall a nterm ntype a',
  term_vars_below (vsubst_tety a ntype a') nterm ntype -> 
  term_vars_below a nterm (S ntype).
Proof.
  generalize type_vars_below_vsubst; intro.
  induction a; simpl; intros; firstorder.
Qed.

Lemma wf_term_vars_below_0: forall e a, wf_term e a -> term_vars_below a 0 0.
Proof.
  generalize wf_type_vars_below_0; intro.
  induction 1; simpl; firstorder.
  destruct (fresh_name TERM (fv_term a ++ dom e)) as [x [F K]].
  apply term_vars_below_vsubst_term with (Param x). apply H2; eauto.
  destruct (fresh_name TYPE (fv_term a ++ dom e)) as [x [F K]].
  apply term_vars_below_vsubst_tety with (Tparam x). apply H2; eauto.
Qed.

Lemma vsubst_term_invariant_below:
  forall a n1 n2 m b, term_vars_below a n1 n2 -> n1 <= m -> vsubst_term a m b = a.
Proof.
  induction a; simpl; intros; try decEq; firstorder.
  destruct (compare_nat n m); auto; elimtype False; omega.
Qed.

Lemma vsubst_tety_invariant_below:
  forall a n1 n2 m t, term_vars_below a n1 n2 -> n2 <= m -> vsubst_tety a m t = a.
Proof.
  generalize vsubst_invariant_below; intro.
  induction a; simpl; intros; decEq; firstorder.
Qed.

Lemma vsubst_term_wf_term:
  forall e a n b, wf_term e a -> vsubst_term a n b = a.
Proof.
  intros. apply vsubst_term_invariant_below with 0 0. 
  eapply wf_term_vars_below_0; eauto. omega.
Qed.

Lemma vsubst_tety_wf_term:
  forall e a n t, wf_term e a -> vsubst_tety a n t = a.
Proof.
  intros. apply vsubst_tety_invariant_below with 0 0. 
  eapply wf_term_vars_below_0; eauto. omega.
Qed.

Lemma psubst_vsubst_term:
  forall e a x b n c,
  wf_term e b -> 
  vsubst_term (psubst_term a x b) n (psubst_term c x b) =
  psubst_term (vsubst_term a n c) x b.
Proof.
  induction a; intros; simpl; try decEq; auto.
  case (eq_name n x); intro; simpl. 
  eapply vsubst_term_wf_term; eauto. 
  auto.
  case (compare_nat n n0); auto.
Qed.

Lemma psubst_freshen_term:
  forall e a x b y,
  wf_term e b -> x <> y ->
  freshen_term (psubst_term a x b) y = psubst_term (freshen_term a y) x b.
Proof.
  intros. unfold freshen_term. 
  rewrite <- (psubst_vsubst_term e); auto.
  simpl. rewrite eq_name_false; auto.
Qed.

Lemma psubst_vsubst_tety:
  forall e a x b n c,
  wf_type e b -> 
  vsubst_tety (psubst_tety a x b) n (psubst_type c x b) =
  psubst_tety (vsubst_tety a n c) x b.
Proof.
  induction a; intros; simpl; try decEq; auto;
  eapply psubst_vsubst_type; eauto.
Qed.

Lemma psubst_freshen_tety:
  forall e a x b y,
  wf_type e b -> x <> y ->
  freshen_tety (psubst_tety a x b) y = psubst_tety (freshen_tety a y) x b.
Proof.
  intros. unfold freshen_tety. 
  rewrite <- (psubst_vsubst_tety e); auto.
  simpl. rewrite eq_name_false; auto.
Qed.

Lemma psubst_vsubst_tetety:
  forall e a x b n c,
  wf_type e b -> 
  vsubst_term (psubst_tety a x b) n (psubst_tety c x b) = 
  psubst_tety (vsubst_term a n c) x b.
Proof.
  induction a; intros; simpl; try decEq; auto.
  destruct (compare_nat n n0); auto. 
Qed.

Lemma psubst_freshen_tetety:
  forall e a x b y,
  wf_type e b -> x <> y ->
  freshen_term (psubst_tety a x b) y = psubst_tety (freshen_term a y) x b.
Proof.
  intros. unfold freshen_term. 
  rewrite <- (psubst_vsubst_tetety e); auto.
Qed.

Lemma psubst_vsubst_tetyte:
  forall e a x b n c,
  wf_term e b -> 
  vsubst_tety (psubst_term a x b) n c = psubst_term (vsubst_tety a n c) x b.
Proof.
  induction a; intros; simpl; try decEq; auto.
  destruct (eq_name n x); auto. eapply vsubst_tety_wf_term; eauto.
Qed.

Lemma psubst_freshen_tetyte:
  forall e a x b y,
  wf_term e b -> x <> y ->
  freshen_tety (psubst_term a x b) y = psubst_term (freshen_tety a y) x b.
Proof.
  intros; unfold freshen_tety. eapply psubst_vsubst_tetyte; eauto.
Qed.

Lemma vsubst_psubst_term:
  forall x a2 a1 n,
  ~In x (fv_term a1) ->
  vsubst_term a1 n a2 = psubst_term (vsubst_term a1 n (Param x)) x a2.
Proof.
  induction a1; simpl; intros.
  rewrite eq_name_false. auto. tauto.
  destruct (compare_nat n n0); auto. 
  simpl. rewrite eq_name_true; auto.
  decEq; auto.
  decEq; auto.
  decEq; auto.
  decEq; auto.
Qed.

Lemma vsubst_psubst_freshen_term:
  forall x a1 a2,
  ~In x (fv_term a1) ->
  vsubst_term a1 0 a2 = psubst_term (freshen_term a1 x) x a2.
Proof.
  intros; unfold freshen_term; eapply vsubst_psubst_term; eauto.
Qed.

Lemma vsubst_psubst_tety:
  forall x t2 a1 n,
  ~In x (fv_term a1) ->
  vsubst_tety a1 n t2 = psubst_tety (vsubst_tety a1 n (Tparam x)) x t2.
Proof.
  generalize vsubst_psubst_type; intro.
  induction a1; simpl; intros; decEq; auto.
Qed.

Lemma vsubst_psubst_freshen_tety:
  forall x a1 t2,
  ~In x (fv_term a1) ->
  vsubst_tety a1 0 t2 = psubst_tety (freshen_tety a1 x) x t2.
Proof.
  intros; unfold freshen_tety; apply vsubst_psubst_tety; auto.
Qed.

(** * Typing rules *)

(** We now define the typing judgement ``term [a] has type [t] in 
  environment [e]'' as an inductive predicate [has_type e a t]. *)

Inductive has_type: typenv -> term -> type -> Prop :=
  | t_var: forall e x t,
      wf_env e -> kind x = TERM -> lookup x e = Some t ->
      has_type e (Param x) t
  | t_abs: forall e t1 a t2,
      wf_type e t1 ->
      (forall x,
        kind x = TERM -> ~In x (dom e) ->
        has_type ((x, t1) :: e) (freshen_term a x) t2) ->
      has_type e (Fun t1 a) (Arrow t1 t2)
  | t_app: forall e a b t1 t2,
      has_type e a (Arrow t1 t2) -> has_type e b t1 ->
      has_type e (App a b) t2
  | t_tabs: forall e t1 a t2,
      wf_type e t1 ->
      (forall x,
        kind x = TYPE -> ~In x (dom e) ->
        has_type ((x, t1) :: e) (freshen_tety a x) (freshen_type t2 x)) ->
      has_type e (TFun t1 a) (Forall t1 t2)
  | t_tapp: forall e a t t1 t2,
      has_type e a (Forall t1 t2) ->
      is_subtype e t t1 ->
      has_type e (TApp a t) (vsubst_type t2 O t)
  | t_sub: forall e a t1 t2,
      has_type e a t1 -> is_subtype e t1 t2 ->
      has_type e a t2.

(** Well-formedness properties: if [has_type e a t] holds, then
  [e] is a well-formed environment, [t] a well-formed type
  and [a] a well-formed term. *)

Lemma has_type_wf_env: forall e a t, has_type e a t -> wf_env e.
Proof.
  induction 1; intros; eauto.
  destruct (fresh_name TERM (dom e)) as [x [FRESH KIND]].
  generalize (H1 x KIND FRESH); intros. inversion H2; auto.
  destruct (fresh_name TYPE (dom e)) as [x [FRESH KIND]].
  generalize (H1 x KIND FRESH); intros. inversion H2; auto.
Qed.

Lemma wf_type_strengthen:
  forall e t, wf_type e t ->
  forall e', (forall x, kind x = TYPE -> In x (dom e) -> In x (dom e')) -> wf_type e' t.
Proof.
  induction 1; intros.
  apply wf_type_param. auto. auto. 
  apply wf_type_top; auto.
  apply wf_type_arrow; auto.
  elim (fresh_name TYPE (fv_type t2 ++ dom e ++ dom e')).
  intros x [FRESH KIND].
  apply wf_type_forall' with x t1; auto. apply H1; auto.
  intros. simpl in *. elim H4; auto. 
Qed.

Lemma has_type_wf_type: forall e a t, has_type e a t -> wf_type e t.
Proof.
  induction 1; intros; eauto.
  (* var *)
  eapply wf_type_lookup; eauto.
  (* fun *)
  apply wf_type_arrow. auto. 
  elim (fresh_name TERM (dom e)); intros x [FRESH KIND].
  apply wf_type_strengthen with ((x, t1) :: e); auto. 
  simpl dom; intros. eapply in_cons_other; eauto. congruence.
  (* app *)
  inversion IHhas_type1; auto.
  (* tfun *)
  apply wf_type_forall. auto. auto. 
  (* tapp *)
  inversion IHhas_type; subst. 
  destruct (fresh_name TYPE (fv_type t2 ++ dom e)) as [x [F K]].
  rewrite (vsubst_psubst_freshen_type x); eauto.
  change e with (psubst_env nil x t ++ e). 
  eapply wf_type_psubst. simpl. apply H5; eauto. eauto.
Qed.

Lemma has_type_wf_term: forall e a t, has_type e a t -> wf_term e a.
Proof.
  induction 1; intros.
  (* var *)
  constructor. auto. eapply lookup_inv; eauto.
  (* fun *)
  constructor; auto.
  (* app *)
  constructor; auto.
  (* tfun *)
  constructor; auto. 
  (* tapp *)
  constructor; eauto. 
  (* subtype *)
  auto.
Qed.

Hint Resolve has_type_wf_env has_type_wf_type has_type_wf_term.

(** The [has_type] predicate is stable by addition of hypotheses. *)

Lemma wf_type_weaken: forall e e' t, wf_type e t -> env_weaken e e' -> wf_type e' t.
Proof.
  intros. apply wf_type_env_incr with e; auto. apply env_weaken_incl_dom; auto.
Qed.

Lemma wf_term_weaken: forall e e' a, wf_term e a -> env_weaken e e' -> wf_term e' a.
Proof.
  intros. apply wf_term_env_incr with e; auto. apply env_weaken_incl_dom; auto.
Qed.

Lemma env_weaken_add:
  forall e e' x t, env_weaken e e' -> env_weaken ((x, t) :: e) ((x, t) :: e').
Proof.
  intros; red; intros x' t'. simpl. 
  case (eq_name x' x); intro. auto. apply H. 
Qed.

Hint Resolve wf_type_weaken wf_term_weaken sub_weaken env_weaken_add.

Lemma has_type_weaken:
  forall e a t, has_type e a t -> forall e', wf_env e' -> env_weaken e e' -> has_type e' a t.
Proof.
  assert (X: forall e e' x, env_weaken e e' -> ~In x (dom e') -> ~In x (dom e)).
    intros. generalize (env_weaken_incl_dom _ _ H). unfold incl. firstorder.
  induction 1; simpl; intros.
  constructor; auto.
  constructor; eauto. intros. apply H1; eauto. constructor; eauto.
  econstructor; eauto.
  constructor; eauto. intros. apply H1; eauto. constructor; eauto.
  econstructor; eauto.
  econstructor; eauto.
Qed.

(** The [has_type] predicate is equivariant, i.e. stable by swapping. *)

Lemma has_type_swap:
  forall u v, kind u = kind v ->
  forall e a t, has_type e a t -> 
  has_type (swap_env u v e) (swap_term u v a) (swap_type u v t).
Proof.
  intros u v KINDuv. induction 1; simpl.
  (* var *)
  constructor. apply wf_env_swap; auto. rewrite swap_kind; auto. 
  apply lookup_swap; auto.
  (* fun *)
  constructor. apply wf_type_swap; auto. 
  intros. pose (x' := swap u v x).
  assert (kind x' = TERM).  unfold x'. rewrite swap_kind; auto.
  assert (~In x' (dom e)). 
    generalize (in_dom_swap u v x' e). unfold x'. rewrite swap_inv. tauto.
  generalize (H1 x' H4 H5). rewrite freshen_term_swap. simpl. 
  replace (swap u v x') with x. auto. unfold x'. rewrite swap_inv. auto.
  (* app *)
  simpl in IHhas_type1. econstructor; eauto. 
  (* tfun *)
  constructor. apply wf_type_swap; auto. 
  intros. pose (x' := swap u v x).
  assert (kind x' = TYPE).  unfold x'. rewrite swap_kind; auto.
  assert (~In x' (dom e)). 
    generalize (in_dom_swap u v x' e). unfold x'. rewrite swap_inv. tauto.
  generalize (H1 x' H4 H5). rewrite freshen_tety_swap. 
  rewrite freshen_type_swap. simpl. 
  replace (swap u v x') with x. auto. unfold x'. rewrite swap_inv. auto.
  (* tapp *)
  simpl in IHhas_type. rewrite vsubst_type_swap. 
  econstructor; eauto. apply is_subtype_swap; auto.
  (* sub *)
  econstructor; eauto. apply is_subtype_swap; auto.
Qed.

(** As a consequence of equivariance, we obtain admissible typing
  rules for functions and type abstractions, similar to rules [t_abs]
  and [t_tabs] but where the variable name is quantified existentially
  rather than universally. *)

Lemma kind_fv_type: forall e t, wf_type e t -> forall x, In x (fv_type t) -> kind x = TYPE.
Proof.
  induction 1; simpl; intros.
  replace x0 with x. auto. tauto. 
  tauto.
  elim (in_app_or _ _ _ H1); auto.
  elim (in_app_or _ _ _ H2); intros. auto.
    destruct (fresh_name TYPE (x :: fv_type t2 ++ dom e)) as [y [F K]].
    eapply H1; eauto. apply fv_type_freshen_type. auto. 
Qed.

Lemma fv_wf_type_kind: forall x e t, wf_type e t -> kind x = TERM -> ~In x (fv_type t).
Proof.
  intros; red; intros. generalize (kind_fv_type _ _ H _ H1). congruence.
Qed.

Lemma fresh_freshen_term:
  forall x t1 e a y,
  wf_term ((x, t1) :: e) (freshen_term a x) -> ~In y (dom e) -> x <> y ->
  ~In y (fv_term a).
Proof.
  intros. 
  red; intro.
  assert (In y (dom ((x, t1) :: e))).
    eapply fv_wf_term. eauto. apply fv_term_freshen_term. auto.
  elim H3; simpl; intros. contradiction. contradiction.
Qed.

Lemma t_abs': 
  forall e t1 a t2 x,
  kind x = TERM -> ~In x (dom e) -> ~In x (fv_term a) ->
  has_type ((x, t1) :: e) (freshen_term a x) t2 ->
  has_type e (Fun t1 a) (Arrow t1 t2).
Proof.
  intros. generalize (has_type_wf_env _ _ _ H2); intro. inversion H3; subst.
  generalize (has_type_wf_type _ _ _ H2); intro.
  generalize (has_type_wf_term _ _ _ H2); intro.
  apply t_abs. auto. intros y KIND DOM.
  case (eq_name x y); intro. subst x; auto.
  assert (kind x = kind y). congruence.
  assert (~In x (fv_type t1)). eapply fv_wf_type_kind; eauto.
  assert (~In x (fv_type t2)). eapply fv_wf_type_kind; eauto. 
  assert (~In y (fv_type t1)). eapply fv_wf_type_kind; eauto.
  assert (~In y (fv_type t2)). eapply fv_wf_type_kind; eauto.
  assert (~In y (fv_term a)).  eapply fresh_freshen_term; eauto.
  generalize (has_type_swap x y H6 _ _ _ H2). 
  rewrite freshen_term_swap. simpl. rewrite swap_left.
  rewrite (swap_type_not_free x y t1); auto.
  rewrite (swap_type_not_free x y t2); auto.
  rewrite (swap_term_not_free x y a); auto.
  rewrite (swap_env_not_free x y e); auto.
Qed.

Lemma fresh_freshen_tety:
  forall x t1 e a y,
  wf_term ((x, t1) :: e) (freshen_tety a x) -> ~In y (dom e) -> x <> y ->
  ~In y (fv_term a).
Proof.
  intros. 
  red; intro.
  assert (In y (dom ((x, t1) :: e))).
    eapply fv_wf_term. eauto. apply fv_term_freshen_tety. auto.
  elim H3; simpl; intros. contradiction. contradiction.
Qed.

Lemma t_tabs': 
  forall e t1 a t2 x,
  kind x = TYPE -> ~In x (dom e) -> ~In x (fv_term a) -> ~In x (fv_type t2) ->
  has_type ((x, t1) :: e) (freshen_tety a x) (freshen_type t2 x) ->
  has_type e (TFun t1 a) (Forall t1 t2).
Proof.
  intros. generalize (has_type_wf_env _ _ _ H3); intro. inversion H4; subst.
  generalize (has_type_wf_type _ _ _ H3); intro.
  generalize (has_type_wf_term _ _ _ H3); intro.
  apply t_tabs. auto. intros y KIND DOM.
  case (eq_name x y); intro. subst x; auto.
  assert (kind x = kind y). congruence.
  assert (~In x (fv_type t1)). generalize (fv_wf_type x _ _ H10); tauto. 
  assert (~In y (fv_type t1)). generalize (fv_wf_type y _ _ H10); tauto.
  assert (~In y (fv_type t2)). eapply fresh_freshen_type; eauto.
  assert (~In y (fv_term a)).  eapply fresh_freshen_tety; eauto.
  generalize (has_type_swap x y H7 _ _ _ H3). 
  rewrite freshen_type_swap. rewrite freshen_tety_swap. 
  simpl. rewrite swap_left.
  rewrite (swap_type_not_free x y t1); auto.
  rewrite (swap_type_not_free x y t2); auto.
  rewrite (swap_term_not_free x y a); auto.
  rewrite (swap_env_not_free x y e); auto.
Qed.

(** * Stability of the typing judgement under substitutions *)

(** We now show that the typing judgement is stable under
  substitutions.  There are two substitutions to consider: of a type
  for a type variable, and of a term for a term variable. *)

Lemma has_type_stable_type_subst:
  forall e1 x p q e2 a t,
  kind x = TYPE ->
  is_subtype e1 p q ->
  has_type (e2 ++ (x, q) :: e1) a t ->
  has_type (psubst_env e2 x p ++ e1) (psubst_tety a x p) (psubst_type t x p).
Proof.
  assert (forall e1 x p q, kind x = TYPE -> is_subtype e1 p q ->
          forall e a t, has_type e a t ->
          forall e2, e = e2 ++ (x, q) :: e1 ->
          has_type (psubst_env e2 x p ++ e1) (psubst_tety a x p) (psubst_type t x p)).
  induction 3; intros; simpl; subst e.
  (* var *)
  elim (lookup_env_concat _ _ _ p _ _ _ H1 H3); intros [A B].
  congruence.
  constructor; auto.
  eapply wf_env_psubst; eauto.
  (* fun *)
  destruct (fresh_name TERM (x :: dom (e2 ++ (x, q) :: e1) ++
                             dom (psubst_env e2 x p ++ e1) ++
                             fv_type (psubst_type t2 x p) ++
                             fv_term (psubst_tety a x p)))
  as [y [F K]].
  apply t_abs' with y; eauto. 
  change ((y, psubst_type t1 x p) :: psubst_env e2 x p ++ e1)
    with (psubst_env ((y, t1) :: e2) x p ++ e1).
  rewrite (psubst_freshen_tetety e1). apply H3; eauto. 
  eauto. eauto.
  (* app *)
  simpl in IHhas_type1. econstructor; eauto.
  (* tfun *)  
  destruct (fresh_name TYPE (x :: dom (e2 ++ (x, q) :: e1) ++
                             dom (psubst_env e2 x p ++ e1) ++
                             fv_type (psubst_type t2 x p) ++
                             fv_term (psubst_tety a x p)))
  as [y [F K]].
  apply t_tabs' with y; eauto. 
  change ((y, psubst_type t1 x p) :: psubst_env e2 x p ++ e1)
    with (psubst_env ((y, t1) :: e2) x p ++ e1).
  rewrite (psubst_freshen_tety e1). 
  rewrite (psubst_freshen_type e1).
  apply H3; eauto. eauto. eauto. eauto. eauto.
  (* tapp *)
  rewrite <- (psubst_vsubst_type e1). simpl in IHhas_type.
  econstructor; eauto.
  eapply sub_stable_subst; eauto. eauto.
  (* sub *)
  econstructor; eauto. eapply sub_stable_subst; eauto.

  eauto.
Qed.

Lemma lookup_env_append:
  forall e2 x p y e1,
  wf_env (e1 ++ (x, p) :: e2) -> 
  lookup y (e1 ++ (x, p) :: e2) = if eq_name y x then Some p else lookup y (e1 ++ e2).
Proof.
  induction e1; simpl; intros.
  auto.
  destruct a. inversion H; subst.
  case (eq_name y n); intro. 
  rewrite eq_name_false. auto. subst n. 
  rewrite dom_append in H4. simpl in H4. eauto. 
  auto.
Qed.

Lemma wf_env_append:
  forall e2 x p e1, wf_env (e1 ++ (x, p) :: e2) -> kind x = TERM -> wf_env (e1 ++ e2).
Proof.
  induction e1; simpl; intros.
  inversion H; auto.
  inversion H; subst. 
  constructor. auto.
  rewrite dom_append. rewrite dom_append in H4. simpl in H4.
  red; intro. elim H4. apply in_or_app. simpl. elim (in_app_or _ _ _ H1); auto.
  apply wf_type_strengthen with (e1 ++ (x, p) :: e2). auto.
  intros. rewrite dom_append in H2. simpl in H2. rewrite dom_append.
  apply in_or_app. elim (in_app_or _ _ _ H2); intro. auto. 
  elim H6; intro. congruence. auto.
Qed.

Lemma is_subtype_strengthen:
  forall e s t, is_subtype e s t ->
  forall e', wf_env e' -> (forall x : name, kind x = TYPE -> lookup x e' = lookup x e) ->
  is_subtype e' s t.
Proof.
  assert (forall e e',
           (forall x : name, kind x = TYPE -> lookup x e' = lookup x e) ->
           (forall x : name, kind x = TYPE -> In x (dom e) -> In x (dom e'))).
    intros. destruct (lookup_exists _ _ H1) as [t L]. 
    apply lookup_inv with t. rewrite H; auto.
  induction 1; intros.
  (* top *)
  constructor; auto. apply wf_type_strengthen with e; eauto.
  (* refl *)
  econstructor; eauto. rewrite H4; eauto.
  (* trans *)
  econstructor; eauto. rewrite H4; auto.
  (* arrow *)
  constructor; auto.
  (* forall *)
  destruct (fresh_name TYPE (dom e ++ dom e' ++ fv_type s2 ++ fv_type t2)) as [x [F K]].
  apply sa_all' with x; eauto. 
  apply H2; eauto. constructor; eauto. 
  intros x0 K0. simpl. case (eq_name x0 x); auto.
Qed.

Lemma has_type_stable_term_subst:
  forall e1 x b s e2 a t,
  kind x = TERM -> has_type e1 b s -> has_type (e2 ++ (x, s) :: e1) a t ->
  has_type (e2 ++ e1) (psubst_term a x b) t.
Proof.
  assert (forall e1 x b s, kind x = TERM -> has_type e1 b s ->
          forall e a t, has_type e a t ->
          forall e2, e = e2 ++ (x, s) :: e1 ->
          has_type (e2 ++ e1) (psubst_term a x b) t).
  induction 3; intros; simpl; subst e.
  (* var *)
  rewrite lookup_env_append in H3; auto. 
  assert (wf_env (e2 ++ e1)). eapply wf_env_append; eauto.
  destruct (eq_name x0 x). 
  replace t with s. eapply has_type_weaken; eauto.
  apply env_concat_weaken; auto. congruence.
  constructor; auto.
  (* fun *)
  destruct (fresh_name TERM (x :: dom (e2 ++ (x, s) :: e1) ++
                             dom (e2 ++ e1) ++
                             fv_type t1 ++
                             fv_term (psubst_term a x b)))
  as [y [F K]].
  apply t_abs' with y; eauto. 
  change ((y, t1) :: e2 ++ e1)
    with (((y, t1) :: e2) ++ e1).
  rewrite (psubst_freshen_term e1). apply H3; eauto. eauto. eauto. 
  (* app *)
  simpl in IHhas_type1. econstructor; eauto.
  (* tfun *)  
  destruct (fresh_name TYPE (x :: dom (e2 ++ (x, s) :: e1) ++
                             dom (e2 ++ e1) ++
                             fv_type t2 ++
                             fv_term (psubst_term a x b)))
  as [y [F K]].
  apply t_tabs' with y; eauto. 
  change ((y, t1) :: e2 ++ e1)
    with (((y, t1) :: e2) ++ e1).
  rewrite (psubst_freshen_tetyte e1). 
  apply H3; eauto. eauto. eauto.
  (* tapp *)
  simpl in IHhas_type.
  econstructor; eauto.
  eapply is_subtype_strengthen. eauto. 
  eapply wf_env_append; eauto. 
  intros. rewrite lookup_env_append. rewrite eq_name_false. auto.
  congruence.
  eauto.
  (* sub *)
  econstructor; eauto. 
  eapply is_subtype_strengthen. eauto. 
  eapply wf_env_append; eauto.
  intros. rewrite lookup_env_append. rewrite eq_name_false. auto.
  congruence. eauto.

  eauto.
Qed.

(** * Dynamic semantics *)

(** The dynamic semantics of $F_{<:}$ is specified by a one-step reduction relation,
  in small-step operational style.  We first define values (final results of reduction
  sequences) as a subset of terms. *)

Inductive isvalue: term -> Prop :=
  | isvalue_fun: forall t a,
      isvalue (Fun t a)
  | isvalue_tfun: forall t a,
      isvalue (TFun t a).

(** We first give a Plotkin-style specification of the reduction
  relation: it uses inductive rules [red_appfun], [red_apparg],
  [red_tapp] instead of contexts to describe reductions inside
  applications.  The two rules [red_appabs] and [red_tapptabs] are the
  familiar beta-reduction rules for term and type applications,
  respectively. *)

Inductive red: term -> term -> Prop :=
  | red_appabs: forall t a v,
      isvalue v ->
      red (App (Fun t a) v) (vsubst_term a 0 v)
  | red_tapptabs: forall t a t',
      red (TApp (TFun t a) t') (vsubst_tety a 0 t')
  | red_appfun: forall a a' b,
      red a a' -> red (App a b) (App a' b)
  | red_apparg: forall v b b',
      isvalue v -> red b b' -> red (App v b) (App v b')
  | red_tapp: forall a a' t,
      red a a' -> red (TApp a t) (TApp a' t).

(** We now give an alternate specification of the reduction relation
  in the style of Wright and Felleisen.  The [red_top] relation
  captures beta-reductions at the top of a term.  Reductions within
  terms are expressed using reduction contexts (see the [red_context]
  relation).  Contexts are represented as functions from terms to
  terms whose shape is constrained by the [is_context] predicate. *)

Inductive red_top: term -> term -> Prop :=
  | red_top_appabs: forall t a v,
      isvalue v ->
      red_top (App (Fun t a) v) (vsubst_term a 0 v)
  | red_top_tapptabs: forall t a t',
      red_top (TApp (TFun t a) t') (vsubst_tety a 0 t').

Inductive is_context: (term -> term) -> Prop :=
  | iscontext_hole:
      is_context (fun a => a)
  | iscontext_app_left: forall c b,
      is_context c -> is_context (fun x => App (c x) b)
  | iscontext_app_right: forall v c,
      isvalue v -> is_context c -> is_context (fun x => App v (c x))
  | iscontext_tapp: forall c t,
      is_context c -> is_context (fun x => TApp (c x) t).

Inductive red_context: term -> term -> Prop :=
  | red_context_intro: forall a a' c,
      red_top a a' -> is_context c -> red_context (c a) (c a').

(** The Plotkin-style relation is more convenient for doing formal
  proofs.  Since the challenge is given in terms of contexts,
  we feel obliged to prove the equivalence between the two formulations
  of reduction.  The proofs are routine inductions over
  the derivations of [red] and [is_context], respectively. *)

Lemma red_red_context: forall a a', red a a' -> red_context a a'.
Proof.
  induction 1; intros.
  change (App (Fun t a) v) with ((fun x => x) (App (Fun t a) v)).
  change (vsubst_term a 0 v) with ((fun x => x) (vsubst_term a 0 v)).
  constructor. constructor. auto. constructor.
  change (TApp (TFun t a) t') with ((fun x => x) (TApp (TFun t a) t')).
  change (vsubst_tety a 0 t') with ((fun x => x) (vsubst_tety a 0 t')).
  constructor. constructor. constructor.
  inversion IHred; subst. 
  change (App (c a0) b) with ((fun x => App (c x) b) a0).
  change (App (c a'0) b) with ((fun x => App (c x) b) a'0).
  constructor. auto. constructor. auto.
  inversion IHred; subst. 
  change (App v (c a)) with ((fun x => App v (c x)) a).
  change (App v (c a')) with ((fun x => App v (c x)) a').
  constructor. auto. constructor. auto. auto.
  inversion IHred; subst. 
  change (TApp (c a0) t) with ((fun x => TApp (c x) t) a0).
  change (TApp (c a'0) t) with ((fun x => TApp (c x) t) a'0).
  constructor. auto. constructor. auto. 
Qed.

Lemma red_context_red: forall a a', red_context a a' -> red a a'.
Proof.
  assert (forall c, is_context c ->
          forall a a', red_top a a' -> red (c a) (c a')).
  induction 1; intros.
  inversion H; constructor; auto.
  apply red_appfun; auto.
  apply red_apparg; auto.
  apply red_tapp; auto.

  intros. inversion H0. auto.
Qed.

(** * Type soundness proof *)

(** Type soundness for $F_{<:}$ is established by proving the standard properties of
  type preservation (also called subject reduction) and progress. *)

(** ** Preservation *)

(** Technical inversion lemmas on typing derivations. These lemmas are 
  similar (but not fully identical) to lemma A.13 in the on-paper proof. *)

Lemma has_type_fun_inv:
  forall e a t, has_type e a t ->
  forall b s1 u1 u2, a = Fun s1 b -> is_subtype e t (Arrow u1 u2) ->
  is_subtype e u1 s1 /\ 
  exists s2, 
    is_subtype e s2 u2 /\
    (forall x, kind x = TERM -> ~In x (dom e) -> has_type ((x, s1) :: e) (freshen_term b x) s2).
Proof.
  induction 1; intros; try discriminate. 
  injection H2; intros; clear H2; subst s1; subst b.
  inversion H3; subst. split. auto. 
  exists t2; split; assumption.
  eapply IHhas_type; eauto. eapply sub_trans; eauto.
Qed.

Lemma has_type_tfun_inv:
  forall e a t, has_type e a t ->
  forall b s1 u1 u2, a = TFun s1 b -> is_subtype e t (Forall u1 u2) ->
  is_subtype e u1 s1 /\ 
  exists s2, 
    (forall x, kind x = TYPE -> ~In x (dom e) ->
        is_subtype ((x, u1) :: e) (freshen_type s2 x) (freshen_type u2 x)) /\
    (forall x, kind x = TYPE -> ~In x (dom e) ->
        has_type ((x, s1) :: e) (freshen_tety b x) (freshen_type s2 x)).
Proof.
  induction 1; intros; try discriminate. 
  injection H2; intros; clear H2; subst s1 b.
  inversion H3; subst. split. auto. 
  exists t2; split. assumption. assumption.
  eapply IHhas_type; eauto. eapply sub_trans; eauto.
Qed.


(** The preservation theorem states that if term [a] reduces to [a'], then
  all typings valid for [a] are also valid for [a'].  It is
  proved by an outer induction on the reduction and an inner induction
  on the typing derivation (to get rid of subtyping steps). *)

Theorem preservation: forall e a a' t, red a a' -> has_type e a t -> has_type e a' t.
Proof. 
  assert (forall a a', red a a' ->
          forall e a0 t, has_type e a0 t -> forall (EQ: a = a0), 
          has_type e a' t).
  induction 1; induction 1; intros; simplify_eq EQ; clear EQ; intros; subst;
  try (eapply t_sub; eauto; fail).
  (** Case app abs *)
  assert (is_subtype e (Arrow t1 t2) (Arrow t1 t2)). apply sub_refl; eauto.
  destruct (has_type_fun_inv _ _ _ H0_ _ _ _ _ (refl_equal _) H0)
  as [A [s2 [B C]]].
  apply t_sub with s2; auto.
  destruct (fresh_name TERM (dom e ++ fv_term a)) as [x [F K]].
  rewrite (vsubst_psubst_freshen_term x); eauto.
  change e with (nil ++ e). 
  apply has_type_stable_term_subst with t; auto.
  apply t_sub with t1; auto.
  simpl; eauto.
  (** Case tapp tabs *)
  assert (is_subtype e (Forall t1 t2) (Forall t1 t2)). apply sub_refl; eauto.
  destruct (has_type_tfun_inv _ _ _ H _ _ _ _ (refl_equal _) H1)
  as [A [s2 [B C]]].
  destruct (fresh_name TYPE (dom e ++ fv_term a ++ fv_type t2)) as [x [F K]].
  rewrite (vsubst_psubst_freshen_tety x); eauto. 
  rewrite (vsubst_psubst_freshen_type x); eauto. 
  apply t_sub with (psubst_type (freshen_type s2 x) x t0).
  change e with (psubst_env nil x t0 ++ e).
  apply has_type_stable_type_subst with t; eauto. 
  apply sub_trans with t1; auto.
  simpl; auto. 
  change e with (psubst_env nil x t0 ++ e).
  apply sub_stable_subst with t1; eauto. simpl; auto.
  (** Case context left app *)
  apply t_app with t1; eauto.
  (** Case context right app *)
  apply t_app with t1; eauto.
  (** Case context left tapp *)
  apply t_tapp with t1; eauto. 
  (** Final conclusion *)
  eauto.
Qed.

(** ** Progress *)

(** The following lemma, which corresponds to lemma A.14 in the challenge statement,
  determines the shape of a value from its type.  Namely, closed values of function
  types are function abstractions, and closed values of polymorphic types are 
  type abstractions. *)

Lemma canonical_forms:
  forall e a t, has_type e a t -> e = nil -> isvalue a ->
  match t with 
  | Arrow t1 t2 => exists s, exists b, a = Fun s b
  | Forall t1 t2 => exists s, exists b, a = TFun s b
  | Top => True
  | _ => False
  end.
Proof.
  induction 1; intros; subst e.
  inversion H3.
  exists t1; exists a; auto.
  inversion H2.
  exists t1; exists a; auto.
  inversion H2.
  generalize (IHhas_type (refl_equal _) H2). 
  inversion H0; auto.
  simpl in H3; discriminate.
Qed.

(** The progress theorem shows that a term well-typed in the empty environment
  is never ``stuck'': either it is a value, or it can reduce.
  The theorem is proved by a simple induction on the typing derivation for the term
  and a case analysis on whether the subterms of the term are values
  or can reduce further. *)

Theorem progress: forall a t, has_type nil a t -> isvalue a \/ exists a', red a a'.
Proof. 
  assert (forall e a t, has_type e a t -> e = nil -> isvalue a \/ exists a', red a a').
  induction 1; intros; subst e.
  (** Free variable: impossible in the empty typing environment. *)
  simpl in H1. discriminate.
  (** Function: already a value. *)
  left; constructor.
  (** Application [App a b]. *)
  right.
  destruct (IHhas_type1 (refl_equal _)) as [Va | [a' Ra]].
  destruct (IHhas_type2 (refl_equal _)) as [Vb | [b' Rb]].
    (** [a] and [b] are values.  [a] must be a [Fun].  
        Beta-reduction is possible. *)
    generalize (canonical_forms _ _ _ H (refl_equal _) Va).
    intros [s [c EQ]]. subst a. 
    exists (vsubst_term c 0 b). constructor. auto.
    (** [a] is a value, but [b] reduces. [App a b] therefore reduces. *)
    exists (App a b'). constructor; auto.
    (** [a] reduces. [App a b] reduces as well. *)
    exists (App a' b). constructor; auto.
  (** Type abstraction: already a value. *)
  left; constructor.
  (** Type application [TApp a t]. *)
  right. destruct (IHhas_type (refl_equal _)) as [Va | [a' Ra]].
    (** [a] is a value. [a] must be a [TFun].  Beta-reduction is possible. *)
    generalize (canonical_forms _ _ _ H (refl_equal _) Va).
    intros [s [b EQ]]. subst a. 
    exists (vsubst_tety b 0 t). constructor. 
    (** [a] reduces, and so does [TApp a t]. *)
    exists (TApp a' t). constructor; auto.
  (** Subtyping step. *)
  auto.
  (** Final conclusion. *)
  eauto.
Qed.


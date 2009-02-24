(** This chapter corresponds to part 1A of the POPLmark challenge,
  namely the formal definition of a subtyping relation between types
  of $F_{<:}$ and the proof of basic type-theoretic properties of
  this relation.

  We start by ``importing'' three modules from the Coq library of standard
  definitions and theorems: [Arith] (arithmetic over natural numbers),
  [ZArith] (arithmetic over integers) and [List] (operations over finite
  lists).  We also import a module [extralibrary] that we developed
  specially, which provides additional lemmas about list membership.
  This module is omitted in this report, but available as part of the
  Web version of this development %\cite{Leroy-POPLmark-Coq}%. *)

Require Import Arith.
Require Import ZArith.
Require Import List.
Require Import extralibrary.

(** * Names and swaps of names *)

(** We use names (also called atoms) to represent free variables
  in terms.  Any infinite type with decidable equality will do.
  In preparation for the second part of the challenge, we
  attach a kind to every name: either ``type'' or ``term'',
  and ensure that there are infinitely many names of each
  kind.  Concretely, we represent names by pairs of
  a kind and an integer (type Z). *)

Inductive name_kind : Set :=
  | TYPE: name_kind
  | TERM: name_kind.

Definition name : Set := (name_kind * Z)%type.

Definition kind (n: name) : name_kind := fst n.

(** Equality between names is decidable. *)

Lemma eq_name: forall (n1 n2: name), {n1 = n2} + {n1 <> n2}.
Proof.
  assert (forall k1 k2: name_kind, {k1 = k2} + {k1 <> k2}).
  decide equality.
  assert (forall p1 p2: positive, {p1 = p2} + {p1 <> p2}).
  decide equality.
  assert (forall z1 z2: Z, {z1 = z2} + {z1 <> z2}).
  decide equality.
  decide equality.
Defined.

(** Moreover, we have the following obvious simplification rules on
  tests over name equality. *)

Lemma eq_name_true:
  forall (A: Set) (n: name) (a b: A), (if eq_name n n then a else b) = a.
Proof.
  intros. case (eq_name n n); congruence.
Qed.

Lemma eq_name_false:
  forall (A: Set) (n m: name) (a b: A), n <> m -> (if eq_name n m then a else b) = b.
Proof.
  intros. case (eq_name n m); congruence.
Qed.

(** The following lemma shows that there always exists a name
  of the given kind that is fresh w.r.t. the given list of names, that is,
  distinct from all the names in this list. *)

Definition find_fresh_name (k: name_kind) (l: list name) : name :=
  (k, 1 + fold_right (fun (n:name) x => Zmax (snd n) x) 0 l)%Z.

Lemma find_fresh_name_is_fresh:
  forall k l, let n := find_fresh_name k l in ~In n l /\ kind n = k.
Proof.
  intros.
  set (ident := fun (n: name) => snd n). 
  set (maxid := 
   fold_right (fun (n:name) x => Zmax (ident n) x) 0%Z).
  assert (forall x, In x l -> (ident x <= maxid l)%Z).
    generalize l. induction l0; simpl; intros.
    elim H.
    elim H; intros. subst x. apply Zmax1. 
    apply Zle_trans with (maxid l0). auto. apply Zmax2.
  replace n with (k, 1 + maxid l)%Z. 
  split. red; intro. generalize (H _ H0). unfold ident, snd. omega.
  reflexivity.
  unfold n; reflexivity.
Qed.

Lemma fresh_name:
  forall (k: name_kind) (l: list name), exists n, ~In n l /\ kind n = k.
Proof.
  intros. exists (find_fresh_name k l). apply find_fresh_name_is_fresh.
Qed.

(** As argued by Pitts and others, swaps (permutations of two
  names) are an interesting special case of renamings.
  We will use swaps later to prove that our definitions
  are equivariant, that is, insensitive to the choices of fresh identifiers. *)

Definition swap (u v x: name) : name :=
  if eq_name x u then v else if eq_name x v then u else x.

(** The following lemmas are standard properties of swaps:
  self-inverse, injective, kind-preserving. *)

Lemma swap_left: forall x y, swap x y x = y.
Proof. intros. unfold swap. apply eq_name_true. Qed.

Lemma swap_right: forall x y, swap x y y = x.
Proof.
  intros. unfold swap. case (eq_name y x); intro. auto.
  apply eq_name_true. 
Qed.

Lemma swap_other: forall x y z, z <> x -> z <> y -> swap x y z = z.
Proof. intros. unfold swap. repeat rewrite eq_name_false; auto. Qed.

Lemma swap_inv: forall u v x, swap u v (swap u v x) = x.
Proof.
  intros; unfold swap.
  case (eq_name x u); intro. 
    case (eq_name v u); intro. congruence. rewrite eq_name_true. congruence.
  case (eq_name x v); intro.
    rewrite eq_name_true. congruence.
  repeat rewrite eq_name_false; auto.
Qed.

Lemma swap_inj: forall u v x y, swap u v x = swap u v y -> x = y.
Proof.
  intros. rewrite <- (swap_inv u v x). rewrite <- (swap_inv u v y).
  congruence.
Qed.

Lemma swap_kind: forall u v x, kind u = kind v -> kind (swap u v x) = kind x.
Proof.
  intros. unfold swap. case (eq_name x u); intro.
  congruence. case (eq_name x v); intro.
  congruence. auto.
Qed.

(** * Types and typing environments *)

(** ** Type expressions *)

(** The syntax of type expressions is standard, except that we have two
  representations for variables: [Tparam] represents free type variables,
  identified by a name, while [Tvar] represents bound type
  variables, identified by their de Bruijn indices. 
  Our de Bruijn indices start at 0.
  In a [Forall t1 t2] type, the variable [Tvar 0] is bound
  by the [Forall] in type [t2].
*)

Inductive type: Set :=
  | Tparam: name -> type
  | Tvar: nat -> type
  | Top: type
  | Arrow: type -> type -> type
  | Forall: type -> type -> type.

(** The free names of a type are defined as follow.  Notice the
  [Forall] case: [Forall] does not bind any name. *)

Fixpoint fv_type (t: type) : list name :=
  match t with
  | Tparam x => x :: nil
  | Tvar n => nil
  | Top => nil
  | Arrow t1 t2 => fv_type t1 ++ fv_type t2
  | Forall t1 t2 => fv_type t1 ++ fv_type t2
  end.

(** There are two substitution operations over types, written
  [vsubst] and [psubst] in Pollack's talk.  
  [vsubst] substitutes a type for a bound variable (a de Bruijn index).
  [psubst] substitutes a type for a free variable (a name).

  The crucial observation is that variable capture cannot occur
  during either substitution:
  - Types never contain free de Bruijn indices, since these
    indices are used only for representing bound variables.
    Therefore, [vsubst] does not need to
    perform lifting of de Bruijn indices in the substituted type.
  - Types never bind names, only de Bruijn indices.
    Therefore, [psubst] never needs to perform renaming of
    names in the substituted term when descending below a
    binder.
*)

Fixpoint vsubst_type (a: type) (x: nat) (b: type) {struct a} : type :=
  match a with
  | Tparam n => Tparam n
  | Tvar n =>
      match compare_nat n x with
      | Nat_less _ => Tvar n
      | Nat_equal _ => b
      | Nat_greater _ => Tvar (pred n)
      end
  | Top => Top
  | Arrow a1 a2 => Arrow (vsubst_type a1 x b) (vsubst_type a2 x b)
  | Forall a1 a2 => Forall (vsubst_type a1 x b) (vsubst_type a2 (S x) b)
  end.

Fixpoint psubst_type (a: type) (x: name) (b: type) {struct a} : type :=
  match a with
  | Tparam n => if eq_name n x then b else Tparam n
  | Tvar n => Tvar n
  | Top => Top
  | Arrow a1 a2 => Arrow (psubst_type a1 x b) (psubst_type a2 x b)
  | Forall a1 a2 => Forall (psubst_type a1 x b) (psubst_type a2 x b)
  end.

(** In the remainder of the development, [vsubst] is only used
  to replace bound variable 0 by a fresh, free variable (a name)
  when taking apart a [Forall] type.
  This operation is similar to the ``freshening'' operation
  used in Fresh ML and related systems.  We call it [freshen_type] for
  clarity. *)

Definition freshen_type (a: type) (x: name) : type := vsubst_type a 0 (Tparam x).

(** Free variables and freshening play well together. *)

Lemma fv_type_vsubst_type:
  forall x a n b, In x (fv_type a) -> In x (fv_type (vsubst_type a n b)).
Proof.
  induction a; simpl; intros. 
  auto. contradiction. contradiction.
  elim (in_app_or _ _ _ H); auto.
  elim (in_app_or _ _ _ H); auto.
Qed.

Lemma fv_type_freshen_type:
  forall x a y, In x (fv_type a) -> In x (fv_type (freshen_type a y)).
Proof.
  intros; unfold freshen_type; apply fv_type_vsubst_type; auto.
Qed.

(** We now define swaps (permutation of names) over types
  and show basic properties of swaps that will be useful later. *)

Fixpoint swap_type (u v: name) (t: type) {struct t} : type :=
  match t with
  | Tparam x => Tparam (swap u v x)
  | Tvar n => Tvar n
  | Top => Top
  | Arrow t1 t2 => Arrow (swap_type u v t1) (swap_type u v t2)
  | Forall t1 t2 => Forall (swap_type u v t1) (swap_type u v t2)
  end.

(** Swaps are involutions (self-inverse). *)

Lemma swap_type_inv: forall u v t, swap_type u v (swap_type u v t) = t.
Proof.
  induction t; simpl; try congruence.
  rewrite swap_inv. auto.
Qed.

(** Swaps of variables that do not occur free in a type
  leave the type unchanged. *)

Lemma swap_type_not_free:
  forall u v t, ~In u (fv_type t) -> ~In v (fv_type t) -> swap_type u v t = t.
Proof.
  induction t; simpl; intros; try (auto; decEq; eauto).
  unfold swap. repeat rewrite eq_name_false. auto. tauto. tauto.
Qed.

(** Swaps commute with [vsubst] substitution and freshening. *)

Lemma vsubst_type_swap:
  forall u v a n b,
  swap_type u v (vsubst_type a n b) = vsubst_type (swap_type u v a) n (swap_type u v b).
Proof.
  induction a; simpl; intros; auto; try (decEq; auto).
  case (compare_nat n n0); auto.
Qed.

Lemma freshen_type_swap:
  forall u v a x,
  swap_type u v (freshen_type a x) = freshen_type (swap_type u v a) (swap u v x).
Proof.
  intros; unfold freshen_type. 
  change (Tparam (swap u v x)) with (swap_type u v (Tparam x)).
  apply vsubst_type_swap. 
Qed.

(** Swaps commute with the computation of free variables. *)

Lemma in_fv_type_swap:
  forall u v x t, In x (fv_type t) <-> In (swap u v x) (fv_type (swap_type u v t)).
Proof.
  induction t; simpl.
  intuition. subst n. tauto.
  left. eapply swap_inj; eauto.
  tauto. tauto. 
  auto. auto.
Qed.

(** ** Typing environments *)

(** Typing environments are standard: lists of (name, type) pairs.
  Bindings are added to the left of the environment using the
  [cons] list operation.  Thus, later bindings come first. *)

Definition typenv := list (name * type).

Definition dom (e: typenv) := map (@fst name type) e.

Lemma dom_append: forall e1 e2, dom (e1 ++ e2) = dom e1 ++ dom e2.
Proof.
  intros; unfold dom. apply map_append. 
Qed.

(** The [lookup] function returns the type associated with a name in a typing environment. *)

Fixpoint lookup (x: name) (e: typenv) {struct e} : option type :=
  match e with
  | nil => None
  | (y, t) :: e' => if eq_name x y then Some t else lookup x e'
  end.

Lemma lookup_inv: forall x t e, lookup x e = Some t -> In x (dom e).
Proof.
  induction e; simpl. congruence.
  case a; intros x' t'. simpl. 
  case (eq_name x x'); intro. subst x'; tauto.
  intros. right. auto.
Qed.

Lemma lookup_exists: forall x e, In x (dom e) -> exists t, lookup x e = Some t.
Proof.
  induction e; simpl; intros.
  elim H.
  destruct a. simpl in H. 
  case (eq_name x n); intro.
  exists t; auto.
  apply IHe. elim H; intro. congruence. auto.
Qed.

(** We extend swaps to typing environments, pointwise. *)

Fixpoint swap_env (u v: name) (e: typenv) {struct e} : typenv :=
  match e with
  | nil => nil
  | (x, t) :: e' => (swap u v x, swap_type u v t) :: swap_env u v e'
  end.

(** Environment lookup commutes with swaps. *)

Lemma lookup_swap:
  forall u v x e t, lookup x e = Some t ->
  lookup (swap u v x) (swap_env u v e) = Some (swap_type u v t).
Proof.
  induction e; simpl.
  intros. congruence.
  case a; intros y t t'. simpl. 
  case (eq_name x y); intros. 
  subst y. rewrite eq_name_true. congruence.
  rewrite eq_name_false. auto. 
  generalize (swap_inj u v x y). tauto.
Qed.

(** The [dom] operation commutes with swaps. *)

Lemma in_dom_swap:
  forall u v x e, In x (dom e) <-> In (swap u v x) (dom (swap_env u v e)).
Proof.
  induction e; simpl.
  tauto.
  case a; intros y t. simpl. intuition. 
  subst x. intuition. 
  left. eapply swap_inj; eauto.
Qed.

(** ** Well-formedness of types and environments *)

(** A type is well-formed in a typing environment if:
  - all names free in the type are of kind [TYPE];
  - all names free in the type are bound in the environment;
  - it does not contain free de Bruijn variables.

We capture these conditions by the following inference rules. *)

Inductive wf_type: typenv -> type -> Prop :=
  | wf_type_param: forall x e,
      kind x = TYPE -> In x (dom e) ->
      wf_type e (Tparam x)
  | wf_type_top: forall e,
      wf_type e Top
  | wf_type_arrow: forall e t1 t2,
      wf_type e t1 -> wf_type e t2 -> wf_type e (Arrow t1 t2)
  | wf_type_forall: forall e t1 t2,
      wf_type e t1 ->
      (forall x,
         kind x = TYPE -> ~In x (fv_type t2) -> ~In x (dom e) ->
         wf_type ((x, t1) :: e) (freshen_type t2 x)) ->
      wf_type e (Forall t1 t2).

(** The rules are straightforward, except perhaps the
  [wf_type_forall] rule.  It follows a general pattern
  for operating over sub-terms of a binder, such as
  [t2] in [Forall t1 t2].  The de Bruijn variable [Tvar 0]
  is potentially free in [t2].  To recover a well-formed term,
  without free de Bruijn variables, we substitute [Tvar 0]
  with a fresh name [x].  Therefore, the premise for [t2]
  applies to [freshen_type t2 x].

  How should [x] be chosen?  As in the name-based specification,
  [x] must not be in the domain of [e], otherwise the
  extended environment [(x, t1) :: e] would be ill-formed.
  In addition, the name [x] must not be free in [t2],
  otherwise the freshening [freshen_type t2 x]
  would incorrectly identify the bound, universally-quantified
  variable of the [Forall] types with an existing, free type
  variable.  

  How should [x] be quantified?  That is, should the second premise
  [wf_type ((x, t1) :: e) (freshen_type t2 x))]
  hold for one particular name [x] not in [dom(e)], or
  for all names [x] not in [dom(e)]?
  The ``for all'' alternative obviously leads to a stronger
  induction principle: proofs that proceed by inversion or
  induction over an hypothesis [wf_type e (Forall t1 t2)]
  can then choose any convenient [x] fresh for [e] to exploit
  the second premise, rather than having to cope with a fixed,
  earlier choice of [x].  Symmetrically, the ``for one'' alternative
  is more convenient for proofs that must conclude
  [wf_type e (Forall t1 t2)]: it suffices to
  exhibit one suitable [x] fresh in [e] that satisfies the
  second premise, rather than having to establish the second
  premise for all such [x].  

  The crucial observation is that those two alternative are
  equivalent: the same subtyping judgements can be derived
  with the ``for all'' rule and the ``for one'' rule.
  (See Pollack's talk for more explanations.)  Therefore,
  in the definition of the [wf_type] predicate above,
  we chose the ``for all'' rule, so as to get the strongest
  induction principle.  And we will show shortly that the
  ``for one'' rule is admissible and can be used in
  proofs that conclude [wf_type e (Forall t1 t2)].
*)

(** An environment is well-formed if every type it contains
  is well-formed in the part of the environment that occurs to its
  right, i.e. the environment at the time this type was introduced.
  This ensures in particular that all the variables in this type
  are bound earlier (i.e. to the right) in the environment.
  Moreover, we impose that no name is bound twice in an
  environment. *)

Inductive wf_env: typenv -> Prop :=
  | wf_env_nil:
      wf_env nil
  | wf_env_cons: forall x t e,
      wf_env e -> ~In x (dom e) -> wf_type e t ->
      wf_env ((x, t) :: e).

Lemma wf_type_env_incr:
  forall e t, wf_type e t -> forall e', incl (dom e) (dom e') -> wf_type e' t.
Proof.
  induction 1; simpl; intros.
  constructor; auto.
  constructor.
  constructor; auto. 
  constructor; auto. intros. apply H1; auto.
  simpl. apply incl_cons2. auto. 
Qed.

(** A type well formed in [e] has all its free names in the
  domain of [e]. *)

Lemma fv_wf_type: forall x e t, wf_type e t -> In x (fv_type t) -> In x (dom e).
Proof.
  induction 1; simpl; intros.
  replace x with x0. auto. tauto.
  elim H.
  elim (in_app_or _ _ _ H1); auto.
  elim (in_app_or _ _ _ H2); auto. 
  intro. elim (fresh_name TYPE (x :: fv_type t2 ++ dom e)); intros y [FRESH KIND].
  assert (In x (dom ((y, t1) :: e))). 
    apply H1; eauto. apply fv_type_freshen_type. auto.
  elim H4; auto.
  simpl; intro; subst y. simpl in FRESH. tauto.
Qed.

(** Looking up the type of a name in a well-formed environment
  returns a well-formed type. *)

Lemma wf_type_lookup: forall e, wf_env e -> forall x t, lookup x e = Some t -> wf_type e t.
Proof.
  induction 1; intros.
  discriminate.
  apply wf_type_env_incr with e.
  simpl in H2. destruct (eq_name x0 x). replace t0 with t. auto. congruence. 
  eauto.
  simpl. red; intros; apply in_cons; auto. 
Qed.

(** Type well-formedness is stable by swapping. *)

Lemma wf_type_swap:
  forall u v e t, 
  kind u = kind v -> wf_type e t -> wf_type (swap_env u v e) (swap_type u v t).
Proof.
  intros until t. intro KIND.
  induction 1; simpl; intros.
  apply wf_type_param. 
    rewrite swap_kind; auto. 
    generalize (in_dom_swap u v x e). tauto.
  apply wf_type_top.
  apply wf_type_arrow; auto.
  apply wf_type_forall; auto.
    intros. 
    pose (x' := swap u v x). 
    assert (x = swap u v x'). unfold x'; symmetry; apply swap_inv.
    assert (~In x' (fv_type t2)). rewrite H5 in H3. 
    generalize (in_fv_type_swap u v x' t2). tauto.
    assert (~In x' (dom e)). rewrite H5 in H4.
    generalize (in_dom_swap u v x' e). tauto.
    assert (kind x' = TYPE).
      unfold x'. rewrite swap_kind; auto.
    generalize (H1 x' H8 H6 H7). simpl. 
    rewrite freshen_type_swap. simpl. rewrite <- H5.
    auto.
Qed.

(** Environment well-formedness is stable by swapping. *)

Lemma wf_env_swap:
  forall u v e, kind u = kind v -> wf_env e -> wf_env (swap_env u v e).
Proof.
  induction 2; simpl. 
  constructor.
  constructor. auto. 
  generalize (in_dom_swap u v x e). tauto.
  apply wf_type_swap; auto.
Qed.

(** The domain of an environment is invariant by swaps of names that are not in this domain. *)

Lemma swap_env_dom:
  forall u v e, ~In u (dom e) -> ~In v (dom e) -> dom (swap_env u v e) = dom e.
Proof.
  induction e; intros; simpl.
  auto.
  destruct a as [x t]. simpl dom in *. simpl. decEq.
  apply swap_other; eauto. eauto. 
Qed. 

(** A well-formed environment is invariant by swaps of names
  that are not in the domains of this environment. *)

Lemma swap_env_not_free:
  forall u v e, wf_env e -> ~In u (dom e) -> ~In v (dom e) -> swap_env u v e = e.
Proof.
  induction 1; simpl; intros.
  auto.
  decEq. decEq. apply swap_other; eauto.
  apply swap_type_not_free; eauto. 
  generalize (fv_wf_type u _ _ H1). tauto.
  generalize (fv_wf_type v _ _ H1). tauto.
  auto.
Qed.

(** We now show that the alternate formulation of rule [wf_type_forall]
  (the one with ``for one fresh name [x]'' instead of
   ``for all fresh names [x]'' in the second premise)
  is admissible. *)

Lemma wf_type_forall':
  forall e x t t1 t2,
  wf_type e t1 -> kind x = TYPE -> ~In x (fv_type t2) -> ~In x (dom e) ->
  wf_type ((x, t) :: e) (freshen_type t2 x) ->
  wf_type e (Forall t1 t2).
Proof.
  intros. constructor. auto. intros. 
  assert (kind x = kind x0). congruence.
  generalize (wf_type_swap x x0 _ _ H7 H3). simpl. 
  rewrite swap_left. 
  rewrite freshen_type_swap. simpl. rewrite swap_left. 
  rewrite (swap_type_not_free x x0 t2); auto. 
  intro. eapply wf_type_env_incr; eauto. simpl. 
  rewrite swap_env_dom; auto. 
Qed.

(** * Algorithmic subtyping *)

(** We now define the subtyping judgement as an inductive
  predicate.  Each constructor of the predicate corresponds
  to an inference rule in the original definition of subtyping. *)

Inductive is_subtype: typenv -> type -> type -> Prop :=
  | sa_top: forall e s,
      wf_env e -> wf_type e s ->
      is_subtype e s Top
  | sa_refl_tvar: forall e x u,
      wf_env e -> kind x = TYPE -> lookup x e = Some u ->
      is_subtype e (Tparam x) (Tparam x)
  | sa_trans_tvar: forall e x u t,
      kind x = TYPE -> lookup x e = Some u -> is_subtype e u t ->
      is_subtype e (Tparam x) t
  | sa_arrow: forall e s1 s2 t1 t2,
      is_subtype e t1 s1 -> is_subtype e s2 t2 ->
      is_subtype e (Arrow s1 s2) (Arrow t1 t2)
  | sa_all: forall e s1 s2 t1 t2,
      is_subtype e t1 s1 ->
      (forall x, 
         kind x = TYPE -> ~In x (dom e) ->
         is_subtype ((x, t1) :: e) (freshen_type s2 x) (freshen_type t2 x)) ->
      is_subtype e (Forall s1 s2) (Forall t1 t2).

(** The [sa_all] rule for [Forall] types follows the pattern
  that we already introduced for the [wf_type] predicate, in rule [wf_type_forall].
  In the original, name-based specification, we say that
  $E \vdash (\forall x <: \sigma_1.~\sigma_2) <:
            (\forall x <: \tau_1.~\tau_2)$
  if $E \vdash \tau_1 <: \sigma_1$ and
  $E, ~ x:\tau_1 \vdash \sigma_2 <: \tau_2$.
  The type variable $x$, being $\alpha$-convertible in the
  conclusion, is (implicitly or explicitly) chosen so that
  $E, ~ x:\tau_1$ is well-formed in the second premise,
  that is, $x$ is chosen not free in $E$.

  In our locally nameless representation, the type
  variables bound by [Forall] in the conclusion do not have
  names.  We must therefore invent a suitable name [x]
  and substitute it for the bound variable [TVar 0] in
  the types [s2] and [t2].  Therefore, the second premise
  puts [freshen_type s2 x] and [freshen_type t2 x] in subtype
  relation.

  As mentioned already, [x] should be chosen not in the domain
  of [e] (otherwise the extended environment [(x, t1) :: e] 
  would be ill-formed) and not free in [s2] and [t2],
  otherwise the freshenings [freshen_type s2 x] and [freshen_type t2 x]
  would incorrectly identify the bound, universally-quantified
  variable of the [Forall] types with an existing, free type
  variable.  However, as we will prove below, the rules for
  [is_subtype] satisfy a well-formedness condition:
  if [is_subtype e u1 u2], then [u1] and [u2] are well-formed
  in [e], implying that a name not in the domain of [e]
  cannot be free in [u1] or [u2].  Therefore, the condition
  ``[x] not in the domain of [e]'' suffices to ensure that
  [x] is not free in [s2] and [t2], and that the
  freshenings [freshen_type s2 x] and [freshen_type t2 x]
  make sense.

  As mentioned already as well, we have a choice between
  quantifying over all suitable [x] or over one suitable [x]
  in the second premise.  Again, we go with the ``for all''
  alternative in order to obtain the strongest induction
  principle, and we will show later that the ``for one''
  alternative is derivable.

  For the time being, we start with simple well-formedness
  properties of the types and environments involved in a
  [is_subtype] relation. *)

Lemma is_subtype_wf_env: forall e s t, is_subtype e s t -> wf_env e.
Proof.
  induction 1; intros; eauto.
Qed.

Lemma is_subtype_wf_type: forall e s t, is_subtype e s t -> wf_type e s /\ wf_type e t.
Proof.
  induction 1; intros.
  split. auto. apply wf_type_top.
  split; apply wf_type_param; auto; eapply lookup_inv; eauto.
  split. apply wf_type_param; auto. eapply lookup_inv; eauto. tauto.
  split; apply wf_type_arrow; tauto.
  elim IHis_subtype; intros. 
  elim (fresh_name TYPE (dom e ++ fv_type s2 ++ fv_type t2)).
  intros x [FRESH KIND].
  assert (~In x (dom e)). eauto.
  elim (H1 x KIND H4); intros.
  split; eapply wf_type_forall'; eauto. 
Qed.

Lemma is_subtype_wf_type_l: forall e s t, is_subtype e s t -> wf_type e s.
Proof.
  intros. elim (is_subtype_wf_type _ _ _ H); auto.
Qed.

Lemma is_subtype_wf_type_r: forall e s t, is_subtype e s t -> wf_type e t.
Proof.
  intros. elim (is_subtype_wf_type _ _ _ H); auto.
Qed.

Hint Resolve is_subtype_wf_env is_subtype_wf_type_l is_subtype_wf_type_r.

(** We now show that the [is_subtype] predicate is stable
  by swapping.  This property is crucial to show the 
  equivalence of the ``for all'' and ``for one'' interpretations
  of rule [sa_all]. *)

Lemma is_subtype_swap:
  forall u v, kind u = kind v ->
  forall e s t, is_subtype e s t ->
  is_subtype (swap_env u v e) (swap_type u v s) (swap_type u v t).
Proof.
  intros u v KINDuv. induction 1; simpl.
  (* sa_top *)
  apply sa_top. apply wf_env_swap; auto. apply wf_type_swap; auto.
  (* sa_refl *)
  eapply sa_refl_tvar. 
    apply wf_env_swap; auto. 
    rewrite swap_kind; auto.
    apply lookup_swap; eauto.
  (* sa_trans *)
  eapply sa_trans_tvar. 
    rewrite swap_kind; auto.
    apply lookup_swap; eauto. auto.
  (* sa_arrow *)
  apply sa_arrow; auto.
  (* sa_all *)
  apply sa_all. auto. 
  intros. 
  pose (x' := swap u v x).
  assert (kind x' = TYPE).
    unfold x'. rewrite swap_kind; auto.
  assert (~In x' (dom e)). 
    generalize (in_dom_swap u v x' e). unfold x'. rewrite swap_inv. tauto.
  generalize (H1 x' H4 H5). repeat rewrite freshen_type_swap. simpl. 
  replace (swap u v x') with x. auto. unfold x'. rewrite swap_inv. auto.
Qed.

(** Two silly lemmas about freshness of names in types. *)

Lemma fresh_wf_type: forall x e t, wf_type e t -> ~In x (dom e) -> ~In x (fv_type t).
Proof.
  intros. generalize (fv_wf_type x _ _ H). tauto.
Qed.

Lemma fresh_freshen_type:
  forall x t1 e t y,
  wf_type ((x, t1) :: e) (freshen_type t x) -> ~In y (dom e) -> x <> y -> ~In y (fv_type t).
Proof.
  intros. 
  red; intro.
  assert (In y (dom ((x, t1) :: e))).
    eapply fv_wf_type. eauto. apply fv_type_freshen_type. auto.
  elim H3; simpl; intros. contradiction. contradiction.
Qed.

(** We now show that the alternate presentation of rule [sa_all]
  (the one with ``for one name'' in the second premise
  instead of ``for all names'') is admissible. *)

Lemma sa_all':
  forall e s1 s2 t1 t2 x,
  is_subtype e t1 s1 ->
  kind x = TYPE -> ~In x (dom e) -> ~In x (fv_type s2) -> ~In x (fv_type t2) ->
  is_subtype ((x, t1) :: e) (freshen_type s2 x) (freshen_type t2 x) ->
  is_subtype e (Forall s1 s2) (Forall t1 t2).
Proof.
  intros. apply sa_all. auto. 
  intros y DOM. 
  case (eq_name x y); intro. subst y. auto.
  elim (is_subtype_wf_type _ _ _ H). intros.
  elim (is_subtype_wf_type _ _ _ H4). intros.
  assert (~In y (fv_type s2)). 
    apply fresh_freshen_type with x t1 e; auto.
  assert (~In y (fv_type t2)). 
    apply fresh_freshen_type with x t1 e; auto.
  replace ((y, t1) :: e) with (swap_env x y ((x, t1) :: e)).
  replace (freshen_type s2 y)
     with (swap_type x y (freshen_type s2 x)).
  replace (freshen_type t2 y)
     with (swap_type x y (freshen_type t2 x)).
  apply is_subtype_swap; auto. congruence.
  rewrite freshen_type_swap. rewrite swap_left. 
  rewrite swap_type_not_free; auto. 
  rewrite freshen_type_swap. simpl. rewrite swap_left. 
  rewrite swap_type_not_free; auto. 
  simpl. rewrite swap_left. rewrite swap_env_not_free; auto.
  rewrite swap_type_not_free. auto.
  apply fresh_wf_type with e; auto.
  apply fresh_wf_type with e; auto. 
  eapply is_subtype_wf_env; eauto.
Qed.

(** * Reflexivity and transitivity of subtyping *)

(** We now turn (at last!) to proving the two theorems of
  part 1 of the POPLmark challenge: reflexivity
  and transitivity of subtyping. **)

(** Reflexivity of subtyping is shown by straightforward induction
  on the derivation of well-formedness of the type.
  As noted by McKinna and Pollack, such inductions conveniently
  replace inductions on the structure of types. *)

Theorem sub_refl: forall t e, wf_type e t -> wf_env e -> is_subtype e t t.
Proof. 
  induction 1; intros.
  (** Case [t = Tparam x] *)
  destruct (lookup_exists _ _ H0) as [t L]. 
  apply sa_refl_tvar with t; auto. 
  (** Case [t = Top] *)
  apply sa_top. auto. constructor.
  (** Case [t = Arrow t1 t2] *)
  apply sa_arrow. auto. auto.
  (** Case [t = Forall t1 t2] *)
  destruct (fresh_name TYPE (fv_type t2 ++ dom e)) as [x [FRESH KIND]].
  apply sa_all' with x; eauto.
  apply H1; eauto.
  constructor; eauto.
Qed.

(** We now do some scaffolding work for the proof of
  transitivity.  First, we will need to perform inductions
  over the size of types.  We cannot just do inductions
  over the structure of types, as the original paper proof did,
  because in the case of [Forall t1 t2], we will need to recurse not on [t2]
  but on [freshen_type t2 x] for some x, which is not a
  sub-term of [t2].  However, the size of [freshen_type t2 x]
  is the same as the size of [t2], so induction over sizes
  will work. *)

Fixpoint size_type (t: type): nat :=
  match t with
  | Tparam _ => 0
  | Tvar _ => 0
  | Top => 0
  | Arrow t1 t2 => 1 + size_type t1 + size_type t2
  | Forall t1 t2 => 1 + size_type t1 + size_type t2
  end.

Lemma vsubst_type_size: forall x a n, size_type (vsubst_type a n (Tparam x)) = size_type a.
Proof.
  induction a; simpl; intros; auto.
  case (compare_nat n n0); reflexivity.
Qed.

Lemma freshen_type_size: forall x a, size_type (freshen_type a x) = size_type a.
Proof.
  unfold freshen_type; intros. apply vsubst_type_size.
Qed.

(** We now define a notion of inclusion between environments
  that we call ``weakening''. [e2] weakens [e1] if all the bindings in [e1]
  are preserved in [e2]; however, [e2] may contain additional, non-interfering bindings. *)

Definition env_weaken (e1 e2: typenv) : Prop :=
  forall x t, lookup x e1 = Some t -> lookup x e2 = Some t.

Lemma env_weaken_incl_dom: forall e1 e2, env_weaken e1 e2 -> incl (dom e1) (dom e2).
Proof.
  unfold incl; intros. 
  elim (lookup_exists _ _ H0). intros t LOOKUP. 
  apply lookup_inv with t. apply H. auto.
Qed.

(** The subtyping relation is stable by weakening of the typing environment. *)

Lemma sub_weaken:
  forall e s t, is_subtype e s t -> forall e', wf_env e' -> env_weaken e e' -> is_subtype e' s t.
Proof.
  induction 1; intros.
  (* Rule sa_top *)
  apply sa_top. auto. apply wf_type_env_incr with e. auto.
  apply env_weaken_incl_dom; auto.
  (* Rule sa_refl_tvar *)
  apply sa_refl_tvar with u; auto. 
  (* Rule sa_trans_tvar *)
  apply sa_trans_tvar with u; auto. 
  (* Rule sa_arrow *)
  apply sa_arrow; auto.
  (* Rule sa_all *)
  apply sa_all; auto. intros. apply H1; auto.
  generalize (env_weaken_incl_dom _ _ H3 x). tauto.
  constructor; auto. apply wf_type_env_incr with e; eauto.
  apply env_weaken_incl_dom; auto.
  red; intro y. simpl. case (eq_name y x); auto. 
Qed.

(** A special case of weakening is the addition of bindings to an existing typing
  environment, provided the resulting environment is well-formed.  *)

Lemma env_concat_weaken:
  forall delta gamma,
  wf_env (delta ++ gamma) -> env_weaken gamma (delta ++ gamma).
Proof.
  induction delta; simpl; intros. 
  red; auto. 
  inversion H. red; intros; simpl. 
  rewrite eq_name_false. apply IHdelta. auto. auto.
  red; intro. subst x0. elim H3. 
  unfold dom. rewrite map_append. apply in_or_app. right.
  apply lookup_inv with t0. auto.
Qed.

(** The following lemmas prove useful properties of environments
  of the form [e1 ++ (x, p) :: e2], that is, all bindings of [e2],
  followed by a binding of [p] to [x], followed by all bindings of [e1]. *)

Lemma dom_env_extends: forall e1 x p q e2, dom (e1 ++ (x, p) :: e2) = dom (e1 ++ (x, q) :: e2).
Proof.
  intros. repeat rewrite dom_append. reflexivity.
Qed.

Lemma wf_env_extends:
  forall e2 x p q e1, wf_env (e1 ++ (x, p) :: e2) -> wf_type e2 q -> wf_env (e1 ++ (x, q) :: e2).
Proof.
  induction e1; simpl; intros.
  inversion H. constructor; auto.
  inversion H. constructor; auto.
  rewrite (dom_env_extends e1 x q p e2). auto.
  apply wf_type_env_incr with (e1 ++ (x, p) :: e2); auto.
  rewrite (dom_env_extends e1 x q p e2). apply incl_refl.
Qed.

Lemma lookup_env_extends:
  forall e2 x p q y e1,
  wf_env (e1 ++ (x, q) :: e2) ->
  lookup y (e1 ++ (x, p) :: e2) = if eq_name y x then Some p else lookup y (e1 ++ (x, q) :: e2).
Proof.
  induction e1; simpl; intros.
  case (eq_name y x); auto.
  destruct a. inversion H. subst x0; subst t0; subst e.
  case (eq_name y n); intro. subst n.
  rewrite eq_name_false. auto. red; intros; subst x. 
  elim H4. unfold dom. rewrite map_append. 
  apply in_or_app. right. simpl. tauto.
  apply IHe1. auto.
Qed.

(** Now comes the major result: transitivity and the narrowing
  property of subtyping, proved simultaneously.
  The proof follows the structure of the paper proof,
  with the structural induction on [q] being replaced
  by a Peano induction on the size of [q]. *)

Lemma sub_trans_narrow:
  forall n,
     (forall e s q t, 
       size_type q <= n ->
       is_subtype e s q -> is_subtype e q t ->
       is_subtype e s t)
  /\ (forall x e1 e2 p q r s,
       size_type q <= n ->
       is_subtype (e1 ++ (x, q) :: e2) r s -> is_subtype e2 p q ->
       is_subtype (e1 ++ (x, p) :: e2) r s).
Proof. 
  intro n0. pattern n0. apply Peano_induction.
  intros size HRsize.
  (** Part 1: transitivity **)
  assert (forall e s q, is_subtype e s q ->
          forall t, size_type q <= size -> is_subtype e q t -> is_subtype e s t).
  (** Sub-induction on the derivation of [is_subtype e s q] **)
  induction 1; intros.
  (** Case [sa_top] **)
  inversion H2. apply sa_top. auto. eauto. 
  (** Case [sa_refl_tvar] **)
  auto.
  (** Case [sa_trans_tvar] **)
  apply sa_trans_tvar with u; auto.
  (** Case [sa_arrow] **)
  inversion H2. 
    apply sa_top. auto. inversion H4. constructor; eauto.
    subst e0; subst s0; subst s3. simpl in H1.
    assert (SZpos: pred size < size). omega.
    elim (HRsize (pred size) SZpos); intros HR1 HR2.
    apply sa_arrow. 
    (** Application of the outer induction hypothesis to [t1] **)
    apply HR1 with t1; auto. omega. 
    (** Application of the outer induction hypothesis to [t2] **)
    apply HR1 with t2; auto. omega.
  (** Case [sa_forall] **)
  inversion H3. 
    apply sa_top. auto. 
    apply is_subtype_wf_type_l with (Forall t1 t2). constructor; assumption.
    subst e0; subst s0; subst s3. simpl in H2.
    assert (SZpos: pred size < size). omega.
    elim (HRsize (pred size) SZpos); intros HR1 HR2.
    (** Choice of an appropriately fresh name x **)
    elim (fresh_name TYPE (dom e ++ fv_type t3 ++ fv_type s2)). 
    intros x [FRESH KIND].
    apply sa_all' with x; eauto.
    (** Application of the outer induction hypothesis to [t1] *)
    apply HR1 with t1; auto. omega.
    (** Application of the outer induction hypothesis to [freshen t2 x] *)
    apply HR1 with (freshen_type t2 x).
    rewrite freshen_type_size. omega.
    change ((x, t0) :: e) with (nil ++ (x, t0) :: e).
    (** Application of the narrowing part of the outer induction hypothesis. *)
    apply HR2 with t1. omega. 
    simpl. apply H0; eauto. auto. apply H9; eauto. 
  (** Part 2: narrowing *)
  assert (forall e r s,
    is_subtype e r s ->
    forall e1 x q e2 p,
    e = e1 ++ (x, q) :: e2 -> size_type q <= size -> is_subtype e2 p q ->
    is_subtype (e1 ++ (x, p) :: e2) r s).
  (** Sub-induction on the derivation of [is_subtype e r s] *)  
  induction 1; intros; subst e.
  (** Case [sa_top] *)
  apply sa_top. apply wf_env_extends with q; eauto.
  apply wf_type_env_incr with (e1 ++ (x, q) :: e2); auto.
  rewrite (dom_env_extends e1 x q p e2). apply incl_refl.
  (** Case [sa_refl_tvar] *)
  apply sa_refl_tvar with (if eq_name x x0 then p else u).
  apply wf_env_extends with q; eauto. auto.
  rewrite (lookup_env_extends e2 x0 p q x e1 H0). 
  case (eq_name x x0); auto.
  (** [Case sa_trans_tvar] *)
  apply sa_trans_tvar with (if eq_name x x0 then p else u).
  auto. rewrite (lookup_env_extends e2 x0 p q x e1).
  case (eq_name x x0); auto. eauto.
  case (eq_name x x0); intro. 
  (** sub-case [x = x0] *)
  generalize H1. rewrite (lookup_env_extends e2 x0 q q x e1); eauto.
  rewrite e; rewrite eq_name_true; intro EQ; injection EQ; intro; subst u.
  apply H with q. 
  apply sub_weaken with e2; auto. 
  apply wf_env_extends with q; eauto.
  change (e1 ++ (x0, p) :: e2) with (e1 ++ (((x0, p) :: nil) ++ e2)).
  rewrite <- app_ass. apply env_concat_weaken. 
  rewrite app_ass. simpl. apply wf_env_extends with q; eauto. 
  auto. 
  apply IHis_subtype with q; auto.
  (** sub-case [x <> x0] *)
  apply IHis_subtype with q; auto.
  (** Case [sa_arrow] *)
  apply sa_arrow. 
  apply IHis_subtype1 with q; auto.
  apply IHis_subtype2 with q; auto.
  (** Case [sa_forall] *)
  apply sa_all.
  apply IHis_subtype with q; auto.
  intros. 
  change ((x0, t1) :: e1 ++ (x, p) :: e2)
    with (((x0, t1) :: e1) ++ (x, p) :: e2).
  apply H2 with q. auto. 
  rewrite (dom_env_extends e1 x q p e2). auto.
  reflexivity. auto. auto. 
  (** Combining the two parts together *)
  split. intros; apply H with q; auto. 
  intros; apply H0 with (e1 ++ (x, q) :: e2) q; auto.
Qed. 

(** As a corollary, we obtain transitivity of subtyping. *)

Theorem sub_trans:
  forall e s q t, is_subtype e s q -> is_subtype e q t -> is_subtype e s t.
Proof.
  intros. elim (sub_trans_narrow (size_type q)); intros.
  apply H1 with q; auto. 
Qed.

(** As well as narrowing. **)

Theorem sub_narrow:
  forall x e1 e2 p q r s,
  is_subtype (e1 ++ (x, q) :: e2) r s -> is_subtype e2 p q ->
  is_subtype (e1 ++ (x, p) :: e2) r s.
Proof.
  intros. elim (sub_trans_narrow (size_type q)); intros.
  apply H2 with q; auto.
Qed.

(** * Stability of the subtyping judgement under substitutions *)

(** We now prove a property of the subtyping judgement that plays
  a crucial role later to prove that instantiation of polymorphic types is semantically sound.
  This property is stability under substitutions, namely
  that if $\Gamma, X <: U \vdash T_1 <: T_2$, then it must be the case
  that $\Gamma \vdash T_1[X \leftarrow U] <: T_2[X \leftarrow U]$.
  In the POPLmark challenge, this property belongs to part 2 of the
  challenge, but we prefer to prove it now, since it involves only
  the subtyping judgement.

  To prove stability under substitution by induction, we need to strengthen
  its statement as follows: if $\Gamma, X <: U, \Gamma' \vdash T_1 <: T_2$,
  then $\Gamma, \Gamma'[X \leftarrow U] \vdash 
                T_1[X \leftarrow U] <: T_2[X \leftarrow U]$.
  We therefore need to extend type substitutions to environments,
  pointwise. *)

Fixpoint psubst_env (e: typenv) (x: name) (b: type) {struct e} : typenv :=
  match e with
  | nil => nil
  | (y, t) :: e' => (y, psubst_type t x b) :: psubst_env e' x b
  end.

Lemma dom_psubst_env: forall x b e, dom (psubst_env e x b) = dom e.
Proof.
  induction e; simpl. auto. destruct a. simpl. congruence. 
Qed.

(** ** Commutation properties for type substitutions *)

(** As a preliminary result, we need to show that well-formedness of
  types and environments is preserved by substitution of a well-formed
  type for a name.  This simple property needs a number of commutation
  properties between the [psubst_type], [freshen_type] and
  [vsubst_type] functions.  Unfortunately, some hacking on de Bruijn
  indices is necessary.  We start by defining a predicate
  [type_vars_below t n] that holds if all free de Bruijn variables in
  the type [t] are less than [n].  In particular, 
  [type_vars_below t 0] holds iff [t] has no free de Bruijn variables. *)

Fixpoint type_vars_below (t: type) (n: nat) {struct t} : Prop :=
  match t with
  | Tparam x => True
  | Tvar m => m < n
  | Top => True
  | Arrow t1 t2 => type_vars_below t1 n /\ type_vars_below t2 n
  | Forall t1 t2 => type_vars_below t1 n /\ type_vars_below t2 (S n)
  end.

Lemma type_vars_below_vsubst:
  forall t n t', type_vars_below (vsubst_type t n t') n -> type_vars_below t (S n).
Proof.
  induction t; simpl; intros; auto.
  destruct (compare_nat n n0); simpl in H; omega.
  firstorder.
  firstorder. 
Qed.

(** A well-formed type, having no free de Bruijn variables,
  has all its de Bruijn variables below 0. *)

Lemma wf_type_vars_below_0: forall e t, wf_type e t -> type_vars_below t 0.
Proof.
  induction 1; simpl. auto. auto. tauto. 
  split. auto. destruct (fresh_name TYPE (fv_type t2 ++ dom e)) as [x [F K]].
  apply type_vars_below_vsubst with (Tparam x). apply H1; eauto. 
Qed.

(** A type is invariant by [vsubst_type] substitution if
  the de Bruijn variable being substituted is not free in the
  type. *)

Lemma vsubst_invariant_below:
  forall t n m s, type_vars_below t n -> n <= m -> vsubst_type t m s = t.
Proof.
  induction t; simpl; intros; auto.
  destruct (compare_nat n m); auto; elimtype False; omega.
  decEq; firstorder. 
  decEq; firstorder.
Qed.

(** As a corollary, well-formed types are invariant by [vsubst]
  substitutions. *)

Lemma vsubst_wf_type: forall e t n s, wf_type e t -> vsubst_type t n s = t.
Proof.
  intros. apply vsubst_invariant_below with 0. 
  eapply wf_type_vars_below_0; eauto. omega.
Qed.

(** It follows that [vsubst] and [psubst] substitutions commute
  in the following sense. *)

Lemma psubst_vsubst_type:
  forall e a x b n c,
  wf_type e b -> 
  vsubst_type (psubst_type a x b) n (psubst_type c x b) = 
  psubst_type (vsubst_type a n c) x b.
Proof.
  induction a; intros; simpl.
  case (eq_name n x); intro; simpl. 
  eapply vsubst_wf_type. eauto. 
  auto.
  case (compare_nat n n0); intro; auto.
  auto.
  decEq; eauto. 
  decEq; eauto. 
Qed.

(** Consequently, [psubst_type] and [freshen_type] commute
  if they operate on distinct names. *)

Lemma psubst_freshen_type:
  forall e a x b y,
  wf_type e b -> x <> y ->
  freshen_type (psubst_type a x b) y = psubst_type (freshen_type a y) x b.
Proof.
  intros. unfold freshen_type. 
  rewrite <- (psubst_vsubst_type e); auto.
  simpl. rewrite eq_name_false; auto.
Qed.

(** Additionally, [vsubst] substitution of de Bruijn variable 0 is
  equivalent to freshening with a fresh type name [x]
  followed by a [psubst] substitution over [x]. *)

Lemma vsubst_psubst_type:
  forall x t2 t1 n, ~In x (fv_type t1) ->
  vsubst_type t1 n t2 = psubst_type (vsubst_type t1 n (Tparam x)) x t2.
Proof.
  induction t1; simpl; intros.
  rewrite eq_name_false. auto. tauto.
  case (compare_nat n n0); intros; auto. 
  simpl. rewrite eq_name_true. auto.
  auto.
  decEq; eauto.
  decEq; eauto.
Qed.

Lemma vsubst_psubst_freshen_type:
  forall x t1 t2, ~In x (fv_type t1) -> 
  vsubst_type t1 0 t2 = psubst_type (freshen_type t1 x) x t2.
Proof.
  intros. unfold freshen_type. apply vsubst_psubst_type. auto.
Qed.

(** ** Preservation of well-formedness of types and environments during substitution *)

(** Well-formedness of types is preserved by [psubst_type] substitution of a well-formed type
  for a type name. *)

Lemma wf_type_psubst:
  forall e1 x p q e2 t,
  wf_type (e2 ++ (x, p) :: e1) t -> wf_type e1 q ->
  wf_type (psubst_env e2 x q ++ e1) (psubst_type t x q).
Proof.
  assert (forall e t, wf_type e t ->
          forall e1 x e2 p q,
          e = e2 ++ (x, p) :: e1 ->
          wf_type e1 q ->
          wf_type (psubst_env e2 x q ++ e1) (psubst_type t x q)).
  induction 1; intros; simpl.
  case (eq_name x x0); intro. 
  apply wf_type_env_incr with e1; auto. 
  rewrite dom_append. apply incl_appr. apply incl_refl.
  constructor. auto. 
  rewrite H1 in H0. rewrite dom_append in H0. simpl in H0. rewrite dom_append.
  apply in_or_app. elim (in_app_or _ _ _ H0); intro. 
  left. rewrite dom_psubst_env. auto. 
  elim H3; intro. congruence. auto.
  constructor.
  constructor; eauto.
  destruct (fresh_name TYPE (x :: fv_type t2 ++ dom e ++ 
                             fv_type (psubst_type t2 x q) ++ 
                             dom (psubst_env e2 x q ++ e1)))
  as [y [F K]].
  apply wf_type_forall' with y (psubst_type t1 x q); eauto. 
  change ((y, psubst_type t1 x q) :: psubst_env e2 x q ++ e1)
    with (psubst_env ((y, t1) :: e2) x q ++ e1).
  rewrite (psubst_freshen_type e1). eapply H1; eauto.
  subst e. simpl. reflexivity. auto. eauto. 

  eauto.
Qed.

(** Similarly, well-formedness of environments is preserved by [psubst_env] substitution. *)

Lemma wf_env_psubst:
  forall e1 x p q e2,
  wf_env (e2 ++ (x, p) :: e1) -> wf_type e1 q ->
  wf_env (psubst_env e2 x q ++ e1).
Proof.
  induction e2; simpl; intros. inversion H. auto.
  inversion H. subst. simpl. constructor. auto. 
  rewrite dom_append. rewrite dom_psubst_env. 
  rewrite dom_append in H4. simpl in H4. 
  red; intro. elim (in_app_or _ _ _ H1); intro; apply H4; eauto.
  apply in_or_app. right. simpl; tauto.
  eapply wf_type_psubst; eauto.
Qed.

(** ** Type substitution preserves subtyping *)

(** We now show that if [s] is subtype of [t] in the environment
  [e2 ++ (x, p) :: e1], and if [q] is subtype of [p] in [e1],
  then [psubst s x q] is subtype of [psubst t x q] in
  [psubst_env x q e2 ++ e1].

  Well-formed environments of the form [e2 ++ (x, p) :: e1]
  are such that [x] is not in the domain of [e1] and not free
  in the types listed in [e1].  Therefore, these types are
  invariant by substitution over [x]. *)

Lemma env_concat_not_free: forall e1 x p e2, wf_env (e2 ++ (x, p) :: e1) -> ~In x (dom e1).
Proof.
  induction e2; simpl; intros; inversion H; auto.
Qed.

Lemma psubst_type_inv: forall t x s, ~In x (fv_type t) -> psubst_type t x s = t.
Proof.
  induction t; simpl; intros; try decEq; auto.
  apply eq_name_false. tauto.
Qed. 

(** The following technical lemma relates [lookup] operations
  between the original environment [e2 ++ (x, p) :: e1]
  and its substituted counterpart, [psubst_env e2 x q ++ e1]. *)

Lemma lookup_env_concat:
  forall e1 x p q y t e2,
  wf_env (e2 ++ (x, p) :: e1) ->
  lookup y (e2 ++ (x, p) :: e1) = Some t ->
  (x = y /\ t = p) \/ 
  (x <> y /\ lookup y (psubst_env e2 x q ++ e1) = Some (psubst_type t x q)).
Proof.
  induction e2; simpl; intros.
  destruct (eq_name y x). 
  left; split; congruence.
  right; split. congruence. 
  inversion H. replace (psubst_type t x q) with t. auto.
  symmetry. apply psubst_type_inv. 
  assert (wf_type e1 t). eapply wf_type_lookup; eauto.
  generalize (fv_wf_type x _ _ H7). firstorder. 
  destruct a as [z t']. inversion H; subst. 
  assert (z <> x). rewrite dom_append in H5. simpl in H5. eauto. 
  simpl. destruct (eq_name y z).
  right. split; congruence. 
  auto.
Qed.

(** We can now prove the stability of subtyping by type substitution
  (lemma A.10 in the challenge statement).  The proof proceeds
  by induction over the derivation of the second subtyping hypothesis. *)

Theorem sub_stable_subst:
  forall e1 x p q e2 s t,
  is_subtype e1 p q ->
  is_subtype (e2 ++ (x, q) :: e1) s t ->
  is_subtype (psubst_env e2 x p ++ e1) (psubst_type s x p) (psubst_type t x p).
Proof. 
  assert (forall e1 x p q, is_subtype e1 p q ->
          forall e s t, is_subtype e s t ->
          forall e2, e = e2 ++ (x, q) :: e1 ->
          is_subtype (psubst_env e2 x p ++ e1)
                     (psubst_type s x p) (psubst_type t x p)).
  induction 2; intros; simpl; subst e.
  (** Rule [sa_top] *)
  constructor. eapply wf_env_psubst; eauto. 
  eapply wf_type_psubst; eauto. 
  (** Rule [sa_refl] *)
  apply sub_refl. 
  case (eq_name x0 x); intro. 
  (** Rule [sa_refl], case [x = x0] *)
  apply wf_type_env_incr with e1; eauto.
  rewrite dom_append. apply incl_appr. apply incl_refl.
  (** Rule [sa_refl], case [x <> x0] *)
  constructor. auto. generalize (lookup_inv _ _ _ H2). 
  repeat rewrite dom_append. simpl. rewrite dom_psubst_env. 
  intro. apply in_or_app. elim (in_app_or _ _ _ H3); intro. 
  auto. elim H4; intro. congruence. auto.
  eapply wf_env_psubst; eauto. 
  (** Rule [sa_trans] *)
  assert (wf_env (e2 ++ (x, q) :: e1)). eapply is_subtype_wf_env; eauto.
  generalize (lookup_env_concat _ _ _ p _ _ _ H3 H1). intro.
  case (eq_name x0 x); intro.
  (** Rule [sa_trans], case [x = x0] *)
  subst x0. assert (u = q). intuition. subst u.
  apply sub_trans with (psubst_type q x p). 
  replace (psubst_type q x p) with q. 
  apply sub_weaken with e1. auto. eapply wf_env_psubst; eauto. 
  apply env_concat_weaken. eapply wf_env_psubst; eauto.
  symmetry. apply psubst_type_inv. 
  assert (wf_type e1 q). eapply is_subtype_wf_type_r; eauto. 
  generalize (fv_wf_type x _ _ H5). 
  generalize (env_concat_not_free _ _ _ _ H3). tauto. 
  apply IHis_subtype. auto. 
  (** Rule [sa_trans], case [x <> x0] *)
  apply sa_trans_tvar with (psubst_type u x p).
  auto. generalize (sym_not_equal n); tauto. 
  apply IHis_subtype. auto. 
  (** Rule [sa_arrow] *)
  constructor; auto.
  (** Rule [sa_forall] *)
  destruct (fresh_name TYPE (x :: dom (e2 ++ (x, q) :: e1) ++
                             dom (psubst_env e2 x p ++ e1) ++
                             fv_type (psubst_type s2 x p) ++
                             fv_type (psubst_type t2 x p)))
  as [y [F K]].
  eapply sa_all'; eauto. 
  repeat rewrite (psubst_freshen_type e1). 
  change ((y, psubst_type t1 x p) :: psubst_env e2 x p ++ e1)
    with (psubst_env ((y, t1) :: e2) x p ++ e1).
  apply H2; eauto. eauto. eauto. eauto. eauto.

  eauto.
Qed.


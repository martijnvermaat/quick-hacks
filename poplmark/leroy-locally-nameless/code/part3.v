(** In this chapter, we consider the problem of executing $F_{<:}$ terms
  as prescribed by the reduction semantics for this language.  Such
  executions are useful for testing that the semantics has the intended
  behavior.  This goal is listed as part 3 in the
  POPLmark challenge.  As we will see, our development will go one
  step further and result in the production of an efficient and
  provably correct interpreter for $F_{<:}$.

  There are two approaches to executing dynamic semantics within Coq.
  The first operates directly on a relational specification of the semantics,
  either big-step or small-step like our [red] predicate from chapter 3.
  The [eauto] Coq tactic, which build proofs by Prolog-style
  resolution over a set of predeclared inference rules and lemmas, can
  be abused to search and build derivation trees for a goal of the
  form [exists b, red a b], therefore executing one reduction step from [a].
  An example of this approach can be found in our work with A. Appel
  on the list-machine benchmark %\cite{Appel-Leroy-listmachine-tr}%.
  However, this approach is tricky to set up and very inefficient.

  The other approach, which we follow in this chapter, is to specify
  the operational semantics as functions rather than predicates.
  While Coq has no efficient built-in execution mechanism for logic
  programs (composed of inductively-defined predicates), it can natively
  evaluate functional programs (composed of functions defined by recursion
  and pattern-matching).  Such functional reductions are actually
  part of the logic of Coq, via the notion of conversion.

  We therefore proceed in two steps.  We will first define functions
  that compute the one-step or $N$-step reduct of a $F_{<:}$ term,
  and prove that they are correct and complete with respect to the
  relational semantics.  We will then use these functions to evaluate
  terms within Coq and to extract efficient Caml code for an interpreter.
*)

Require Import Arith.
Require Import ZArith.
Require Import List.
Require Import extralibrary.
Require Import part1a.
Require Import part2a.

(** * Execution of one-step reductions *)

(** We first show that the [isvalue] predicate is decidable.
  The lemma below will actually provides us with a decision procedure
  that takes any term [a] and returns whether it is a value or not.
  We can then use this decision procedure within function definitions. *)

Lemma isvalue_dec:
  forall a, {isvalue a} + {~isvalue a}.
Proof.
  destruct a; (left; constructor) || (right; red; intro H; inversion H).
Defined.

(** The [reduce] function maps a term [a] to either [Some b] if
  [a] reduces in one step to [b], or to [None] if [a] does not reduce.
  It is defined by structural recursion over [a] and case analysis
  on whether subterms of [a] are values, or reduce, or are stuck. *)

Fixpoint reduce (a: term) : option term :=
  match a with
  | App b c =>
      if isvalue_dec b then
        if isvalue_dec c then
          match b with Fun t d => Some (vsubst_term d 0 c) | _ => None end
        else
          match reduce c with Some c' => Some(App b c') | None => None end
      else
        match reduce b with Some b' => Some(App b' c) | None => None end
  | TApp b t =>
      if isvalue_dec b then
        match b with TFun t' c => Some (vsubst_tety c 0 t) | _ => None end
      else
        match reduce b with Some b' => Some(TApp b' t) | None => None end
  | _ => None
  end.

(** We then show that this function is correct and complete with respect
  to the reduction rules: [reduce a = Some b] if and only if [red a b]
  holds.  The proofs are routine inductions on the structure of [a]
  for the ``only if'' part and on the derivation of [red a b] for the
  ``if'' part. *)

Lemma reduce_is_correct:
  forall a a', reduce a = Some a' -> red a a'.
Proof.
  induction a; simpl; intros; try discriminate.
  destruct (isvalue_dec a1). destruct (isvalue_dec a2).
  destruct a1; inversion H. apply red_appabs; auto.
  destruct (reduce a2); inversion H. apply red_apparg; auto.
  destruct (reduce a1); inversion H. apply red_appfun; auto.
  destruct (isvalue_dec a).
  destruct a; inversion H. apply red_tapptabs; auto.
  destruct (reduce a); inversion H. apply red_tapp; auto.
Qed.

Lemma isvalue_dec_true:
  forall a (T: Set) (b c: T), isvalue a -> (if isvalue_dec a then b else c) = b.
Proof.
  intros. destruct (isvalue_dec a). auto. contradiction.
Qed.

Lemma isvalue_dec_false:
  forall a a' (T: Set) (b c: T), red a a' -> (if isvalue_dec a then b else c) = c.
Proof.
  intros. destruct (isvalue_dec a). 
  inversion i; subst a; inversion H.
  auto. 
Qed.

Lemma reduce_is_complete:
  forall a a', red a a' -> reduce a = Some a'.
Proof.
  induction 1; simpl. 
  apply isvalue_dec_true; auto.
  auto.
  rewrite (isvalue_dec_false a a'); auto. rewrite IHred; auto.
  rewrite isvalue_dec_true; auto. 
  rewrite (isvalue_dec_false b b'); auto. rewrite IHred; auto.
  rewrite (isvalue_dec_false a a'); auto. rewrite IHred; auto.
Qed.

(** * Execution of [N]-step reductions *)

(** The following function iterates the one-step reduction function
  [compute] to obtain the normal form of a term.  Since Coq functions
  must always terminate, we need to bound the number of iterations
  by the [n] parameter.  If a normal form cannot be reached in [n]
  steps, [compute] returns [None]. *)

Fixpoint compute (n: nat) (a: term) {struct n}: option term :=
  match n with
  | O => None
  | S n' =>
      match reduce a with
      | Some a' => compute n' a'
      | None => Some a
      end
  end.

(** We now show that [compute a], if it succeeds, returns a
  reduct of [a] that is in normal form (irreducible). *)

Definition irreducible (a: term): Prop := forall b, ~red a b.

Inductive red_sequence: term -> term -> Prop :=
  | red_sequence_0:
      forall a, irreducible a -> red_sequence a a
  | red_sequence_1: forall a b c,
      red a b -> red_sequence b c -> red_sequence a c.

Lemma compute_correct:
  forall n a a', compute n a = Some a' -> red_sequence a a'.
Proof.
  induction n; intros until a'; simpl.
  congruence.
  caseEq (reduce a); intros.
  apply red_sequence_1 with t. apply reduce_is_correct; auto. auto.
  inversion H0. apply red_sequence_0. 
  intro; red; intro. generalize (reduce_is_complete _ _ H1). congruence.
Qed.

(** Conversely, if a term [a] has a normal form [a'], there exists
  a number of iterations [n] such that [compute] returns [Some a']. *)

Lemma compute_complete:
  forall a a', red_sequence a a' -> exists n, compute n a = Some a'.
Proof.
  induction 1.
  exists 1; simpl. caseEq (reduce a); intros. 
  generalize (reduce_is_correct _ _ H0). firstorder. auto.
  destruct IHred_sequence as [n C]. exists (S n). simpl. 
  rewrite (reduce_is_complete _ _ H). auto.
Qed.

(** * Experiments *)

(** We can now use the Coq directives [Eval compute in (reduce a)]
  and [Eval compute in (compute N a)] to display the results of
  performing one or [N] reduction steps in [a]. *)

Definition F_poly_identity := TFun Top (Fun (Tvar 0) (Var 0)).
Definition F_top_identity := TApp F_poly_identity Top.
Definition F_delta := Fun (Arrow Top Top) (App (Var 0) (Var 0)).
Definition F_testprog := App F_delta F_top_identity.

Eval compute in (reduce F_testprog).
Eval compute in (compute 100 F_testprog).

(** The latter returns [Some (Fun Top (Var 0))], which is indeed
the value of the term [F_testprog].  For a larger example, here is
some arithmetic on Church integers. *)
  
Definition F_one : term :=
  (TFun Top (TFun (Tvar 0) (TFun (Tvar 1)
        (Fun (Arrow (Tvar 2) (Tvar 1))
          (Fun (Tvar 0)
            (App (Var 1) (Var 0))))))).

Definition F_nat : type :=
  (Forall Top
    (Forall (Tvar 0)
      (Forall (Tvar 1)
        (Arrow (Arrow (Tvar 2) (Tvar 1)) (Arrow (Tvar 0) (Tvar 1)))))).

Definition F_add : term :=
  (Fun F_nat
    (Fun F_nat
      (TFun Top (TFun (Tvar 0) (TFun (Tvar 1)
         (Fun (Arrow (Tvar 2) (Tvar 1))
           (Fun (Tvar 0)
              (App (TApp (TApp (TApp (Var 3) (Tvar 2)) (Tvar 1)) (Tvar 1))
                   (App (Var 1)
                        (App (TApp (TApp (TApp (Var 2) (Tvar 2)) (Tvar 1))
                                   (Tvar 0))
                             (App (Var 1) (Var 0)))))))))))).

Eval compute in (compute 100 (App (App F_add F_one) F_one)).

(** Execution is nearly instantaneous.  In Coq 8.1, we can also
use [Eval vm_compute] to request evaluation via compilation to
virtual machine code.  This results in execution speed comparable
to that of bytecoded OCaml.

An alternate execution path is to generate (or ``extract''
in Coq's terminology) Caml code from the Coq definition of function
[compute].  This is achieved by the following command:
*)

Extraction "/tmp/fsub_eval.ml" compute.

(** The generated Caml code can be compiled with the OCaml native-code
compiler for even higher execution speed.  More importantly, it can be
linked with a lexer, parser and printer hand-written in OCaml,
obtaining a stand-alone reference interpreter for $F_{<:}$ that can
execute non-trivial programs. *)

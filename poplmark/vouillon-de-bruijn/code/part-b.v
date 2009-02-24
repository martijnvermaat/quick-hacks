(* PoplMark Challenge, parts 1b and 2b
   By Jerome Vouillon
   March-May 2005
*)

Set Implicit Arguments.
Unset Strict Implicit.

Require Import Arith.
Require Import Omega.


(*************************************************************************)
(*                          Definition of Fsub                           *)
(*************************************************************************)


(*** Standard de Bruijn presentation of Fsub types and terms ***)

Parameter lab : Set.

(* Label comparison is decidable *)
Axiom lab_eq_dec : forall (l l' : lab), {l = l'} + {~ l = l'}.

Inductive typ : Set :=
  | tvar : nat -> typ
  | top : typ
  | arrow : typ -> typ -> typ
  | all : typ -> typ -> typ
  | trecord : trec -> typ

with trec : Set :=
  | tcons : lab -> typ -> trec -> trec
  | tnil : trec.

Scheme typ_induction := Induction for typ Sort Prop
with trec_induction := Induction for trec Sort Prop.

Inductive pat : Set :=
    pvar : typ -> pat
  | precord : prec -> pat

with prec : Set :=
  | pcons : lab -> pat -> prec -> prec
  | pnil : prec.

Inductive term : Set :=
  | var : nat -> term
  | abs : typ -> term -> term
  | app : term -> term -> term
  | tabs : typ -> term -> term
  | tapp : term -> typ -> term
  | record : rec -> term
  | proj : term -> lab -> term
  | tlet : pat -> term -> term -> term

with rec : Set :=
  | rcons : lab -> term -> rec -> rec
  | rnil : rec.

Scheme term_induction := Induction for term Sort Prop
with rec_induction := Induction for rec Sort Prop.

(****)

(*** Record access ****)

Fixpoint trec_get (T : trec) (l : lab) {struct T} : (option typ) :=
  match T with
  | tcons l' T1 T2 => if (lab_eq_dec l l') then Some T1 else trec_get T2 l
  | tnil           => None
  end.

Coercion trec_get : trec >-> Funclass.

Fixpoint rec_get (t : rec) (l : lab) {struct t} : (option term) :=
  match t with
  | rcons l' t1 t2 => if (lab_eq_dec l l') then Some t1 else rec_get t2 l
  | rnil           => None
  end.

Coercion rec_get : rec >-> Funclass.

Fixpoint prec_get (p : prec) (l : lab) {struct p} : (option pat) :=
  match p with
  | pcons l' p1 p2 => if (lab_eq_dec l l') then Some p1 else prec_get p2 l
  | pnil           => None
  end.

Coercion prec_get : prec >-> Funclass.

(****)

(*** Shiftings and substitutions ***)

Fixpoint tshift (X : nat) (T : typ) {struct T} : typ :=
  match T with
  | tvar Y      => tvar (if le_gt_dec X Y then 1 + Y else Y)
  | top         => top
  | arrow T1 T2 => arrow (tshift X T1) (tshift X T2)
  | all T1 T2   => all (tshift X T1) (tshift (1 + X) T2)
  | trecord T1  => trecord (trshift X T1)
  end

with trshift (X : nat) (T : trec) {struct T} : trec :=
  match T with
  | tcons l T1 T2 => tcons l (tshift X T1) (trshift X T2)
  | tnil          => tnil
  end.

(* Applies [f] to [x] one time for each binder crossed in the pattern
   [p].  *)
Fixpoint offset (A : Set) (f : A -> A) (p : pat) (x : A) {struct p} : A :=
  match p with
    pvar _     => f x
  | precord p' => roffset f p' x
  end

with roffset (A : Set) (f : A -> A) (p : prec) (x : A) {struct p} : A :=
  match p with
    pcons _ p1 p2 => roffset f p2 (offset f p1 x)
  | pnil          => x
  end.

Fixpoint shift (x : nat) (t : term) {struct t} : term :=
  match t with
  | var y        => var (if le_gt_dec x y then 1 + y else y)
  | abs T1 t2    => abs T1 (shift (1 + x) t2)
  | app t1 t2    => app (shift x t1) (shift x t2)
  | tabs T1 t2   => tabs T1 (shift x t2)
  | tapp t1 T2   => tapp (shift x t1) T2
  | record t1    => record (rshift x t1)
  | proj t1 l    => proj (shift x t1) l
  | tlet p t1 t2 => tlet p (shift x t1)
                           (shift (offset (fun x => 1 + x) p x) t2)
  end

with rshift (x : nat) (t : rec) {struct t} : rec :=
  match t with
    rcons l t1 t2 => rcons l (shift x t1) (rshift x t2)
  | rnil          => rnil
  end.

Fixpoint pshift_typ (X : nat) (p : pat) {struct p} : pat :=
  match p with
    pvar T     => pvar (tshift X T)
  | precord p' => precord (prshift_typ X p')
  end

with prshift_typ (X : nat) (p : prec) {struct p} : prec :=
  match p with
    pcons l p1 p2 => pcons l (pshift_typ X p1) (prshift_typ X p2)
  | pnil          => pnil
  end.

Fixpoint shift_typ (X : nat) (t : term) {struct t} : term :=
  match t with
  | var y      => var y
  | abs T1 t2  => abs (tshift X T1) (shift_typ X t2)
  | app t1 t2  => app (shift_typ X t1) (shift_typ X t2)
  | tabs T1 t2 => tabs (tshift X T1) (shift_typ (1 + X) t2)
  | tapp t1 T2 => tapp (shift_typ X t1) (tshift X T2)
  | record t1  => record (rshift_typ X t1)
  | proj t1 l    => proj (shift_typ X t1) l
  | tlet p t1 t2 => tlet (pshift_typ X p) (shift_typ X t1) (shift_typ X t2)
  end

with rshift_typ (X : nat) (t : rec) {struct t} : rec :=
  match t with
    rcons l t1 t2 => rcons l (shift_typ X t1) (rshift_typ X t2)
  | rnil          => rnil
  end.

Fixpoint tsubst (T : typ) (X : nat) (T' : typ) {struct T} : typ :=
  match T with
  | tvar Y =>
      match lt_eq_lt_dec Y X with
      | inleft (left _)  => tvar Y
      | inleft (right _) => T'
      | inright _        => tvar (Y - 1)
      end
  | top         => top
  | arrow T1 T2 => arrow (tsubst T1 X T') (tsubst T2 X T')
  | all T1 T2   => all (tsubst T1 X T') (tsubst T2 (1 + X) (tshift 0 T'))
  | trecord T1  => trecord (trsubst T1 X T')
  end

with trsubst (T : trec) (X : nat) (T' : typ) {struct T} : trec :=
  match T with
  | tcons l T1 T2 => tcons l (tsubst T1 X T') (trsubst T2 X T')
  | tnil          => tnil
  end.

Fixpoint subst (t : term) (x : nat) (t' : term) {struct t} : term :=
  match t with
  | var y =>
      match lt_eq_lt_dec y x with
      | inleft (left _)  => var y
      | inleft (right _) => t'
      | inright _        => var (y - 1)
      end
  | abs T1 t2    => abs T1 (subst t2 (1 + x) (shift 0 t'))
  | app t1 t2    => app (subst t1 x t') (subst t2 x t')
  | tabs T1 t2   => tabs T1 (subst t2 x (shift_typ 0 t'))
  | tapp t1 T2   => tapp (subst t1 x t') T2
  | record t1    => record (rsubst t1 x t')
  | proj t1 l    => proj (subst t1 x t') l
  | tlet p t1 t2 => tlet p (subst t1 x t')
                           (subst t2 (offset (fun x => 1 + x) p x)
                                     (offset (shift 0) p t'))
  end

with rsubst (t : rec) (x : nat) (t' : term) {struct t} : rec :=
  match t with
    rcons l t1 t2 => rcons l (subst t1 x t') (rsubst t2 x t')
  | rnil          => rnil
  end.

Fixpoint psubst_typ (p : pat) (X : nat) (T : typ) {struct p} : pat :=
  match p with
    pvar T1    => pvar (tsubst T1 X T)
  | precord p' => precord (prsubst_typ p' X T)
  end

with prsubst_typ (p : prec) (X : nat) (T : typ) {struct p} : prec :=
  match p with
    pcons l p1 p2 => pcons l (psubst_typ p1 X T) (prsubst_typ p2 X T)
  | pnil          => pnil
  end.

Fixpoint subst_typ (t : term) (X : nat) (T : typ) {struct t} : term :=
  match t with
  | var y        => var y
  | abs T1 t2    => abs (tsubst T1 X T) (subst_typ t2 X T)
  | app e1 e2    => app (subst_typ e1 X T) (subst_typ e2 X T)
  | tabs T1 e1   => tabs (tsubst T1 X T) (subst_typ e1 (1 + X) (tshift 0 T))
  | tapp e1 T2   => tapp (subst_typ e1 X T) (tsubst T2 X T)
  | record t1    => record (rsubst_typ t1 X T)
  | proj t1 l    => proj (subst_typ t1 X T) l
  | tlet p t1 t2 => tlet (psubst_typ p X T) (subst_typ t1 X T)
                         (subst_typ t2 X T)
  end

with rsubst_typ (t : rec) (X : nat) (T : typ) {struct t} : rec :=
  match t with
    rcons l t1 t2 => rcons l (subst_typ t1 X T) (rsubst_typ t2 X T)
  | rnil          => rnil
  end.

(****)

(*** Operations on option types ***)

Definition opt_bind (A B : Set) (x : option A) (f : A -> option B) :=
  match x with
  | Some x => f x
  | None   => None
  end.

Definition opt_map (A B : Set) (f : A -> B) (x : option A) :=
  match x with
  | Some x => Some (f x)
  | None   => None
  end.

Lemma opt_bind_some :
  forall (A B : Set) (e : option A) (f : A -> option B) (b : B),
  opt_bind e f = Some b -> exists a, e = Some a /\ f a = Some b.
intros A B e f b E; induction e;
  [ exists a; auto
  | discriminate ].
Qed.

(****)

(*** Contexts ***)

(* We define the contexts [env] and the two functions [get_bound] and
   [get_var] which access the context. *)

Inductive env : Set :=
  | empty : env
  | evar : env -> typ -> env
  | ebound : env -> typ -> env.

Fixpoint get_bound (e : env) (X : nat) {struct e} : option typ :=
  match e with
    empty     => None
  | evar e' _ => get_bound e' X
  | ebound e' T =>
      opt_map (tshift 0)
        (match X with
         | O    => Some T
         | S X' => get_bound e' X'
         end)
  end.

Fixpoint get_var (e : env) (x : nat) {struct e} : option typ :=
  match e with
    empty       => None
  | ebound e' _ => opt_map (tshift 0) (get_var e' x)
  | evar e' T =>
      match x with
      | O    => Some T
      | S x' => get_var e' x'
      end
  end.

(****)

(*** Well-formedness conditions ***)

(* The variables must all be bound *)

Fixpoint wf_typ (e : env) (T : typ) {struct T} : Prop :=
  match T with
  | tvar X      => get_bound e X <> None
  | top         => True
  | arrow T1 T2 => wf_typ e T1 /\ wf_typ e T2
  | all T1 T2   => wf_typ e T1 /\ wf_typ (ebound e T1) T2
  | trecord T1  => wf_trec e T1
  end

with wf_trec (e : env) (t : trec) {struct t} : Prop :=
  match t with
  | tcons l T1 T2 => wf_typ e T1 /\ wf_trec e T2 /\ T2 l = None
  | tnil          => True
  end.

(* This function traverse a pattern checking its well-formedness and
   building an environment extended with the binders of the patterns.
   This environment is then applied to [f]. *)
Fixpoint wf_pat (e : env) (p : pat) (f : env -> Prop) {struct p} : Prop :=
  match p with
    pvar T1    => wf_typ e T1 /\ f (evar e T1)
  | precord p1 => wf_prec e p1 f
  end

with wf_prec (e : env) (p : prec) (f : env -> Prop) {struct p} : Prop :=
  match p with
    pcons l p1 p2 => p2 l = None /\ wf_pat e p1 (fun e => wf_prec e p2 f)
  | pnil          => f e
  end.

Fixpoint wf_term (e : env) (t : term) {struct t} : Prop :=
  match t with
  | var x        => get_var e x <> None
  | abs T1 t2    => wf_typ e T1  /\ wf_term (evar e T1) t2
  | app t1 t2    => wf_term e t1 /\ wf_term e t2
  | tabs T1 t2   => wf_typ e T1  /\ wf_term (ebound e T1) t2
  | tapp t1 T2   => wf_term e t1 /\ wf_typ e T2
  | record t1    => wf_rec e t1
  | proj t1 l    => wf_term e t1
  | tlet p t1 t2 => wf_term e t1 /\ wf_pat e p (fun e => wf_term e t2)
  end

with wf_rec (e : env) (t : rec) {struct t} : Prop :=
  match t with
  | rcons l t1 t2 => wf_term e t1 /\ wf_rec e t2 /\ t2 l = None
  | rnil          => True
  end.

Fixpoint wf_env (e : env) : Prop :=
  match e with
    empty      => True
  | evar e T   => wf_typ e T /\ wf_env e
  | ebound e T => wf_typ e T /\ wf_env e
  end.

(****)

(*** Subtyping relation ***)

(* In the definition of the subtyping and typing relations, we insert
   some well-formedness condition that ensure that all environments,
   types and terms occuring in these relations are well-formed. The
   lemmas [sub_wf] and [typing_wf] show that this is indeed the case.

   We inserted as few well-formedness condition as possible in order
   to reduce the number of time we need to prove that a
   well-formedness condition holds when building a derivation.
*)

Inductive sub : env -> typ -> typ -> Prop :=
  | SA_Top :
      forall (e : env) (S : typ), wf_env e -> wf_typ e S -> sub e S top
  | SA_Refl_TVar :
      forall (e : env) (X : nat),
      wf_env e -> wf_typ e (tvar X) -> sub e (tvar X) (tvar X)
  | SA_Trans_TVar :
      forall (e : env) (X : nat) (T U : typ),
      get_bound e X = Some U -> sub e U T -> sub e (tvar X) T
  | SA_Arrow :
      forall (e : env) (T1 T2 S1 S2 : typ),
      sub e T1 S1 -> sub e S2 T2 -> sub e (arrow S1 S2) (arrow T1 T2)
  | SA_All :
      forall (e : env) (T1 T2 S1 S2 : typ),
      sub e T1 S1 -> sub (ebound e T1) S2 T2 -> sub e (all S1 S2) (all T1 T2)
  | SA_Rcd :
      forall (e : env) (T1 S1 : trec),
      wf_env e -> wf_trec e T1 -> wf_trec e S1 ->
      (forall (l : lab),
       S1 l = None -> T1 l = None) ->
      (forall (l : lab) (S2 T2 : typ),
       T1 l = Some T2 -> S1 l = Some S2 -> sub e S2 T2) ->
      sub e (trecord S1) (trecord T1).

(****)

(*** Typing relation ***)

(* This corresponds to the P-Var and P-Rcd rules except that we extend
   an environment instead of building a piece of environment. *)
Inductive ptyping : env -> pat -> typ -> env -> Prop :=
  | P_Var :
      forall (e : env) (T : typ), ptyping e (pvar T) T (evar e T)
  | P_Rcd :
      forall (e e' : env) (t : prec) (U : trec),
      prtyping e t U e' -> ptyping e (precord t) (trecord U) e'

(* Decomposition of the P-Rcd rule in simpler definitions. *)
with prtyping : env -> prec -> trec -> env -> Prop :=
  | P_Rcd_Cons :
      forall (e1 e2 e3 : env),
      forall (l : lab) (t1 : pat) (t2 : prec) (U1 : typ) (U2 : trec),
      ptyping e1 t1 U1 e2 -> prtyping e2 t2 U2 e3 -> t2 l = None ->
      prtyping e1 (pcons l t1 t2) (tcons l U1 U2) e3
  | P_Rcd_Nil :
      forall (e : env), prtyping e pnil tnil e.

Scheme ptyping_induction := Induction for ptyping Sort Prop
with prtyping_induction := Induction for prtyping Sort Prop.

Inductive typing : env -> term -> typ -> Prop :=
  | T_Var :
      forall (e : env) (x : nat) (T : typ),
      wf_env e -> get_var e x = Some T -> typing e (var x) T
  | T_Abs :
      forall (e : env) (t : term) (T1 T2 : typ),
      typing (evar e T1) t T2 ->
      typing e (abs T1 t) (arrow T1 T2)
  | T_App :
      forall (e : env) (t1 t2 : term) (T11 T12 : typ),
      typing e t1 (arrow T11 T12) ->
      typing e t2 T11 -> typing e (app t1 t2) T12
  | T_Tabs :
      forall (e : env) (t : term) (T1 T2 : typ),
      typing (ebound e T1) t T2 -> typing e (tabs T1 t) (all T1 T2)
  | T_Tapp :
      forall (e : env) (t1 : term) (T11 T12 T2 : typ),
      typing e t1 (all T11 T12) ->
      sub e T2 T11 -> typing e (tapp t1 T2) (tsubst T12 0 T2)
  | T_Sub :
      forall (e : env) (t : term) (T1 T2 : typ),
      typing e t T1 -> sub e T1 T2 -> typing e t T2
  | T_Let :
      forall (e e' : env) (t1 t2 : term) (p : pat) (T1 T2 : typ),
      typing e t1 T1 -> ptyping e p T1 e' -> typing e' t2 T2 ->
      typing e (tlet p t1 t2) T2
  | T_Rcd :
      forall (e : env) (t : rec) (T : trec),
      rtyping e t T -> typing e (record t) (trecord T)
  | T_Proj :
      forall (e : env) (t1 : term) (l : lab) (T1 : trec) (T2 : typ),
      typing e t1 (trecord T1) -> T1 l = Some T2 ->
      typing e (proj t1 l) T2

(* Decomposition of the T-Rcd rule in simpler definitions. *)
with rtyping : env -> rec -> trec -> Prop :=
  | T_Rcd_Cons :
      forall (e : env) (l : lab) (t1 : term) (T1 : typ) (t2 : rec) (T2 : trec),
      typing e t1 T1 -> rtyping e t2 T2 -> t2 l = None -> T2 l = None ->
      rtyping e (rcons l t1 t2) (tcons l T1 T2)
  | T_Rcd_Nil :
      forall (e : env), wf_env e -> rtyping e rnil tnil.

Scheme typing_induction := Induction for typing Sort Prop
with rtyping_induction := Induction for rtyping Sort Prop.

(****)

(*** Reduction rules ***)

Fixpoint value (t : term) : Prop :=
  match t with
  | abs _ _   => True
  | tabs _ _  => True
  | record t1 => rvalue t1
  | _         => False
  end

with rvalue (t : rec) : Prop :=
  match t with
  | rcons _ t1 t2 => value t1 /\ rvalue t2
  | rnil          => True
  end.

Inductive ctx : Set :=
    c_hole : ctx
  | c_appfun : ctx -> term -> ctx
  | c_apparg : forall (t : term), value t -> ctx -> ctx
  | c_typefun : ctx -> typ -> ctx
  | c_proj : ctx -> lab -> ctx
  | c_record : rctx -> ctx
  | c_let : pat -> ctx -> term -> ctx

(* Decomposition of record contexts: either in the current field or in
   a latter field. *)
with rctx : Set :=
    c_here : lab -> ctx -> rec -> rctx
  | c_next : lab -> forall (t : term), value t -> rctx -> rctx.

Scheme ctx_induction := Induction for ctx Sort Prop
with rctx_induction := Induction for rctx Sort Prop.

Fixpoint ctx_app (c : ctx) (t : term) {struct c} : term :=
  match c with
    c_hole           => t
  | c_appfun c' t'   => app (ctx_app c' t) t'
  | c_apparg t' _ c' => app t' (ctx_app c' t)
  | c_typefun c' T   => tapp (ctx_app c' t) T
  | c_proj c' l      => proj (ctx_app c' t) l
  | c_record c'      => record (rctx_app c' t)
  | c_let p c' t'    => tlet p (ctx_app c' t) t'
  end

with rctx_app (c : rctx) (t : term) {struct c} : rec :=
  match c with
    c_here l c' t'   => rcons l (ctx_app c' t) t'
  | c_next l t' _ c' => rcons l t' (rctx_app c' t)
  end.

(* Matching rules match(p,t1)t2, implemented as a function.
   There is one case by rule in the paper definition plus one case for
   failure.
   We maintain the following invariant: the value [t1] lives in the
   environment outside the pattern, while the term [t2] lives in the
   environment containing the pattern bindings.  This is exactly what
   is needed to perform the substitution in rule M-Var.  In order to
   preserve this invariant, the matched value must be shifted when
   crossing part of the pattern (call to the function [offset] is the
   body of tunction [prmatch] below.
*)
Fixpoint pmatch (p : pat) (t1 t2 : term) {struct p} : option term :=
  match p, t1 with
    pvar _,     _         => Some (subst t2 0 t1)
  | precord p1, record r1 => prmatch p1 r1 t2
  | _,          _         => None
  end

(* Decomposition of the M-Rcd rule. *)
with prmatch (p : prec) (r1 : rec) (t2 : term) {struct p} : option term :=
  match p with
    pcons l p1 p2 => opt_bind (prmatch p2 (offset (rshift 0) p1 r1) t2)
                       (fun t2 =>
                     opt_bind (r1 l) (fun t1 =>
                     pmatch p1 t1 t2))
  | pnil          => Some t2
  end.

Inductive red : term -> term -> Prop :=
  | E_AppAbs :
      forall (t11 : typ) (t12 t2 : term),
      value t2 -> red (app (abs t11 t12) t2) (subst t12 0 t2)
  | E_TappTabs :
      forall (t11 t2 : typ) (t12 : term),
      red (tapp (tabs t11 t12) t2) (subst_typ t12 0 t2)
  | E_LetV :
      forall (p : pat) (t1 t2 t: term),
      value t1 -> pmatch p t1 t2 = Some t -> red (tlet p t1 t2) t
  | E_ProjRcd :
      forall (l :lab) (t1 : rec) (t1' : term),
      rvalue t1 -> t1 l = Some t1' -> red (proj (record t1) l) t1'
  | E_Ctx :
      forall (c : ctx) (t1 t1' : term),
      red t1 t1' -> red (ctx_app c t1) (ctx_app c t1').


(*************************************************************************)
(*                            General lemmas                             *)
(*************************************************************************)


(*** Commutation properties of shifting and substitution ***)

Ltac tvar_case :=
  unfold tshift; unfold tsubst; fold tshift; fold tsubst;
  match goal with
  | |- ?x =>
      match x with
      | context [le_gt_dec ?n ?n'] =>
          case (le_gt_dec n n')
      | context C [(lt_eq_lt_dec ?n ?n')] =>
          case (lt_eq_lt_dec n n'); [intro s; case s; clear s | idtac ]
      end
  end.

Ltac common_cases n T :=
  simpl; generalize n; clear n; induction T; intros n''; intros;
    [ repeat tvar_case;
      simpl; trivial; try (intros; apply f_equal with (f := tvar); omega);
      try (intros; assert False; [ omega | contradiction ])
    | trivial
    | simpl; apply f_equal2 with (f := arrow); trivial
    | simpl; apply f_equal2 with (f := all); trivial ].

Ltac common_cases_2 n T P :=
  simpl; generalize n; clear n;
  induction T using typ_induction with (P0 := P); intros n''; intros;
    [ repeat tvar_case;
      simpl; trivial; try (intros; apply f_equal with (f := tvar); omega);
      try (intros; assert False; [ omega | contradiction ])
    | trivial
    | simpl; apply f_equal2 with (f := arrow); trivial
    | simpl; apply f_equal2 with (f := all); trivial
    | simpl; apply f_equal with (f := trecord); trivial
    | simpl; apply (@f_equal2 typ trec trec); trivial
    | trivial ].

Lemma tsubst_tshift_prop :
  forall (n : nat) (T T' : typ), T = tsubst (tshift n T) n T'.
intros n T;
common_cases_2 n T (fun (T : trec) =>
  forall (n : nat) (T' : typ), T = trsubst (trshift n T) n T').
Qed.

Lemma tshift_tshift_prop_1 :
  forall (n n' : nat) (T : typ),
  tshift n (tshift (n + n') T) = tshift (1 + (n + n')) (tshift n T).
intros n n' T;
common_cases_2 n T (fun (T : trec) =>
  forall (n : nat),
  trshift n (trshift (n + n') T) = trshift (S (n + n')) (trshift n T));
exact (IHT2 (S n'')).
Qed.

Lemma tshift_tsubst_prop_1 :
  forall (n n' : nat) (T T' : typ),
  tshift n (tsubst T (n + n') T') =
  tsubst (tshift n T) (1 + n + n') (tshift n T').
intros n n' T;
common_cases_2 n T (fun (T : trec) =>
  forall (n : nat) (T' : typ),
  trshift n (trsubst T (n + n') T') =
  trsubst (trshift n T) (S (n + n')) (tshift n T'));
rewrite (tshift_tshift_prop_1 0 n''); apply (IHT2 (S n'')).
Qed.

Lemma tshift_tsubst_prop_2 :
  forall (n n' : nat) (T T' : typ),
  (tshift (n + n') (tsubst T n T')) =
  (tsubst (tshift (1 + n + n') T) n (tshift (n + n') T')).
intros n n' T;
common_cases_2 n T (fun (T : trec) =>
  forall (n : nat) (T' : typ),
  (trshift (n + n') (trsubst T n T')) =
  (trsubst (trshift (S (n + n')) T) n (tshift (n + n') T')));
rewrite (tshift_tshift_prop_1 0 (n'' + n')); apply (IHT2 (S n'')).
Qed.

Lemma tsubst_tsubst_prop :
  forall (n n' : nat) (T U V : typ),
  (tsubst (tsubst T n U) (n + n') V) =
  (tsubst (tsubst T (1 + n + n') (tshift n V)) n (tsubst U (n + n') V)).
intros n n' T;
common_cases_2 n T (fun (T : trec) =>
  forall (n : nat) (U V : typ),
  (trsubst (trsubst T n U) (n + n') V) =
  (trsubst (trsubst T (S (n + n')) (tshift n V)) n (tsubst U (n + n') V)));
  [ intros; apply tsubst_tshift_prop
  | rewrite (tshift_tsubst_prop_1 0 (n'' + n'));
    rewrite (tshift_tshift_prop_1 0 n'');
    apply (IHT2 (S n'')) ].
Qed.

(****)

(*** Propertis of record access functions ***)

Lemma get_trshift :
  forall (T : trec) (l : lab) (X : nat),
  trshift X T l = opt_map (tshift X) (T l).
induction T; trivial; simpl;
intros l'; case (lab_eq_dec l' l); trivial.
Qed.

Lemma get_trsubst :
  forall (T : trec) (l : lab) (X : nat) (T' : typ),
  trsubst T X T' l = opt_map (fun T => tsubst T X T') (T l).
induction T; trivial; simpl;
intros l'; case (lab_eq_dec l' l); trivial.
Qed.

Lemma get_prshift_typ :
  forall (t : prec) (l : lab) (X : nat),
  prshift_typ X t l = opt_map (pshift_typ X) (t l).
induction t; simpl; trivial; intros l' X; case (lab_eq_dec l' l); trivial.
Qed.

Lemma get_rshift_typ :
  forall (t : rec) (l : lab) (X : nat),
  rshift_typ X t l = opt_map (shift_typ X) (t l).
induction t; simpl; trivial; intros l' X; case (lab_eq_dec l' l); trivial.
Qed.

Lemma get_rshift :
  forall (t : rec) (l : lab) (x : nat),
  rshift x t l = opt_map (shift x) (t l).
induction t; simpl; trivial; intros l' x; case (lab_eq_dec l' l); trivial.
Qed.

Lemma get_rsubst :
  forall (t : rec) (l : lab) (x : nat) (t' : term),
  rsubst t x t' l = opt_map (fun t => subst t x t') (t l).
induction t; simpl; trivial; intros l' x; case (lab_eq_dec l' l); trivial.
Qed.

Lemma get_rsubst_typ :
  forall (t : rec) (l : lab) (X : nat) (T : typ),
  rsubst_typ t X T l = opt_map (fun t => subst_typ t X T) (t l).
induction t; trivial; simpl; intros l'; case (lab_eq_dec l' l); trivial.
Qed.

Lemma get_prsubst_typ :
  forall (t : prec) (l : lab) (X : nat) (T : typ),
  prsubst_typ t X T l = opt_map (fun t => psubst_typ t X T) (t l).
induction t; trivial; simpl; intros l'; case (lab_eq_dec l' l); trivial.
Qed.

(****)

(*** Some properties of the well-formedness conditions *)

Lemma wf_typ_env_weaken :
  forall (T : typ) (e e' : env),
  (forall (X : nat), get_bound e' X = None -> get_bound e X = None) ->
  wf_typ e T -> wf_typ e' T.
induction T using typ_induction with (P0 :=
  fun (T : trec) => forall (e e' : env),
  (forall (X : nat), get_bound e' X = None -> get_bound e X = None) ->
  wf_trec e T -> wf_trec e' T);
simpl; auto; intros e e' H (H1, H2); split;
  [ apply (IHT1 _ _ H H1)
  | apply (IHT2 _ _ H H2)
  | apply (IHT1 _ _ H H1)
  | apply IHT2 with (2 := H2); induction X;
      [ trivial
      | simpl; intro H3; rewrite H; trivial;
        generalize H3; case (get_bound e' X); simpl; trivial;
        intros; discriminate ]
  | apply (IHT _ _ H H1)
  | split;
      [ apply (IHT0 _ _ H (proj1 H2))
      | tauto ] ].
Qed.

Lemma wf_trec_env_weaken :
  forall (T : trec) (e e' : env),
  (forall (X : nat), get_bound e' X = None -> get_bound e X = None) ->
  wf_trec e T -> wf_trec e' T.
induction T; trivial; simpl;
intros e e' H1 (H2, (H3, H4)); repeat split; trivial;
  [ exact (wf_typ_env_weaken H1 H2)
  | exact (IHT _ _ H1 H3) ].
Qed.

Lemma wf_typ_extensionality :
  forall (T : typ) (e e' : env),
  (forall (X : nat), get_bound e X = get_bound e' X) ->
  wf_typ e T -> wf_typ e' T.
intros T e e' H1 H2; apply wf_typ_env_weaken with (2 := H2);
intros n H3; rewrite H1; trivial.
Qed.

Lemma wf_trec_extensionality :
  forall (T : trec) (e e' : env),
  (forall (X : nat), get_bound e X = get_bound e' X) ->
  wf_trec e T -> wf_trec e' T.
intros T e e' H1 H2; apply wf_trec_env_weaken with (2 := H2);
intros n H3; rewrite H1; trivial.
Qed.

(****)

(*** Removal of a term variable binding ***)

(*
   This corresponds to the environment operation
      E, x : T, E'  |-->  E.
*)

Fixpoint remove_var (e : env) (x : nat) {struct e} : env :=
  match e with
  | empty       => empty
  | ebound e' T => ebound (remove_var e' x) T
  | evar e' T =>
      match x with
      | O   => e'
      | S x => evar (remove_var e' x) T
      end
  end.

Lemma get_var_remove_var_lt :
  forall (e : env) (x x' : nat),
  x < x' -> get_var (remove_var e x') x = get_var e x.
induction e; simpl; trivial; intros n n' H;
  [ induction n';
      [ inversion H
      | clear IHn'; induction n; simpl; trivial;
        apply IHe; omega ]
  | apply f_equal with (f := opt_map (tshift 0)); auto ].
Qed.

Lemma get_var_remove_var_ge :
  forall (e : env) (x x' : nat),
  x >= x' -> get_var (remove_var e x') x = get_var e (1 + x).
induction e; simpl; trivial; intros n n' H;
  [ induction n'; trivial;
    clear IHn'; induction n;
      [ inversion H
      | simpl; apply (IHe n); omega ]
  | apply f_equal with (f := opt_map (tshift 0)); apply (IHe n); trivial ].
Qed.

Lemma get_bound_remove_var :
  forall (e : env) (X x': nat), get_bound e X = get_bound (remove_var e x') X.
induction e; simpl; trivial; intros n n';
  [ induction n'; simpl; trivial
  | induction n; trivial;
    apply f_equal with (f := opt_map (tshift 0)); trivial ].
Qed.

Lemma wf_typ_remove_var :
  forall (e : env) (x : nat) (T : typ),
  wf_typ e T -> wf_typ (remove_var e x) T.
intros e n T; apply wf_typ_extensionality;
intro n'; apply get_bound_remove_var.
Qed.

Lemma wf_typ_insert_var :
  forall (e : env) (n : nat) (T : typ),
  wf_typ (remove_var e n) T -> wf_typ e T.
intros e n T; apply wf_typ_extensionality; intro n';
apply sym_eq; apply get_bound_remove_var.
Qed.

Lemma wf_env_remove_var :
  forall (e : env) (x : nat), wf_env e -> wf_env (remove_var e x).
induction e; simpl; trivial;
  [ intros n (H1, H2); induction n; trivial;
    simpl; split; auto; apply wf_typ_remove_var; trivial
  | intros n (H1, H2); split; auto; apply wf_typ_remove_var; trivial ].
Qed.

(****)

(*** Insertion of a type variable binding in an environment ****)

(*
   This corresponds to the environment operation
       E, E'  |-->  E, X <: T, E'.
   Note that all type variable in E' has to be shifted.
*)

Inductive insert_bound : nat -> env -> env -> Prop :=
    ib_here :
      forall (T : typ) (e : env), wf_typ e T -> insert_bound 0 e (ebound e T)
  | ib_var :
      forall (X : nat) (T : typ) (e e' : env),
      insert_bound X e e' ->
      insert_bound X (evar e T) (evar e' (tshift X T))
  | ib_bound :
      forall (X : nat) (T : typ) (e e' : env),
      insert_bound X e e' ->
      insert_bound (1 + X) (ebound e T) (ebound e' (tshift X T)).

Lemma get_bound_insert_bound_ge :
  forall (X X' : nat) (e e' : env),
  insert_bound X' e e' -> X' <= X ->
  get_bound e' (1 + X) = opt_map (tshift X') (get_bound e X).
simpl; intros n n' e e' H; generalize n; clear n; induction H; simpl; trivial;
intros n' H1; induction n'; simpl;
  [ inversion H1
  | clear IHn'; rewrite IHinsert_bound; try omega;
    case (get_bound e n'); simpl; trivial;
    intro T''; apply f_equal with (f := @Some typ);
    apply (tshift_tshift_prop_1 0 X) ].
Qed.

Lemma get_bound_insert_bound_lt :
  forall (X X' : nat) (e e' : env),
  insert_bound X' e e' -> X < X' ->
  get_bound e' X = opt_map (tshift X') (get_bound e X).
intros n n' e e' H; generalize n; clear n; induction H; simpl; trivial;
  [ intros n H1; inversion H1
  | intros n' H1; induction n';
      [ simpl; apply f_equal with (f := @Some typ);
        apply (tshift_tshift_prop_1 0 X)
      | clear IHn'; rewrite IHinsert_bound; try omega;
        case (get_bound e n'); simpl; trivial;
        intro T''; apply f_equal with (f := @Some typ);
        apply (tshift_tshift_prop_1 0 X) ] ].
Qed.

Lemma get_var_insert_bound :
  forall (x X' : nat) (e e' : env),
  insert_bound X' e e' -> get_var e' x = opt_map (tshift X') (get_var e x).
intros n n' e e' H; generalize n; clear n; induction H; simpl; intro n';
  [ trivial
  | induction n'; trivial
  | rewrite IHinsert_bound; case (get_var e n'); simpl; trivial;
    intro T'; apply f_equal with (f := @Some typ);
    apply (tshift_tshift_prop_1 0 X) ].
Qed.

Lemma insert_bound_wf_typ :
  forall (T : typ) (X : nat) (e e' : env),
  insert_bound X e e' -> wf_typ e T -> wf_typ e' (tshift X T).
induction T using typ_induction with (P0 :=
  fun (T : trec) => forall (X : nat) (e e' : env),
  insert_bound X e e' -> wf_trec e T -> wf_trec e' (trshift X T));
trivial;
  [ unfold tshift; fold tshift; intros n' e e' H1 H2; case (le_gt_dec n' n);
      [ intro H3; unfold wf_typ; rewrite (get_bound_insert_bound_ge H1 H3);
        intro H4; apply H2; induction (get_bound e n); trivial; discriminate
      | intro H3; simpl; rewrite (get_bound_insert_bound_lt H1 H3);
        intro H4; apply H2; induction (get_bound e n); trivial; discriminate ]
  | simpl; intros n e e' H1 (H2, H3); eauto
  | simpl; intros n e e' H1 (H2, H3); split;
      [ apply (IHT1 _ _ _ H1 H2)
      | apply IHT2 with (e := (ebound e T1)); trivial;
        exact (ib_bound T1 H1) ]
  | simpl; intros X e e' H1 (H2, (H3, H4)); repeat split;
      [ apply (IHT _ _ _ H1 H2)
      | apply (IHT0 _ _ _ H1 H3)
      | rewrite get_trshift; rewrite H4; trivial ] ].
Qed.

Lemma insert_bound_wf_trec :
  forall (T : trec) (X : nat) (e e' : env),
  insert_bound X e e' -> wf_trec e T -> wf_trec e' (trshift X T).
induction T; trivial; simpl;
intros X e e' H1 (H2, (H3, H4)); repeat split;
  [ exact (insert_bound_wf_typ H1 H2)
  | apply (IHT _ _ _ H1 H3)
  | rewrite get_trshift; rewrite H4; trivial ].
Qed.

Lemma insert_bound_wf_env :
  forall (X : nat) (e e' : env),
  insert_bound X e e' -> wf_env e -> wf_env e'.
intros n e e' H; induction H; simpl; auto;
intros (H1, H2); split; auto; exact (insert_bound_wf_typ H H1).
Qed.

(****)

(*** More properties of the well-formedness conditions *)

Lemma wf_typ_weakening_bound :
  forall (e : env) (T U : typ),
  wf_typ e T -> wf_typ e U -> wf_typ (ebound e U) (tshift 0 T).
intros e T U H1 H2; apply insert_bound_wf_typ with (2 := H1);
apply ib_here; trivial.
Qed.

Lemma wf_typ_weakening_var :
  forall (e : env) (T U : typ),
  wf_typ e U -> wf_typ (evar e T) U.
intros e T U H; apply wf_typ_env_weaken with (2 := H); simpl; trivial.
Qed.

Lemma wf_trec_weakening_var :
  forall (e : env) (T : typ) (U : trec),
  wf_trec e U -> wf_trec (evar e T) U.
intros e T U H; apply wf_trec_env_weaken with (2 := H); simpl; trivial.
Qed.

Lemma wf_typ_strengthening_var :
  forall (e : env) (T U : typ),
  wf_typ (evar e T) U -> wf_typ e U.
intros e T U H; apply wf_typ_env_weaken with (2 := H); simpl; trivial.
Qed.

Lemma wf_typ_ebound :
  forall (T U V : typ) (e : env),
  wf_typ (ebound e U) T -> wf_typ (ebound e V) T.
intros T U V e; apply wf_typ_env_weaken; intro X; induction X;
  [ intros; discriminate
  | trivial ].
Qed.

Lemma get_var_wf :
  forall (e : env) (n : nat) (T : typ),
  wf_env e -> get_var e n = Some T -> wf_typ e T.
induction e; simpl;
  [ intros; discriminate
  | induction n; intros T (H1, H2) E;
      [ injection E; clear E; intro E;
        rewrite <- E; exact (wf_typ_weakening_var t H1)
      | apply wf_typ_weakening_var; eauto ]
  | intros n T (H1, H2) E; assert (H3 := IHe n); clear IHe;
    induction (get_var e n);
      [ simpl in E; injection E; clear E; intro E; rewrite <- E;
        apply wf_typ_weakening_bound with (2 := H1); apply H3 with (1 := H2);
        trivial
      | discriminate ] ].
Qed.

Lemma wf_typ_get :
  forall (e : env) (l : lab) (U : typ) (T : trec),
  wf_trec e T -> T l = Some U -> wf_typ e U.
intros e l U T; induction T;
  [ simpl; intros (H1, (H2, H3)); case (lab_eq_dec l l0); intros E1 E2; auto;
    injection E2; intro E3; rewrite <- E3; trivial
  | intros; discriminate ].
Qed.

Lemma ptyping_wf_trec :
  forall (e1 e2 : env) (p : pat) (T : typ) (U : trec),
  ptyping e1 p T e2 -> wf_trec e1 U -> wf_trec e2 U.
intros e1 e2 p T U H; induction H using ptyping_induction with (P0 :=
  fun e1 p T e2 (H : prtyping e1 p T e2) => wf_trec e1 U -> wf_trec e2 U);
auto;
apply wf_trec_weakening_var.
Qed.


(*************************************************************************)
(*                       Transitivity of subtyping                       *)
(*************************************************************************)


(*** Subtyping relation well-formedness ***)

Lemma sub_wf :
  forall (e : env) (T U : typ),
  sub e T U -> wf_env e /\ wf_typ e T /\ wf_typ e U.
intros e T U H; induction H; repeat split; simpl; trivial; try tauto;
  [ rewrite H; discriminate
  | apply wf_typ_ebound with (U := T1); tauto ].
Qed.

(****)

(*** A.1 Lemma [Reflexivity] ***)

Lemma sub_reflexivity :
  forall (e : env) (T : typ), wf_env e -> wf_typ e T -> sub e T T.
intros e T; generalize e; clear e; induction T using typ_induction with (P0 :=
  fun T => forall (e : env) (l : lab) (T' : typ),
           T l = Some T' -> wf_env e -> wf_typ e T' -> sub e T' T');
intros e;
  [ intros H1 H2; apply SA_Refl_TVar; trivial
  | intros H1 H2; apply SA_Top; trivial
  | intros H1 H2; apply SA_Arrow;
      [ exact (IHT1 _ H1 (proj1 H2))
      | exact (IHT2 _ H1 (proj2 H2)) ]
  | intros H1 H2; apply SA_All;
      [ exact (IHT1 _ H1 (proj1 H2))
      | apply IHT2 with (2 := (proj2 H2)); simpl; simpl in H2; tauto ]
  | intros H1 H2; apply SA_Rcd; trivial;
    intros l S2 T2 E1 E2; rewrite E1 in E2; injection E2;
    intro E3; rewrite <- E3; apply (IHT e) with (1 := E1); trivial;
    exact (wf_typ_get H2 E1)
  | intros l' T'; simpl; case (lab_eq_dec l' l);
      [ intros E1 E2; injection E2; intro E3; rewrite <- E3; auto
      | eauto ]
  | intros; discriminate ].
Qed.

(****)

(*** A.2 Lemma [Permutation and Weakening] ***)
(*** A.5 Lemma [Weakening for Subtyping and Typing] (subtyping part) ***)

(*
   Our proof does not make use of any permutation lemma.
   We only use one-step weakening with a variable inserted anywhere in
   the environment.
   The shifting is needed as a type variable binding is inserted in
   the environment.
*)

Lemma sub_weakening_bound_ind :
  forall (e e' : env) (X : nat) (U V : typ),
  insert_bound X e e' -> sub e U V -> sub e' (tshift X U) (tshift X V).
intros e e' X U V H1 H2; generalize X e' H1; clear X e' H1;
induction H2; intros X' e'; simpl;
  [ intro H1; apply SA_Top;
      [ exact (insert_bound_wf_env H1 H)
      | exact (insert_bound_wf_typ H1 H0) ]
  | intro H1; apply SA_Refl_TVar;
      [ exact (insert_bound_wf_env H1 H)
      | exact (insert_bound_wf_typ H1 H0) ]
  | intro H1; apply SA_Trans_TVar with (2 := (IHsub X' e' H1));
    case (le_gt_dec X' X); intro H3;
      [ change (S X) with (1 + X); trivial;
        rewrite get_bound_insert_bound_ge with (1 := H1) (2 := H3);
        rewrite H; trivial
      | rewrite get_bound_insert_bound_lt with (1 := H1) (2 := H3);
        rewrite H; trivial ]
  | intro H1; apply SA_Arrow; auto
  | intro H1; apply SA_All; auto;
    exact (IHsub2 (1 + X') _ (ib_bound T1 H1))
  | intro H5; apply SA_Rcd;
      [ exact (insert_bound_wf_env H5 H)
      | exact (insert_bound_wf_trec H5 H0)
      | exact (insert_bound_wf_trec H5 H1)
      | intros l E; rewrite get_trshift; rewrite H2; trivial;
        rewrite get_trshift in E; induction (S1 l); trivial; discriminate
      | intros l S2 T2 E1 E2; assert (H6 := H4 l); clear H4;
        rewrite get_trshift in E1; rewrite get_trshift in E2;
        induction (T1 l); try discriminate; injection E1; clear E1; intro E1;
        induction (S1 l); try discriminate; injection E2; clear E2; intro E2;
        rewrite <- E1; rewrite <- E2; apply H6; trivial ] ].
Qed.

Lemma sub_weakening_bound :
  forall (e : env) (T U V : typ),
  wf_typ e V -> sub e T U -> sub (ebound e V) (tshift 0 T) (tshift 0 U).
intros e T U V H0 H; apply sub_weakening_bound_ind with (2 := H);
apply ib_here; trivial.
Qed.

(*
   Rather than proving the weakening property for term variable
   bindings by induction on a derivation on a derivation (as in the
   paper proof), we prove the more general result that the subtyping
   relation does not depend on the term variable bindings.  Then, this
   intermediate result can be used for proving strengthening.
*)

Lemma sub_extensionality :
  forall (e e' : env) (U V : typ),
  (forall (X : nat), (get_bound e X) = (get_bound e' X)) -> wf_env e' ->
  sub e U V -> sub e' U V.
intros e e' U V H0 H1 H2; generalize e' H0 H1; clear e' H0 H1;
induction H2; intros e' H5 H6;
  [ apply SA_Top; trivial; exact (wf_typ_extensionality H5 H0)
  | apply SA_Refl_TVar; trivial; exact (wf_typ_extensionality H5 H0)
  | rewrite H5 in H; apply SA_Trans_TVar with (1 := H); auto
  | apply SA_Arrow; auto
  | apply SA_All; auto;
    apply IHsub2 with (e' := (ebound e' T1));
      [ intro X; induction X; simpl; trivial; rewrite H5; trivial
      | simpl; split; trivial;
        apply wf_typ_extensionality with (1 := H5);
        exact (proj1 (proj2 (sub_wf H2_))) ]
  | apply SA_Rcd; trivial;
      [ exact (wf_trec_extensionality H5 H0)
      | exact (wf_trec_extensionality H5 H1)
      | eauto ] ].
Qed.

Lemma sub_weakening_var_ind :
  forall (e : env) (x : nat) (U V : typ),
  wf_env e -> sub (remove_var e x) U V -> sub e U V.
intros e x U V H1; apply sub_extensionality; trivial;
intro X; apply sym_eq; apply get_bound_remove_var.
Qed.

Lemma sub_weakening_var :
  forall (e : env) (T U V : typ),
  wf_typ e V -> sub e T U -> sub (evar e V) T U.
intros e T U V H1 H2; generalize H2; apply sub_extensionality; trivial;
simpl; split; trivial; exact (proj1 (sub_wf H2)).
Qed.

(****)

(*** Relation "E' is a narrow of E" ***)

(*
   The environments E,X <: Q,E' and E,X<:P,E' are in a narrowing relation
   if E |- P <: Q.
*)

Inductive narrow : nat -> env -> env -> Prop :=
    narrow_0 :
      forall (e : env) (T T' : typ),
      sub e T' T -> narrow 0 (ebound e T) (ebound e T')
  | narrow_extend_bound :
      forall (e e' : env) (T : typ) (X : nat),
      wf_typ e' T -> narrow X e e' ->
      narrow (1 + X) (ebound e T) (ebound e' T)
  | narrow_extend_var :
      forall (e e' : env) (T : typ) (X : nat),
      wf_typ e' T -> narrow X e e' -> narrow X (evar e T) (evar e' T).

Lemma get_bound_narrow_ne :
  forall (X X' : nat) (e e' : env),
  narrow X e e' -> X' <> X -> get_bound e X' = get_bound e' X'.
intros n n' e e' H; generalize n'; clear n'; induction H; intros n' H1; simpl;
  [ induction n'; trivial; case H1; trivial
  | induction n'; trivial; rewrite IHnarrow; trivial; omega
  | auto ].
Qed.

Lemma get_bound_narrow_eq :
  forall (X : nat) (e e' : env),
  narrow X e e' ->
  exists T, exists T',
  get_bound e X = Some T /\ get_bound e' X = Some T' /\ sub e' T' T.
intros n e e' H; induction H;
  [ exists (tshift 0 T); exists (tshift 0 T'); repeat split;
    apply sub_weakening_bound; trivial; exact (proj1 (proj2 (sub_wf H)))
  | generalize IHnarrow; intros (Q, (P, (H1, (H2, H3))));
    exists (tshift 0 Q); exists (tshift 0 P); simpl; repeat split;
      [ rewrite H1; trivial
      | rewrite H2; trivial
      | apply sub_weakening_bound; trivial ]
  | generalize IHnarrow; intros (Q, (P, (H1, (H2, H3))));
    exists Q; exists P; repeat split; trivial;
    apply sub_weakening_var; trivial ].
Qed.

Lemma get_var_narrow :
  forall (X x' : nat) (e e' : env),
  narrow X e e' -> get_var e x' = get_var e' x'.
intros n n' e e' H; generalize n'; clear n'; induction H;
  [ trivial
  | simpl; intros n'; rewrite IHnarrow; trivial
  | simpl; induction n'; trivial ].
Qed.

Lemma narrow_wf_typ :
  forall (e e' : env) (T : typ) (X : nat),
  narrow X e e' -> wf_typ e T -> wf_typ e' T.
intros e e' T n H1 H2;
apply wf_typ_env_weaken with (2 := H2); intros n' H3;
case (eq_nat_dec n' n);
  [ intros E; rewrite E in H3;
    generalize (get_bound_narrow_eq H1);
    intros (Q, (P, (H4, (H5, H6)))); rewrite H5 in H3; discriminate
  | intro H4; rewrite (get_bound_narrow_ne H1 H4); trivial ].
Qed.

Lemma narrow_wf_trec :
  forall (e e' : env) (T : trec) (X : nat),
  narrow X e e' -> wf_trec e T -> wf_trec e' T.
intros e e' T n H1 H2;
apply wf_trec_env_weaken with (2 := H2); intros n' H3;
case (eq_nat_dec n' n);
  [ intros E; rewrite E in H3;
    generalize (get_bound_narrow_eq H1);
    intros (Q, (P, (H4, (H5, H6)))); rewrite H5 in H3; discriminate
  | intro H4; rewrite (get_bound_narrow_ne H1 H4); trivial ].
Qed.

Lemma narrow_wf_env :
  forall (e e' : env) (X : nat),
  narrow X e e' -> wf_env e -> wf_env e'.
intros e e' n H; induction H; simpl;
intros (H1, H2); split; auto;
exact (proj1 (proj2 (sub_wf H))).
Qed.

(****)

(* A.3 Lemma [Transitivity and Narrowing] *)

(* The statements of the properties of transitivity and narrowing
   (we give the *statement* here and the *proof* below) *)

Definition transitivity_prop (Q : typ) :=
  forall (e : env) (S T : typ), sub e S Q -> sub e Q T -> sub e S T.

Definition narrowing_prop (Q : typ) :=
  forall (e e' : env) (X : nat) (S T : typ),
  narrow X e e' -> get_bound e X = Some Q ->
  sub e S T -> sub e' S T.

(* The proof follows closely the paper proof.  However, we cannot
   perform a proof on the distinguished type [Q] as the induction in
   the paper proof is on [Q] *up to alpha conversion* (shifting).
   Instead, we perform a proof by induction on the size of types. *)

Fixpoint size (T : typ) : nat :=
  match T with
  | tvar _      => 0
  | top         => 0
  | arrow T1 T2 => 1 + size T1 + size T2
  | all T1 T2   => 1 + size T1 + size T2
  | trecord T1  => rsize T1
  end

with rsize (T : trec) : nat :=
  match T with
  | tcons _ T1 T2 => 1 + size T1 + rsize T2
  | tnil          => 0
  end.

Lemma shift_preserves_size :
 forall (T : typ) (X : nat), size (tshift X T) = size T.
induction T using typ_induction with (P0 :=
  fun (T : trec) => forall (X : nat), rsize (trshift X T) = rsize T);
trivial; simpl; intros X;
  [ rewrite IHT1; rewrite IHT2; trivial
  | rewrite IHT1; rewrite IHT2; trivial
  | rewrite IHT; rewrite IHT0; trivial ].
Qed.

Lemma field_size :
  forall (l : lab) (U : typ) (T : trec), T l = Some U -> size U < rsize T.
intros l U T; induction T;
  [ simpl; case (lab_eq_dec l l0);
      [ intros E1 E2; injection E2; intro E; rewrite E; omega
      | intros H1 E; assert (H2 := IHT E); omega ]
  | intros; discriminate ].
Qed.

(* Now we give the crucial step in the proof of transitivity, showing
   that transitivity holds if we assume that both transitivity and
   narrowing hold for smaller "cut types" q' *)

Lemma transitivity_case :
  forall Q : typ,
  (forall Q' : typ,
   size Q' < size Q -> transitivity_prop Q' /\ narrowing_prop Q') ->
  transitivity_prop Q.
intros Q H e S T H1 H2; induction H1;
  [ inversion_clear H2; apply SA_Top; trivial
  | trivial
  | exact (SA_Trans_TVar H0 (IHsub H H2))
  | inversion_clear H2;
      [ apply SA_Top; trivial;
        simpl; split;
          [ apply (proj2 (proj2 (sub_wf H1_)))
          | apply (proj1 (proj2 (sub_wf H1_0))) ]
      | apply SA_Arrow;
          [ assert (H5 : size T1 < size (arrow T1 T2)); try (simpl; omega);
            generalize (H _ H5); intros (H6, _); exact (H6 _ _ _ H0 H1_)
          | assert (H5 : size T2 < size (arrow T1 T2)); try (simpl; omega);
            generalize (H _ H5); intros (H6, _);
            exact (H6 _ _ _ H1_0 H1) ] ]
  | inversion_clear H2;
      [ apply SA_Top; trivial;
        simpl; split;
          [ apply (proj2 (proj2 (sub_wf H1_)))
          | apply wf_typ_ebound with (U := T1);
            apply (proj1 (proj2 (sub_wf H1_0))) ]
      | assert (H5 : size T1 < size (all T1 T2)); try (simpl; omega);
        apply SA_All;
          [ generalize (H _ H5); intros (H6, _); exact (H6 _ _ _ H0 H1_)
          | assert (H5' : size (tshift 0 T1) < size (all T1 T2));
              [ rewrite shift_preserves_size; trivial
              | generalize (H _ H5'); intros (_, H6);
                assert (H7 := narrow_0 H0);
                assert
                  (H7' : get_bound (ebound e T1) 0 = Some (tshift 0 T1));
                  [ trivial
                  | assert (H8 := H6 _ _ _ _ _ H7 H7' H1_0);
                    assert (H9 : size T2 < size (all T1 T2));
                    try (simpl; omega);
                    assert (G1 := proj1 (H _ H9));
                    exact (G1 (ebound e T0) _ _ H8 H1) ] ] ] ]
  | inversion_clear H2;
      [ apply SA_Top; trivial
      | apply SA_Rcd; auto;
        intros l S2 T2 E1 E2; cut (exists U2, T1 l = Some U2);
          [ intros (U2, E3);
            apply (proj1 (H _ (field_size E3))); eauto
          | assert (G1 := H10 l); induction (T1 l);
              [ exists a; trivial
              | rewrite G1 in E1; trivial; discriminate ] ] ] ].
Qed.

(* Next we give the crucial step in the proof of narrowing, showing
   that narrowing for q holds if we assume transitivity for types of
   the same size as q.  (Not "for q itself" because there is some
   shifting involved.) *)

Lemma narrowing_case :
  forall Q : typ,
  (forall Q' : typ, size Q' = size Q -> transitivity_prop Q') ->
  narrowing_prop Q.
intros Q H2 e e' n T1 T2 H3 H4 H5; generalize e' n H3 H4; clear e' n H3 H4;
generalize Q H2; clear Q H2; induction H5;
  [ intros Q H2 e' n H3 H4; apply SA_Top;
      [ exact (narrow_wf_env H3 H)
      | exact (narrow_wf_typ H3 H0) ]
  | intros Q H2 e' n H3 H4; apply SA_Refl_TVar;
      [ exact (narrow_wf_env H3 H)
      | exact (narrow_wf_typ H3 H0) ]
  | intros Q H2 e' n H3 H4; case (eq_nat_dec X n);
      [ intro E; rewrite E in H; rewrite E; clear X E;
        assert (H4' := IHsub _ H2 _ _ H3 H4);
        rewrite H in H4; injection H4; intro E; rewrite E in H4';
        apply (H2 _ (refl_equal (size Q))) with (2 := H4');
        rewrite <- E;
        generalize (get_bound_narrow_eq H3);
        intros (T1, (T2, (H6, (H7, H8))));
        rewrite H in H6; injection H6;
        intro E1; rewrite <- E1 in H8;
        apply SA_Trans_TVar with (2 := H8); trivial
      | intro H6; apply SA_Trans_TVar with (2 := IHsub _ H2 _ _ H3 H4);
        rewrite <- (get_bound_narrow_ne H3 H6); trivial ]
  | intros Q H2 e' n H3 H4; apply SA_Arrow; eauto
  | intros Q H2 e' n H3 H4; apply SA_All;
     [ eauto
     | apply IHsub2 with (Q := tshift 0 Q) (n := (1 + n));
         [ intros Q' E; apply H2; rewrite E; apply shift_preserves_size
         | apply narrow_extend_bound with (2 := H3);
           apply narrow_wf_typ with (1 := H3);
           exact (proj1 (proj2 (sub_wf H5_)))
         | simpl; rewrite H4; trivial ] ]
  | intros Q H5 e' n H6 E1; apply SA_Rcd; eauto;
      [ exact (narrow_wf_env H6 H)
      | exact (narrow_wf_trec H6 H0)
      | exact (narrow_wf_trec H6 H1) ] ].
Qed.

(* Now we combine the above lemmas into the full proof of transitivity
   and narrowing, by induction on the size of q.  (Note that this
   departs slightly from the paper proof, which was by structural
   induction on q.) *)

Lemma transitivity_and_narrowing :
 forall Q : typ, transitivity_prop Q /\ narrowing_prop Q.
assert
 (H :
  forall (n : nat) (Q : typ),
  size Q < n -> transitivity_prop Q /\ narrowing_prop Q);
 [ induction n;
    [ intros Q H; assert False; [ omega | contradiction ]
    | intros Q H; case (le_lt_or_eq _ _ H);
       [ intro H'; apply IHn; omega
       | intro E; injection E; clear E; intro E; rewrite <- E in IHn;
          assert
           (H1 : forall Q' : typ, size Q' = size Q -> transitivity_prop Q');
          [ intros Q' E1; rewrite <- E1 in IHn; apply transitivity_case;
             trivial
          | split; [ apply H1; trivial | apply narrowing_case; trivial ] ] ] ]
 | intro Q; apply (H (S (size Q))); omega ].
Qed.

Lemma sub_transitivity :
  forall (e : env) (T U V : typ), sub e T U -> sub e U V -> sub e T V.
intros e T U; apply (proj1 (transitivity_and_narrowing U)).
Qed.

Lemma sub_narrowing :
  forall (e e' : env) (X : nat) (S T : typ),
  narrow X e e' -> sub e S T -> sub e' S T.
intros e e' n S T H1 H2;
generalize (get_bound_narrow_eq H1); intros (Q, (P, (H3, _)));
exact (proj2 (transitivity_and_narrowing Q) _ _ _ _ _ H1 H3 H2).
Qed.


(*************************************************************************)
(*                              Type safety                              *)
(*************************************************************************)


(*** Substitution of a type variable in an environment ****)

(*
   This corresponds to the environment operation
      E, X <: T, E'  |-->  E, [X|->T']E',
   assuming that E |- T' <: T.
   (see definition A.9)
*)

Inductive env_subst : nat -> typ -> env -> env -> Prop :=
    es_here :
      forall (e : env) (T T' : typ),
      sub e T' T -> env_subst 0 T' (ebound e T) e
  | es_var :
      forall (X : nat) (T T' : typ) (e e' : env),
      env_subst X T' e e' ->
      env_subst X T' (evar e T) (evar e' (tsubst T X T'))
  | es_bound :
      forall (X : nat) (T T' : typ) (e e' : env),
      env_subst X T' e e' ->
      env_subst (1 + X) (tshift 0 T') (ebound e T) (ebound e' (tsubst T X T')).

Lemma env_subst_get_var :
  forall (x X' : nat) (e e' : env) (T : typ),
  (env_subst  X' T e e') ->
  get_var e' x = opt_map (fun T' => tsubst T' X' T) (get_var e x).
intros n n' e e' T H; generalize n; clear n; induction H;
  [ intro n; simpl; induction (get_var e n); simpl; trivial;
    apply f_equal with (f := @Some typ); apply tsubst_tshift_prop
  | intro n'; induction n'; simpl; trivial
  | simpl; intro n'; rewrite IHenv_subst;
    induction (get_var e n'); simpl; trivial;
    apply f_equal with (f := @Some typ);
    apply (tshift_tsubst_prop_1 0 X) ].
Qed.

Lemma env_subst_get_bound_lt :
  forall (X X' : nat) (e e' : env) (T : typ),
  (env_subst X' T e e') -> X < X' ->
  get_bound e' X = opt_map (fun T' => tsubst T' X' T) (get_bound e X).
intros n n' e e' T H; generalize n; clear n;
induction H; simpl; trivial; intros n' H1;
  [ inversion H1
  | induction n';
      [ simpl; apply f_equal with (f := @Some typ);
        apply (tshift_tsubst_prop_1 0 X)
      | clear IHn'; rewrite IHenv_subst;
          [ case (get_bound e n'); simpl; trivial; intro T'';
            apply f_equal with (f := @Some typ);
            apply (tshift_tsubst_prop_1 0 X)
          | omega ] ] ].
Qed.

Lemma env_subst_get_bound_ge :
  forall (X X' : nat) (e e' : env) (T : typ),
  env_subst X' T e e' -> X' < X ->
  get_bound e' (X - 1) = opt_map (fun T' => tsubst T' X' T) (get_bound e X).
intros n n' e e' T H; generalize n; clear n;
induction H; simpl; trivial; intros n' H1;
  [ induction n';
      [ inversion H1
      | simpl; rewrite <- minus_n_O; case (get_bound e n'); simpl; trivial;
        intro T''; apply f_equal with (f := @Some typ);
        apply tsubst_tshift_prop ]
  | induction n';
      [ inversion H1
      | clear IHn'; replace ((S n') - 1) with (S (n' - 1)); try omega;
        rewrite IHenv_subst; try omega;
        case (get_bound e n'); simpl; trivial; intro T'';
        apply f_equal with (f := @Some typ);
        apply (tshift_tsubst_prop_1 0 X) ] ].
Qed.

Lemma env_subst_wf_typ_0 :
  forall (e e' : env) (T : typ) (X : nat),
  env_subst X T e e' -> wf_env e' -> wf_typ e' T.
intros e e' T X H; induction H; simpl;
  [ intros _; exact (proj1 (proj2 (sub_wf H)))
  | intros (H1, H2); apply wf_typ_weakening_var; auto
  | intros (H1, H2); apply wf_typ_weakening_bound; auto ].
Qed.

Lemma env_subst_wf_typ :
  forall (e e' : env) (S T : typ) (X : nat),
  env_subst X T e e' -> wf_typ e S -> wf_env e' -> wf_typ e' (tsubst S X T).
intros e e' S; generalize e e'; clear e e';
induction S using typ_induction with (P0 :=
  fun S => forall (e e' : env) (T : typ) (X : nat),
  env_subst X T e e' -> wf_trec e S -> wf_env e' ->
  wf_trec e' (trsubst S X T)); trivial; simpl; intros e e' T X H1;
  [ intros H2 H3; simpl in H2; case (lt_eq_lt_dec n X);
      [ intro s; case s; clear s; intro H5;
          [ simpl; rewrite env_subst_get_bound_lt with (1 := H1) (2 := H5);
            induction (get_bound e n); trivial; discriminate
          | exact (env_subst_wf_typ_0 H1 H3) ]
      | intro H5; simpl;
        rewrite env_subst_get_bound_ge with (1 := H1) (2 := H5);
        induction (get_bound e n); trivial; discriminate ]
  | intros (H2, H3) H4; eauto
  | intros (H2, H3) H4; split; eauto;
    apply IHS2 with (e := (ebound e S1)); trivial;
      [ exact (es_bound S1 H1)
      | simpl; split; trivial; apply IHS1 with (1 := H1); trivial ]
  | intros (H2, (H3, H4)) H5; repeat split; eauto;
    rewrite get_trsubst; rewrite H4; trivial ].
Qed.

Lemma env_subst_wf_trec :
  forall (e e' : env) (S : trec) (T : typ) (X : nat),
  env_subst X T e e' -> wf_trec e S -> wf_env e' -> wf_trec e' (trsubst S X T).
intros e e' S; generalize e e'; clear e e';
induction S; auto; simpl;
intros e e' T X H1 (H2, (H3, H4)) H5; repeat split; eauto;
  [ exact (env_subst_wf_typ H1 H2 H5)
  | rewrite get_trsubst; rewrite H4; trivial ].
Qed.

Lemma env_subst_wf_env :
  forall (e e' : env) (T : typ) (X : nat),
  env_subst X T e e' -> wf_env e -> wf_env e'.
intros e e' T X H; induction H; simpl; try tauto;
intros (H1, H2); split; auto;
apply env_subst_wf_typ with (1 := H); auto.
Qed.

(****)

(*** Typing relation well-formedness ***)

Lemma ptyping_wf :
  forall (e e' : env) (T1 T2 : typ) (p : pat) (P : env -> Prop),
  ptyping e p T1 e' -> wf_env e' -> P e' -> wf_typ e' T2 ->
  wf_env e /\ wf_pat e p P /\ wf_typ e T2.
intros e e' T1 T2 p P H; generalize P; clear P;
induction H using ptyping_induction with (P0 :=
  fun e p T1 e' (H : prtyping e p T1 e') =>
  forall (P : env -> Prop), wf_env e' -> P e' -> wf_typ e' T2 ->
  wf_env e /\ wf_prec e p P /\ wf_typ e T2); simpl;
  [ intros P (H1, H2) H3 H4; repeat split; trivial;
    exact (wf_typ_strengthening_var H4)
  | auto
  | intros P H1 H2 H3;
    generalize (IHptyping0 _ H1 H2 H3); intros (H4, (H5, H6));
    generalize (IHptyping (fun e => wf_prec e t2 P) H4 H5 H6);
    intros (G1, (G2, G3)); auto
  | auto ].
Qed.

Lemma typing_wf :
  forall (e : env) (t : term) (U : typ),
  typing e t U -> wf_env e /\ wf_term e t /\ wf_typ e U.
intros e t U H; induction H using typing_induction with (P0 :=
  fun (e : env) (r : rec) (t : trec) (H : rtyping e r t) =>
  wf_env e /\ wf_rec e r /\ wf_trec e t);
  [ repeat split; simpl; trivial;
      [ simpl; rewrite e0; discriminate
      | exact (get_var_wf w e0) ]
  | simpl in IHtyping; simpl; repeat split; try tauto;
    apply wf_typ_strengthening_var with (T := T1); tauto
  | simpl; simpl in IHtyping1; tauto
  | simpl; simpl in IHtyping; tauto
  | simpl; simpl in IHtyping; assert (H1 := proj1 (proj2 (sub_wf s)));
    repeat split; try tauto;
    apply env_subst_wf_typ with (1 := es_here s); tauto
  | repeat split; try tauto; exact (proj2 (proj2 (sub_wf s)))
  | simpl; generalize IHtyping2; intros (H1, (H2, H3));
    generalize (ptyping_wf (P := fun e' => wf_term e' t2) p0 H1 H2 H3);
    intros (H4, (H5, H6)); tauto
  | trivial
  | simpl; simpl in IHtyping; repeat split; try tauto;
    apply wf_typ_get with (2 := e0); tauto
  | simpl; tauto
  | simpl; auto ].
Qed.

(****)

(*** A.4 Lemma [Permutation for Typing] ***)

(* We don't need any permutation lemma. *)

(****)

(*** A.5 Lemma [Weakening for typing] (typing part) ***)

Lemma ptyping_weakening_bound_ind :
  forall (e1 e1' e2 : env) (X : nat) (p : pat) (T : typ),
  insert_bound X e1 e1' ->
  ptyping e1 p T e2 ->
  exists e2', insert_bound X e2 e2' /\
              ptyping e1' (pshift_typ X p) (tshift X T) e2'.
intros e1 e1' e2 X p T H1 H2; generalize e1' H1; clear e1' H1;
induction H2 using ptyping_induction with (P0 :=
  fun e1 p T e2 (H : prtyping e1 p T e2) =>
  forall (e1' : env), insert_bound X e1 e1' ->
  exists e2', insert_bound X e2 e2' /\
              prtyping e1' (prshift_typ X p) (trshift X T) e2');
  [ intros e1' H1; exists (evar e1' (tshift X T)); split;
      [ exact (ib_var T H1)
      | simpl; apply P_Var ]
  | intros e1' H1; generalize (IHptyping _ H1); intros (e2', (H2, H3));
    exists e2'; split; trivial;
    simpl; apply P_Rcd; trivial
  | intros e1' H1; generalize (IHptyping _ H1); intros (e2', (H3, H4));
    generalize (IHptyping0 _ H3); intros (e3', (H5, H6));
    exists e3'; split; trivial;
    simpl; apply (P_Rcd_Cons (l := l) H4 H6);
    rewrite get_prshift_typ; rewrite e; trivial
  | intros e1' H1; exists e1'; split; trivial;
    simpl; apply P_Rcd_Nil ].
Qed.

Lemma typing_weakening_bound_ind :
  forall (e e' : env) (X : nat) (t : term) (U : typ),
  insert_bound X e e' ->
  typing e t U -> typing e' (shift_typ X t) (tshift X U).
intros e e' n t U H1 H2; generalize n e' H1; clear n e' H1;
induction H2 using typing_induction with (P0 :=
  fun e t U (H : rtyping e t U) => forall (X : nat) (e' : env),
  insert_bound X e e' -> rtyping e' (rshift_typ X t) (trshift X U)); simpl;
  [ intros n1 e' H1; apply T_Var;
      [ exact (insert_bound_wf_env H1 w)
      | rewrite get_var_insert_bound with (1 := H1); rewrite e0; trivial ]
  | intros n1 e' H1; apply T_Abs; apply IHtyping; apply ib_var; trivial
  | intros n1 e' H1;
    assert (H2 := (IHtyping1 _ _ H1)); assert (H3 := (IHtyping2 _ _ H1));
    exact (T_App H2 H3)
  | intros n1 e' H1; apply T_Tabs; apply IHtyping; exact (ib_bound T1 H1)
  | intros n1 e' H1; rewrite (tshift_tsubst_prop_2 0 n1);
    apply (T_Tapp (IHtyping _ _ H1) (sub_weakening_bound_ind H1 s))
  | intros n1 e' H1;
    exact (T_Sub (IHtyping _ _ H1) (sub_weakening_bound_ind H1 s))
  | intros X e1 H1; generalize (ptyping_weakening_bound_ind H1 p0);
    intros (e2', (H2, H3));
     exact (T_Let (IHtyping1 _ _ H1) H3 (IHtyping2 _ _ H2))
  | intros n1 e' H1; apply T_Rcd; auto
  | intros n1 e' H1; apply T_Proj with (T1 := trshift n1 T1);
      [ exact (IHtyping _ _ H1)
      | rewrite get_trshift; rewrite e0; trivial ]
  | intros X e' H1; apply T_Rcd_Cons; auto;
      [ rewrite get_rshift_typ; rewrite e0; trivial
      | rewrite get_trshift; rewrite e1; trivial ]
  | intros X e' H1; apply T_Rcd_Nil; exact (insert_bound_wf_env H1 w) ].
Qed.

Lemma typing_weakening_bound :
  forall (e : env) (t : term) (U V : typ),
  wf_typ e V -> typing e t U ->
  typing (ebound e V) (shift_typ 0 t) (tshift 0 U).
intros e t U V H1 H2; apply typing_weakening_bound_ind with (2 := H2);
apply ib_here; trivial.
Qed.

Lemma ptyping_weakening_var_ind :
  forall (e1 e2 e1' : env) (p : pat) (x : nat) (T : typ),
  ptyping e1 p T e2 -> e1 = remove_var e1' x -> wf_env e1' -> wf_typ e1' T ->
  exists e2', ptyping e1' p T e2' /\
              e2 = remove_var e2' (offset (fun x => 1 + x) p x) /\
              wf_env e2'.
intros e1 e2 e1' p n T H1; generalize e1' n; clear e1' n;
induction H1 using ptyping_induction with (P0 :=
  fun e1 p T e2 (H : prtyping e1 p T e2) => forall (e1' : env) (n : nat),
  e1 = remove_var e1' n -> wf_env e1' -> wf_trec e1' T ->
  exists e2' : env, prtyping e1' p T e2' /\
                    e2 = remove_var e2' (roffset (fun x => 1 + x) p n) /\
                    wf_env e2');
  [ intros e1' n H1 H2 H3; exists (evar e1' T); repeat split; trivial;
      [ apply P_Var
      | simpl; rewrite H1; trivial ]
  | intros e1' n H1 H2 H3; generalize (IHptyping _ _ H1 H2 H3);
    intros (e2', (H4, (H5, H6))); exists e2'; repeat split; trivial;
    apply P_Rcd; trivial
  | simpl; intros e1' n H2 H3 (H4, (H4', H4''));
    generalize (IHptyping _ _ H2 H3 H4); intros (e2', (H5, (H6, H7)));
    generalize (IHptyping0 _ _ H6 H7 (ptyping_wf_trec H5 H4'));
    intros (e3', (H8, (H9, H10))); clear IHptyping IHptyping0;
    exists e3'; repeat split; trivial;
    exact (P_Rcd_Cons H5 H8 e)
  | intros e1' n H1 H2 H3; exists e1'; repeat split; trivial;
    apply P_Rcd_Nil ].
Qed.

Lemma typing_weakening_var_ind :
  forall (e : env) (x : nat) (t : term) (U : typ),
  wf_env e -> typing (remove_var e x) t U -> typing e (shift x t) U.
intros e n t U H1 H2; cut (exists e', e' = remove_var e n);
  [ intros (e', E); rewrite <- E in H2; generalize n e E H1; clear n e E H1;
    induction H2 using typing_induction with (P0 :=
      fun e' t U (H : rtyping e' t U) => forall (n : nat) (e : env),
      e' = remove_var e n -> wf_env e -> rtyping e (rshift n t) U); simpl;
      [ intros n' e' E H1; apply T_Var; trivial; rewrite E in e0;
        case (le_gt_dec n' x); intro H2;
          [ rewrite get_var_remove_var_ge in e0; trivial; omega
          | rewrite get_var_remove_var_lt in e0; trivial; omega ]
      | intros n' e' E H1; apply T_Abs; apply IHtyping;
          [ rewrite E; trivial
          | simpl; split; trivial;
            assert (H3 := proj1 (proj1 (typing_wf H2))); rewrite E in H3;
            exact (wf_typ_insert_var H3) ]
      | intros n' e' E H1;
        exact (T_App (IHtyping1 _ _ E H1) (IHtyping2 _ _ E H1))
      | intros n' e' E H1; apply T_Tabs; apply IHtyping;
          [ rewrite E; trivial
          | simpl; split; trivial;
            assert (H3 := proj1 (proj1 (typing_wf H2))); rewrite E in H3;
            exact (wf_typ_insert_var H3) ]
      | intros n' e' E H1; apply (T_Tapp (T2 := T2) (IHtyping _ _ E H1));
        rewrite E in s; exact (sub_weakening_var_ind H1 s)
      | intros n' e' E H1; apply (T_Sub (T2 := T2) (IHtyping _ _ E H1));
        rewrite E in s; exact (sub_weakening_var_ind H1 s)
      | intros n e1 E H1; assert (H2 : wf_typ e1 T1);
          [ assert (H2 := proj2 (proj2 (typing_wf H2_))); rewrite E in H2;
            exact (wf_typ_insert_var H2)
          | generalize (ptyping_weakening_var_ind p0 E H1 H2);
            intros (e2', (H3, (H4, H5)));
            exact (T_Let (IHtyping1 _ _ E H1) H3 (IHtyping2 _ _ H4 H5)) ]
      | intros n e' E H1; apply T_Rcd; auto
      | intros n e' E H1; apply T_Proj with (2 := e0);
        exact (IHtyping _ _ E H1)
      | intros n e' E H1; apply T_Rcd_Cons; auto;
        rewrite get_rshift; rewrite e0; trivial
      | intros n e' E H1; apply T_Rcd_Nil; trivial ]
  | exists (remove_var e n); trivial ].
Qed.

Lemma typing_weakening_var :
  forall (e : env) (t : term) (U V : typ),
  wf_typ e V -> typing e t U -> typing (evar e V) (shift 0 t) U.
intros e t U V H1 H2; apply (@typing_weakening_var_ind (evar e V));
simpl; trivial; split; trivial; exact (proj1 (typing_wf H2)).
Qed.

(****)

(*** A.6 Lemma [Strengthening] ***)

Lemma sub_strengthening_var :
  forall (e : env) (x : nat) (U V : typ),
  sub e U V -> sub (remove_var e x) U V.
intros e x U V H1; generalize H1; apply sub_extensionality;
  [ intro X; apply get_bound_remove_var
  | apply wf_env_remove_var; exact (proj1 (sub_wf H1)) ].
Qed.

(****)

(*** A.7 Lemma [Narrowing for the Typing Relation] ***)

Lemma ptyping_narrowing_ind :
  forall (e1 e2 e1' : env) (p : pat) (X : nat) (T : typ),
  ptyping e1 p T e2 -> narrow X e1 e1' -> wf_typ e1' T ->
  exists e2', ptyping e1' p T e2' /\ narrow X e2 e2'.
intros e1 e2 e1' p X T H1; generalize e1' X; clear e1' X;
induction H1 using ptyping_induction with (P0 :=
  fun e1 p T e2 (H : prtyping e1 p T e2) => forall (e1' : env) (X : nat),
   narrow X e1 e1' -> wf_trec e1' T ->
   exists e2' : env, prtyping e1' p T e2' /\ narrow X e2 e2');
  [ intros e1' X H1; exists (evar e1' T); split;
      [ apply P_Var
      | apply narrow_extend_var; trivial ]
  | intros e1' X H1 H2; generalize (IHptyping _ _ H1 H2);
    intros (e2', (H3, H4)); exists e2'; split; trivial;
    apply P_Rcd; trivial
  | simpl; intros e1' X H2 (H3, (H4, H5));
    generalize (IHptyping _ _ H2 H3); intros (e2', (H6, H7));
    generalize (IHptyping0 _ _ H7 (ptyping_wf_trec H6 H4));
    intros (e3', (H8, H9)); exists e3'; split; trivial;
    exact (P_Rcd_Cons H6 H8 e)
  | intros e1' X H1 H2; exists e1'; split; trivial;
    apply P_Rcd_Nil ].
Qed.

Lemma typing_narrowing_ind :
  forall (e e' : env) (X : nat) (t : term) (U : typ),
  narrow X e e' -> typing e t U -> typing e' t U.
intros e e' n t U H1 H2; generalize e' n H1; clear e' n H1;
induction H2 using typing_induction with (P0 :=
  fun e t U (H : rtyping e t U) => forall (e' : env) (n : nat),
  narrow n e e' -> rtyping e' t U);
  [ intros e' n1 H1; apply T_Var;
      [ exact (narrow_wf_env H1 w)
      | rewrite <- get_var_narrow with (1 := H1); trivial ]
  | intros e' n1 H1; apply T_Abs; apply IHtyping with (n := n1);
    apply narrow_extend_var; trivial;
    exact (narrow_wf_typ H1 (proj1 (proj1 (typing_wf H2))))
  | intros e' n1 H1; eapply T_App; eauto
  | intros e' n1 H1; apply T_Tabs; apply IHtyping with (n := S n1);
    apply narrow_extend_bound with (X := n1); trivial;
    exact (narrow_wf_typ H1 (proj1 (proj1 (typing_wf H2))))
  | intros e' n1 H1; eapply T_Tapp; eauto; exact (sub_narrowing H1 s)
  | intros e' n1 H1; apply T_Sub with (1 := IHtyping _ _ H1);
    exact (sub_narrowing H1 s)
  | intros e'' n1 H1;
    assert (H2 := narrow_wf_typ H1 (proj2 (proj2 (typing_wf H2_))));
    generalize (ptyping_narrowing_ind p0 H1 H2); intros (e2', (H3, H4));
    exact (T_Let (IHtyping1 _ _ H1) H3 (IHtyping2 _ _ H4))
  | intros e' n1 H1; apply T_Rcd; eauto
  | intros e' n1 H1; apply T_Proj with (2 := e0); eauto
  | intros e' n1 H1;
    exact (T_Rcd_Cons (IHtyping _ _ H1) (IHtyping0 _ _ H1) e0 e1)
  | intros e' n1 H1; apply T_Rcd_Nil; exact (narrow_wf_env H1 w) ].
Qed.

Lemma typing_narrowing :
 forall (e : env) (t : term) (U V1 V2 : typ),
 typing (ebound e V1) t U -> sub e V2 V1 -> typing (ebound e V2) t U.
intros e t U V1 V2 H1 H2; exact (typing_narrowing_ind (narrow_0 H2) H1).
Qed.

(****)

(*** A.8 Lemma [Subtyping preserves typing] ***)

(* Compared to the lemma in the paper proof, this lemma is slightly
   stronger: [u] is typed in a larger environment.  This makes it
   possible to use our one-step weakning lemmas rather that the
   stronger lemmas of the paper proof. *)

Lemma subst_preserves_ptyping :
  forall (e1 e2 : env) (p : pat) (x : nat) (u : term) (T W : typ),
  ptyping e1 p T e2 ->
  typing (remove_var e1 x) u W -> wf_typ (remove_var e1 x) T ->
  get_var e1 x = Some W ->
  ptyping (remove_var e1 x) p T
          (remove_var e2 (offset (fun x => 1 + x) p x)) /\
  exists W, typing (remove_var e2 (offset (fun x => 1 + x) p x))
                   (offset (shift 0) p u) W /\
            get_var e2 (offset (fun x => 1 + x) p x) = Some W.
intros e1 e2 p x u T W H1; generalize x u W; clear x u W;
induction H1 using ptyping_induction with (P0 :=
  fun e1 p T e2 (H : prtyping e1 p T e2) =>
  forall (x : nat) (u : term) (W : typ),
   typing (remove_var e1 x) u W -> wf_trec (remove_var e1 x) T ->
   get_var e1 x = Some W ->
   prtyping (remove_var e1 x) p T
            (remove_var e2 (roffset (fun x => 1 + x) p x)) /\
   (exists W : typ,
      typing (remove_var e2 (roffset (fun x => 1 + x) p x))
             (roffset (shift 0) p u) W /\
      get_var e2 (roffset (fun x => 1 + x) p x) = Some W));
  [ simpl; intros x u W H1 H2 H3; split;
      [ apply P_Var
      | exists W; split; trivial;
        exact (typing_weakening_var H2 H1) ]
  | intros x u W H1 H2 H3; generalize (IHptyping _ _ _ H1 H2 H3);
    intros (H4, (V, (H5, H6))); split;
      [ exact (P_Rcd H4)
      | exists V; auto ]
  | simpl; intros x u W H2 (H3, (H4, H5)) H6;
    generalize (IHptyping _ _ _ H2 H3 H6); clear IHptyping;
    intros (H7, (W1, (H8, H9)));
    generalize (IHptyping0 _ _ _ H8 (ptyping_wf_trec H7 H4) H9);
    clear IHptyping0; intros (G1, (W2, (G2, G3))); split;
      [ exact (P_Rcd_Cons H7 G1 e)
      | exists W2; split; trivial ]
  | intros x u W H1 H2 H3; split;
      [ apply P_Rcd_Nil
      | exists W; auto ] ].
Qed.

Lemma subst_preserves_typing :
  forall (e : env) (x : nat) (t u : term) (V W : typ),
  typing e t V ->
  typing (remove_var e x) u W -> get_var e x = Some W ->
  typing (remove_var e x) (subst t x u) V.
intros e n t u V W H; generalize n u W; clear n u W;
induction H using typing_induction with (P0 :=
  fun e t V (H : rtyping e t V) => forall (n : nat) (u : term) (W : typ),
  typing (remove_var e n) u W ->
  get_var e n = Some W -> rtyping (remove_var e n) (rsubst t n u) V);
intros n' u W H1 E1; simpl;
  [ case (lt_eq_lt_dec x n');
      [ intro s; case s; clear s; intro H2;
          [ apply T_Var;
              [ apply wf_env_remove_var; trivial
              | rewrite get_var_remove_var_lt with (1 := H2); trivial ]
          | rewrite H2 in e0; rewrite e0 in E1; injection E1;
            intro E3; rewrite E3; trivial ]
      | intro H2; apply T_Var;
          [ apply wf_env_remove_var; trivial
          | induction x;
              [ inversion H2
              | simpl; rewrite <- minus_n_O;
                rewrite get_var_remove_var_ge; trivial; omega ] ] ]
  | apply T_Abs; apply (IHtyping (S n') (shift 0 u) W); trivial;
    assert (H2 := wf_typ_remove_var n' (proj1 (proj1 (typing_wf H))));
    exact (typing_weakening_var H2 H1)
  | exact (T_App (IHtyping1 _ u W H1 E1) (IHtyping2 _ u W H1 E1))
  | apply T_Tabs; apply (IHtyping n' (shift_typ 0 u) (tshift 0 W));
      [ assert (H2 := wf_typ_remove_var n' (proj1 (proj1 (typing_wf H))));
        exact (typing_weakening_bound H2 H1)
      | simpl; rewrite E1; trivial ]
  | apply T_Tapp with (1 := (IHtyping _ u W H1 E1));
    exact (sub_strengthening_var n' s)
  | apply T_Sub with (1 := (IHtyping _ u W H1 E1));
    exact (sub_strengthening_var n' s)
  | assert (H2 := wf_typ_remove_var n' (proj2 (proj2 (typing_wf H))));
    generalize (subst_preserves_ptyping p0 H1 H2 E1);
    intros (H3, (V, (H4, H5)));
    exact (T_Let (IHtyping1 _ _ _ H1 E1) H3 (IHtyping2 _ _ _ H4 H5))
  | apply T_Rcd; eauto
  | apply T_Proj with (2 := e0); eauto
  | assert (H2 := IHtyping _ _ _ H1 E1); assert (H3 := IHtyping0 _ _ _ H1 E1);
    apply (T_Rcd_Cons (l := l) H2 H3); trivial;
    rewrite get_rsubst; rewrite e0; trivial
  | apply T_Rcd_Nil; apply wf_env_remove_var; trivial ].
Qed.

(****)

(*** A.10 Lemma [Type substitution preserves subtyping] ***)

Lemma env_subst_sub :
  forall (e e' : env) (T T' : typ) (X : nat),
  env_subst X T' e e' -> (get_bound e X) = (Some T) -> wf_env e' ->
  (sub e' T' (tsubst T X T')).
intros e e' T T' X H; generalize T; clear T; induction H; simpl;
  [ intros T'' E H1; injection E; clear E; intro E; rewrite <- E;
    rewrite <- tsubst_tshift_prop; trivial
  | intros T'' E (H1, H2);
    exact (sub_weakening_var H1 (IHenv_subst _ E H2))
  | intros T'' E (H1, H2); induction (get_bound e X); try discriminate;
    injection E; clear E; intro E; rewrite <- E;
    rewrite <- (tshift_tsubst_prop_1 0 X);
    apply sub_weakening_bound with (1 := H1); auto ].
Qed.

Lemma tsubst_preserves_subtyping :
  forall (e e' : env) (X : nat) (T U V : typ),
  env_subst X T e e' -> sub e U V -> sub e' (tsubst U X T) (tsubst V X T).
intros e e' n T U V H1 H2; generalize n e' T H1; clear n e' T H1; induction H2;
  [ intros n e' T H1; apply SA_Top;
      [ exact (env_subst_wf_env H1 H)
      | exact (env_subst_wf_typ H1 H0 (env_subst_wf_env H1 H)) ]
  | intros n e' T H1; apply sub_reflexivity;
      [ exact (env_subst_wf_env H1 H)
      | exact (env_subst_wf_typ H1 H0 (env_subst_wf_env H1 H)) ]
  | intros n e' T' H1; simpl; case (lt_eq_lt_dec X n);
      [ intros s; case s; clear s;
          [ intro H5; apply SA_Trans_TVar with (U := tsubst U n T');
              [ rewrite env_subst_get_bound_lt with (1 := H1) (2 := H5);
                rewrite H; trivial
              | apply IHsub; trivial ]
          | intro E; apply sub_transitivity with (2 := IHsub _ _ _ H1);
            rewrite E in H; apply (env_subst_sub H1 H);
            exact (env_subst_wf_env H1 (proj1 (sub_wf H2))) ]
      | intro H5; apply SA_Trans_TVar with (U := tsubst U n T');
          [ rewrite env_subst_get_bound_ge with (1 := H1); try omega;
            induction X;
              [ assert False; [ omega | contradiction ]
              | simpl; rewrite H; trivial ]
          | apply IHsub; trivial ] ]
  | intros n e' T H1; simpl; apply SA_Arrow; auto
  | intros n e' T H1; simpl; apply SA_All; auto;
    exact (IHsub2 _ _ _ (es_bound T1 H1))
  | intros n e' T H5; simpl; apply SA_Rcd;
      [ exact (env_subst_wf_env H5 H)
      | exact (env_subst_wf_trec H5 H0 (env_subst_wf_env H5 H))
      | exact (env_subst_wf_trec H5 H1 (env_subst_wf_env H5 H))
      | intros l E; rewrite get_trsubst; rewrite H2; trivial;
        rewrite get_trsubst in E; induction (S1 l); trivial; discriminate
      | intros l S2 T2 E1 E2; assert (H6 := H4 l); clear H4;
        rewrite get_trsubst in E1; rewrite get_trsubst in E2;
        induction (T1 l); try discriminate; induction (S1 l); try discriminate;
        injection E2; injection E1; clear E1 E2; intros E1 E2;
        rewrite <- E1; rewrite <- E2; apply H6; trivial ] ].
Qed.

(****)

(*** A.11 Lemma [Type substitution preserves typing] ***)

Lemma subst_typ_preserves_ptyping_ind :
  forall (e1 e1' e2 : env) (p : pat) (T P : typ) (X : nat),
  ptyping e1 p T e2 ->
  env_subst X P e1 e1' ->
  exists e2', ptyping e1' (psubst_typ p X P) (tsubst T X P) e2' /\
              env_subst X P e2 e2'.
intros e1 e1' e2 p T P X H; generalize e1'; clear e1';
induction H using ptyping_induction with (P0 :=
  fun e1 p T e2 (H : prtyping e1 p T e2) => forall e1' : env,
  env_subst X P e1 e1' ->
  exists e2' : env,
    prtyping e1' (prsubst_typ p X P) (trsubst T X P) e2' /\
    env_subst X P e2 e2');
intros e1' H1;
  [ exists (evar e1' (tsubst T X P)); split;
      [ simpl; apply P_Var
      | apply es_var; trivial ]
  | generalize (IHptyping _ H1); intros (e2', (H2, H3));
    exists e2'; split; trivial;
    simpl; apply P_Rcd; trivial
  | generalize (IHptyping _ H1); intros (e2', (H2, H3));
    generalize (IHptyping0 _ H3); intros (e3', (H4, H5));
    exists e3'; split; trivial;
    apply (P_Rcd_Cons (l := l) H2 H4); rewrite get_prsubst_typ;
    rewrite e; trivial
  | exists e1'; split; trivial;
    apply P_Rcd_Nil ].
Qed.

Lemma subst_typ_preserves_typing_ind :
  forall (e e' : env) (t : term) (U P : typ) (X : nat),
  env_subst X P e e' ->
  typing e t U -> typing e' (subst_typ t X P) (tsubst U X P).
intros e e' t U P n H1 H2; generalize n e' P H1; clear n e' P H1;
induction H2 using typing_induction with (P0 :=
  fun e t U (H : rtyping e t U) => forall (n : nat) (e' : env) (P : typ),
  env_subst n P e e' -> rtyping e' (rsubst_typ t n P) (trsubst U n P));
intros n' e'' P H1; simpl;
  [ apply T_Var;
      [ exact (env_subst_wf_env H1 w)
      | rewrite env_subst_get_var with (1 := H1); rewrite e0; trivial ]
  | apply T_Abs; exact (IHtyping _ _ _ (es_var _ H1))
  | exact (T_App (IHtyping1 _ _ _ H1) (IHtyping2 _ _ _ H1))
  | exact (T_Tabs (IHtyping _ _ _ (es_bound _ H1)))
  | assert (H4 := T_Tapp (T2 := (tsubst T2 n' P)) (IHtyping _ _ _ H1));
    fold tsubst in H4; rewrite (tsubst_tsubst_prop 0 n');
    apply H4; exact (tsubst_preserves_subtyping H1 s)
  | apply T_Sub with (1 := IHtyping _ _ _ H1);
    exact (tsubst_preserves_subtyping H1 s)
  | generalize (subst_typ_preserves_ptyping_ind p0 H1); intros (e2', (H2, H3));
    exact (T_Let (IHtyping1 _ _ _ H1) H2 (IHtyping2 _ _ _ H3))
  | apply T_Rcd; auto
  | apply T_Proj with (T1 := trsubst T1 n' P);
      [ simpl in IHtyping; auto
      | rewrite get_trsubst; rewrite e0; trivial ]
  | apply (T_Rcd_Cons (l := l) (IHtyping _ _ _ H1) (IHtyping0 _ _ _ H1));
      [ rewrite get_rsubst_typ; rewrite e0; trivial
      | rewrite get_trsubst; rewrite e1; trivial ]
  | exact (T_Rcd_Nil (env_subst_wf_env H1 w)) ].
Qed.

Lemma subst_typ_preserves_typing :
  forall (e : env) (t : term) (U P Q : typ),
  typing (ebound e Q) t U -> sub e P Q ->
  typing e (subst_typ t 0 P) (tsubst U 0 P).
intros e t U P Q H1 H2; exact (subst_typ_preserves_typing_ind (es_here H2) H1).
Qed.

(****)

(*** A.12 Lemma [Inversion of subtyping] ***)

(* For the first cases we can use Coq inversion tactics instead.
   The last case is less immediate *)

Lemma record_subtyping_inversion :
  forall (e : env) (S : typ) (P : trec),
  sub e S (trecord P) ->
  (exists X, S = tvar X) \/
  (exists Q, S = trecord Q /\
             forall (l : lab) (T : typ), P l = Some T ->
             exists U, Q l = Some U /\ sub e U T).
intros e S P H; cut (exists V, V = trecord P);
  [ intros (V, E); rewrite <- E in H; generalize P E; clear P E;
    induction H; try (intros; discriminate);
      [ intros P E; left; exists X; trivial
      | intros P E; right; injection E; clear E; intro E;
        rewrite <- E; clear P E H4; exists S1; split; trivial;
        intros l T E1; assert (H4 :exists S2, S1 l = Some S2);
          [ assert (H4 := H2 l); induction (S1 l);
              [ exists a; trivial
              | rewrite H4 in E1; trivial; discriminate ]
          | generalize H4; clear H4; intros (S2, E2);
            exists S2; split; trivial;
            exact (H3 _ _ _ E1 E2) ] ]
  | exists (trecord P); trivial ].
Qed.

(****)

(*** A.13 Lemma ***)

Lemma t_abs_inversion :
  forall (e : env) (t : term) (T0 T1 T2 T3 : typ),
  typing e (abs T1 t) T0 ->
  sub e T0 (arrow T2 T3) ->
  sub e T2 T1 /\
  (exists T4, sub e T4 T3 /\ typing (evar e T1) t T4).
intros e t T0 T1 T2 T3 H; cut (exists t' : _, t' = abs T1 t);
  [ intros (t', E1); rewrite <- E1 in H; generalize t T1 T2 T3 E1;
    clear t T1 T2 T3 E1;
    induction H; intros; try discriminate;
      [ injection E1; intros E2 E3; rewrite <- E2; rewrite <- E3;
        inversion_clear H0; split; [ trivial | exists T2; split; trivial ]
      | apply IHtyping with (1 := E1) (2 := sub_transitivity H0 H1) ]
  | exists (abs T1 t); trivial ].
Qed.

Lemma t_tabs_inversion :
  forall (e : env) (t : term) (T0 T1 T2 T3 : typ),
  typing e (tabs T1 t) T0 ->
  sub e T0 (all T2 T3) ->
  sub e T2 T1 /\
  (exists T4, sub (ebound e T2) T4 T3 /\ typing (ebound e T2) t T4).
intros e t T0 T1 T2 T3 H; cut (exists t' : _, t' = tabs T1 t);
  [ intros (t', E1); rewrite <- E1 in H; generalize t T1 T2 T3 E1;
    clear t T1 T2 T3 E1;
    induction H; intros; try discriminate;
      [ injection E1; intros E2 E3; rewrite <- E2; rewrite <- E3;
        inversion_clear H0; split; trivial;
        exists T2; split; trivial; exact (typing_narrowing H H1)
      | apply IHtyping with (1 := E1) (2 := sub_transitivity H0 H1) ]
  | exists (tabs T1 t); trivial ].
Qed.

Lemma t_record_inversion :
  forall (e : env) (t1 : rec) (T : typ) (T1 : trec),
  typing e (record t1) T ->
  sub e T (trecord T1) ->
  forall (l : lab) (T2 : typ),
  T1 l = Some T2 ->
  exists t2, t1 l = Some t2 /\ typing e t2 T2.
intros e t1 T T1 H; cut (exists t' : _, t' = record t1);
  [ intros (t', E1); rewrite <- E1 in H;
    induction H; try (intros; discriminate);
      [ intro H1; apply IHtyping; trivial; exact (sub_transitivity H0 H1)
      | injection E1; clear E1; intro E1; rewrite E1 in H; clear t E1;
        intros H1 l T2 E1; generalize (record_subtyping_inversion H1);
        intros [(X, E) | (Q, (E3, H4))];
          [ discriminate
          | generalize (H4 _ _ E1); intros (U, (E4, H5));
            injection E3; clear E3; intro E3; rewrite E3 in H;
            cut (exists t2, t1 l = Some t2);
              [ intros (t2, E2); exists t2; split; trivial;
                apply T_Sub with (2 := H5); generalize E2 E4;
                clear T T1 T2 H1 H4 H5 E1 E2 E3 E4;
                induction H; simpl;
                  [ case (lab_eq_dec l l0);
                      [ intros E1 E2 E3; injection E3; injection E2;
                        clear E2 E3; intros E2 E3;
                        rewrite <- E2; rewrite <- E3; trivial
                      | trivial ]
                  | intros; discriminate ]
              | clear T1 T H1 T2 E1 H4 H5 E3;
                generalize E4; clear E4;
                induction H; simpl;
                  [ case (lab_eq_dec l l0); trivial;
                    intros; exists t1; trivial
                  | intros; discriminate ] ] ] ]
  | exists (record t1); trivial ].
Qed.

(****)

(*** A.14 Lemma [Canonical Forms] ***)

Lemma fun_value :
  forall (t : term) (T1 T2 : typ),
  value t -> typing empty t (arrow T1 T2) ->
  exists t' , exists T1' , t = abs T1' t'.
intros t T1 T2 H1 H; cut (exists e, e = empty);
  [ intros (e, E1); rewrite <- E1 in H; cut (exists T0, T0 = arrow T1 T2);
      [ intros (T0, E2); rewrite <- E2 in H; generalize T1 T2 E2;
        clear T1 T2 E2; induction H; try contradiction;
          [ intros T3 T4 E; exists t; exists T1; trivial
          | intros; discriminate
          | intros T3 T4 E2; rewrite E2 in H0; inversion H0;
              [ rewrite E1 in H2; induction X; discriminate
              | exact (IHtyping H1 E1 _ _ (sym_eq H5)) ]
          | intros; discriminate ]
      | exists (arrow T1 T2); trivial ]
  | exists empty; trivial ].
Qed.

Lemma typefun_value :
  forall (t : term) (T1 T2 : typ),
  value t -> typing empty t (all T1 T2) ->
  exists t', exists T1', t = tabs T1' t'.
intros t T1 T2 H1 H; cut (exists e, e = empty);
  [ intros (e, E1); rewrite <- E1 in H; cut (exists T0, T0 = all T1 T2);
      [ intros (T0, E2); rewrite <- E2 in H; generalize T1 T2 E2;
        clear T1 T2 E2; induction H; try contradiction;
          [ intros; discriminate
          | intros T3 T4 E; exists t; exists T1; trivial
          | intros T3 T4 E2; rewrite E2 in H0; inversion H0;
              [ rewrite E1 in H2; induction X; discriminate
              | exact (IHtyping H1 E1 _ _ (sym_eq H5)) ]
          | intros; discriminate ]
      | exists (all T1 T2); trivial ]
  | exists empty; trivial ].
Qed.

Lemma value_not_var_type :
  forall (e : env) (t : term) (X : nat),
  typing e t (tvar X) -> value t -> False.
intros e t X H; cut (exists T, T = tvar X);
  [ intros (T, E); rewrite <- E in H; generalize X E; clear X E;
    induction H; try contradiction; try (intros; discriminate);
    generalize IHtyping; clear H IHtyping;
    induction H0; try (intros; discriminate); trivial;
    intros H1 Y E H2; exact (H1 _ (refl_equal _) H2)
  | exists (tvar X); trivial ].
Qed.

Lemma record_value :
  forall (e : env) (t : term) (T : trec),
  value t -> typing e t (trecord T) ->
  exists t', t = record t' /\ forall (l : lab), t' l = None -> T l = None.
intros e t T H1 H; cut (exists T0, T0 = trecord T);
  [ intros (T0, E2); rewrite <- E2 in H; generalize T E2;
    clear T E2; induction H; try contradiction; try (intros; discriminate);
      [ intros T E; rewrite E in H0; inversion H0;
          [ rewrite <- H5 in H; case (value_not_var_type H H1)
          | generalize (IHtyping H1 _ (sym_eq H8));
            intros (t', (G1, G2)); exists t'; split; trivial;
            auto ]
      | intros T0 E; injection E; clear E; intro E; rewrite <- E;
        exists t; split; trivial; clear T0 E; intro l; induction H;
          [ simpl; case (lab_eq_dec l l0);
              [ intros; discriminate
              | intros _; exact (IHrtyping (proj2 H1)) ]
          | trivial ] ]
  | exists (trecord T); trivial ].
Qed.

(****)

(*** A value can be matched again a pattern when this is well-typed. ***)

(* This crucial lemma is missing from the paper proof! *)

Lemma get_value :
  forall (l : lab) (t : rec) (t' : term),
  t l = Some t' -> rvalue t -> value t'.
intros l t; induction t;
  [ intro t'; simpl; case (lab_eq_dec l l0);
      [ intros E1 E2 (H1, H2); injection E2; intro E; rewrite <- E; trivial
      | intros _ E2 (H1, H2); auto ]
  | intros; discriminate ].
Qed.

Scheme pat_induction := Induction for pat Sort Prop
with prec_induction := Induction for prec Sort Prop.

Lemma get_offset :
   forall (l : lab) (p : pat) (t1 : rec) (t2 : term),
   t1 l = Some t2 ->
   offset (rshift 0) p t1 l = Some (offset (shift 0) p t2).
intros l p; induction p using pat_induction with (P0 :=
  fun p => forall (t1 : rec) (t2 : term),
  t1 l = Some t2 ->
  roffset (rshift 0) p t1 l = Some (roffset (shift 0) p t2)); simpl; trivial;
  [ intros t1 t2 E; rewrite get_rshift; rewrite E; trivial
  | intros t1 t2 E; exact (IHp0 _ _ (IHp _ _ E)) ].
Qed.

Lemma typing_weakening_ptyping :
  forall (e1 e2 : env) (p : pat) (T U : typ) (t : term),
  ptyping e1 p T e2 -> wf_typ e1 T -> typing e1 t U ->
  typing e2 (offset (shift 0) p t) U.
intros e1 e2 p T U t H; generalize t; clear t;
induction H using ptyping_induction with (P0 :=
  fun e1 p T e2 (H : prtyping e1 p T e2) => forall t : term,
  wf_trec e1 T -> typing e1 t U -> typing e2 (roffset (shift 0) p t) U);
trivial;
  [ intro t; simpl; apply typing_weakening_var
  | simpl; intros t (H1, (H2, H3)) H4;
    apply IHptyping0 with (1 := ptyping_wf_trec H H2); auto ].
Qed.

Lemma rvalue_offset_prop :
  forall (p : pat) (t : rec),
  rvalue t -> rvalue (offset (rshift 0) p t).
intro p; induction p using pat_induction with (P0 :=
  fun p => forall (t : rec),
  rvalue t -> rvalue (roffset (rshift 0) p t));
trivial;
  [ simpl; clear t; intro t;
    induction t using rec_induction with (P :=
      fun t => value t -> value (shift 0 t));
    try contradiction; simpl; trivial;
    intros (H1, H2); split; auto
  | intros t H1; exact (IHp0 _ (IHp _ H1)) ].
Qed.

Lemma matching_defined :
  forall (e e' : env) (p : pat) (T1 : typ) (t1 t2 : term),
  ptyping e p T1 e' -> value t1 -> typing e t1 T1 ->
  exists t, pmatch p t1 t2 = Some t.
intros e e' p T1 t1 t2 H; generalize t1 t2; clear t1 t2;
induction H using ptyping_induction with (P0 :=
  fun e p T1 e' (H : prtyping e p T1 e') => forall (t1 : rec) (t2 : term),
  wf_trec e T1 ->rvalue t1 ->
  (forall (l : lab) (T2 : typ),
   T1 l = Some T2 -> exists t2, t1 l = Some t2 /\ typing e t2 T2) ->
  exists t : term, prmatch p t1 t2 = Some t);
  [ intros t1 t2 E H1; exists (subst t2 0 t1); trivial
  | intros t1 t2 H1 H2; generalize (record_value H1 H2);
    intros (t', (E1, H3)); rewrite E1 in H1; rewrite E1 in H2;
    rewrite E1; clear t1 E1;
    assert (H4 := proj1 (typing_wf H2));
    assert (H5 := proj2 (proj2 (typing_wf H2)));
    assert (H6 := t_record_inversion H2 (sub_reflexivity H4 H5)); clear H4 H5;
    exact (IHptyping _ t2 (proj2 (proj2 (typing_wf H2))) H1 H6)
  | simpl; intros t3 t4 (H1, (H2, H3)) H4 H5; generalize (H5 l); simpl;
    case (lab_eq_dec l l); try (intros E; case E; trivial; fail); intros _;
    intros H6; generalize (H6 _ (refl_equal _)); clear H6;
    intros (t5, (E1, H7)); rewrite E1; simpl;
    case (IHptyping0 (offset (rshift 0) t1 t3) t4 (ptyping_wf_trec H H2));
      [ exact (rvalue_offset_prop t1 H4)
      | intros l' T2 E2; generalize (H5 l'); case (lab_eq_dec l' l);
          [ intros E; rewrite E in E2; rewrite H3 in E2; discriminate
          | clear H5; intros _ H5; generalize (H5 _ E2); clear H5 E2;
            intros (t6, (E2, H8)); exists (offset (shift 0) t1 t6); split;
              [ exact (get_offset t1 E2)
              | exact (typing_weakening_ptyping H H1 H8) ] ]
      | intros t6 E2; rewrite E2; simpl;
        exact (IHptyping _ t6 (get_value E1 H4) H7) ]
  | intros t1 t2 E H1 H2; exists t2; trivial ].
Qed.

(****)

(*** A.15 Lemma ***)

Lemma local_progress :
  forall (t : term) (U : typ),
  typing empty t U -> value t \/
  exists c, exists t0, exists t0', red t0 t0' /\ t = ctx_app c t0.
intros t U H; cut (exists e, e = empty);
  [ intros (e, E); rewrite <- E in H; generalize E; clear E;
    induction H using typing_induction with (P0 :=
      fun e t U (H : rtyping e t U) =>
      e = empty ->
      rvalue t \/
      exists c, exists t0, exists t0', red t0 t0' /\ t = rctx_app c t0);
    simpl; auto;
      [ intro E; rewrite E in e0; induction x; discriminate
      | intro E; right; case (IHtyping1 E); clear IHtyping1;
          [ intro H2; case (IHtyping2 E); clear IHtyping2;
              [ intro H3; rewrite E in H; generalize (fun_value H2 H);
                intros (t', (T1', E1)); rewrite E1; exists c_hole;
                exists (app (abs T1' t') t2); exists (subst t' 0 t2);
                split; trivial; apply E_AppAbs; trivial
              | intros (c, (t0, (t0', (H3, E1)))); exists (c_apparg H2 c);
                exists t0; exists t0'; rewrite E1; auto ]
          | intros (c, (t0, (t0', (H3, E1)))); exists (c_appfun c t2);
            exists t0; exists t0'; rewrite E1; auto ]
      | right; case (IHtyping E); clear IHtyping;
          [ intro H1; rewrite E in H; generalize (typefun_value H1 H);
            intros (t', (T1', E1)); rewrite E1; exists c_hole;
            exists (tapp (tabs T1' t') T2); exists (subst_typ t' 0 T2);
            split; trivial; apply E_TappTabs
          | intros (c, (t0, (t0', (H3, E1)))); exists (c_typefun c T2);
            exists t0; exists t0'; rewrite E1; auto ]
      | intro E; right; case (IHtyping1 E);
          [ intro H2; exists c_hole; exists (tlet p t1 t2);
            generalize (matching_defined t2 p0 H2 H); intros (t0', E1);
            exists t0'; split; trivial;
            exact (E_LetV H2 E1)
          | intros (c, (t0, (t0', (H1, H2))));
            exists (c_let p c t2); exists t0; exists t0'; split; trivial;
            rewrite H2; trivial ]
      | intro E; case (IHtyping E);
          [ auto
          | intros (c, (t0, (t0', (H1, H2)))); right;
            exists (c_record c); exists t0; exists t0'; split; trivial;
            rewrite H2; trivial ]
      | intro E; right; case (IHtyping E);
          [ intro H2; exists c_hole; exists (proj t1 l);
            rewrite E in H; generalize (record_value H2 H);
            intros (t', (H3, H4));
            assert (H5 : exists t0', t' l = Some t0');
              [ assert (H5 := H4 l); induction (t' l);
                  [ exists a; trivial
                  | rewrite (H5 (refl_equal _)) in e0; discriminate ]
              | generalize H5; clear H5; intros (t0', H5);
                exists t0'; split; trivial;
                rewrite H3 in H2; rewrite H3; exact (E_ProjRcd H2 H5) ]
          | intros (c, (t0, (t0', (H1, H2))));
            exists (c_proj c l); exists t0; exists t0'; split; trivial;
            rewrite H2; trivial ]
      | intro E; case (IHtyping E);
          [ intro H2; case (IHtyping0 E);
              [ auto
              | intros (c, (t0, (t0', (H3, H4)))); right;
                exists (c_next l H2 c); exists t0; exists t0'; split; trivial;
                rewrite H4; trivial ]
          | intros (c, (t0, (t0', (H3, H4)))); right;
            exists (c_here l c t2); exists t0; exists t0'; split; trivial;
            rewrite H4; trivial ] ]
  | exists empty; trivial ].
Qed.

(****)

(*** A.16 Theorem [Progress] ***)

Theorem progress :
  forall (t : term) (U : typ),
  typing empty t U -> value t \/ exists t', red t t'.
intros t U H; generalize (local_progress H);
intros [H1 | (c, (t0, (t0', (H1, H2))))]; auto;
right; exists (ctx_app c t0'); rewrite H2; apply E_Ctx; trivial.
Qed.

(****)

(*** A.17 Lemma [Matched patterns preserve typing] ***)

Lemma matched_patterns_preserve_typing :
  forall (e e' : env) (p : pat) (t1 t2 t : term) (T1 T2 : typ),
  ptyping e p T1 e' -> typing e t1 T1 -> typing e' t2 T2 ->
  pmatch p t1 t2 = Some t -> typing e t T2.
intros e e' p t1 t2 t T1 T2 H; generalize t1 t2 t; clear t1 t2 t;
induction H using ptyping_induction with (P0 :=
  fun e p T1 e' (H : prtyping e p T1 e') => forall (t1 : rec) (t2 t : term),
  wf_trec e T1 ->
  (forall (l : lab) (T2 : typ),
   T1 l = Some T2 -> exists t2, t1 l = Some t2 /\ typing e t2 T2) ->
  typing e' t2 T2 -> prmatch p t1 t2 = Some t -> typing e t T2); simpl;
  [ intros t1 t2 t H1 H2 E; injection E; clear E; intro E; rewrite <- E;
    apply (subst_preserves_typing (x := 0) H2 H1); trivial
  | intros t1 t2 t3 H1 H2 H3; induction t1; try discriminate;
    assert (H4 := proj1 (typing_wf H1));
    assert (H5 := proj2 (proj2 (typing_wf H1)));
    assert (H6 := t_record_inversion H1 (sub_reflexivity H4 H5));
    eauto
  | intros t3 t4 t (H1, (H2, E1)) H3 H4 E2;
    generalize (opt_bind_some E2); clear E2; intros (t5, (E2, E3));
    generalize (opt_bind_some E3); clear E3; intros (t6, (E3, E4));
    generalize (H3 l);
    case (lab_eq_dec l l); try (intros E; case E; trivial; fail); intros _;
    intro G; generalize (G _ (refl_equal _)); clear G; intros (t7, (E5, H5));
    rewrite E3 in E5; injection E5; clear E5; intro E5;
    rewrite <- E5 in H5; clear t7 E5;
    apply IHptyping with (1 := H5) (3 := E4);
    apply IHptyping0 with (1 := ptyping_wf_trec H H2) (3 := H4) (4 := E2);
    intros l' T3 E5; generalize (H3 l'); case (lab_eq_dec l' l);
      [ intro E; rewrite E in E5; rewrite E1 in E5; discriminate
      | intros _ H6; generalize (H6 _ E5); intros (t7, (E6, H7));
        exists (offset (shift 0) t1 t7); split;
          [ exact (get_offset t1 E6)
          | exact (typing_weakening_ptyping H H1 H7) ] ]
  | intros t1 t2 t _ H1 H2 E; injection E; intro E1; rewrite <- E1; trivial ].
Qed.

(****)

(*** A.18 Lemma ***)

(*
   We only prove the first part of the lemma, as the second part is
   not needed.
   We don't follow the paper proof sketch (induction on the structure
   of evaluation contexts, then case on the last rule used in the
   typing derivation) as this does not go through...  Instead, our
   proof is by induction on the typing derivation and case on the
   evaluation context.
*)

Lemma rctx_domain :
  forall (t t' : term) (l : lab) (c : rctx),
  rctx_app c t l = None -> rctx_app c t' l = None.
intros t t' l c; induction c; simpl; case (lab_eq_dec l l0); trivial;
intros; discriminate.
Qed.

Lemma context_replacement :
   forall (e : env) (c : ctx) (t t' : term) (T : typ),
   (forall (T' : typ), (typing e t T') -> (typing e t' T')) ->
   typing e (ctx_app c t) T -> typing e (ctx_app c t') T.
intros e c t t' T H1 H2; cut (exists t'', t'' = ctx_app c t);
  [ intros (t'', E); rewrite <- E in H2;
    generalize c E H1; clear c E H1;
    induction H2 using typing_induction with (P0 :=
      fun e t'' T (H : rtyping e t'' T) => forall c : rctx,
      (forall (T' : typ), (typing e t T') -> (typing e t' T')) ->
      t'' = rctx_app c t -> rtyping e (rctx_app c t') T);
      [ induction c; try (intros; discriminate); simpl;
        intros E H1; apply H1; rewrite <- E; apply T_Var; trivial
      | induction c; try (intros; discriminate); simpl;
        intros E H1; apply H1; rewrite <- E; apply T_Abs; trivial
      | induction c; try (intros; discriminate); simpl; intros E H1;
          [ apply H1; rewrite <- E; exact (T_App H2_ H2_0)
          | injection E; clear E; intros E1 E2;
            rewrite <- E1; apply T_App with (2 := H2_0);
            apply IHtyping1; trivial
          | injection E; clear E; intros E1 E2;
            rewrite <- E2; apply T_App with (1 := H2_);
            apply IHtyping2; trivial ]
      | induction c; try (intros; discriminate); simpl;
        intros E H1; apply H1; rewrite <- E; exact (T_Tabs H2)
      | induction c; try (intros; discriminate); simpl; intros E H1;
          [ apply H1; rewrite <- E; exact (T_Tapp H2 s)
          | injection E; clear E; intros E1 E2;
            rewrite <- E1; apply T_Tapp with (2 := s);
            apply IHtyping; trivial ]
      | intros c E H1; apply T_Sub with (2 := s); apply IHtyping; trivial
      | induction c; try (intros; discriminate); simpl; intros E H1;
          [ apply H1; rewrite <- E; exact (T_Let H2_ p0 H2_0)
          | injection E; clear E; intros E1 E2 E3;
            rewrite <- E1; rewrite <- E3;
            apply T_Let with (2 := p0) (3 := H2_0);
            apply IHtyping1; trivial ]
      | induction c; try (intros; discriminate); simpl; intros E H1;
          [ apply H1; rewrite <- E; exact (T_Rcd r)
          | injection E; clear E; intros E1;
            apply T_Rcd; apply IHtyping; trivial ]
      | induction c; try (intros; discriminate); simpl; intros E H1;
          [ apply H1; rewrite <- E; exact (T_Proj H2 e0)
          | injection E; clear E; intros E1 E2;
            rewrite <- E1; apply T_Proj with (2 := e0);
            apply IHtyping; trivial ]
      | induction c; try (intros; discriminate); simpl; intros H1 E;
          [ injection E; clear E; intros E1 E2 E3;
            rewrite <- E1; rewrite <- E3; apply T_Rcd_Cons; trivial;
            apply IHtyping; trivial
          | injection E; clear E; intros E1 E2 E3;
            rewrite <- E2; rewrite <- E3; apply T_Rcd_Cons; trivial;
              [ apply IHtyping0; trivial
              | rewrite E1 in e0; exact (rctx_domain t' e0) ] ]
      | induction c; intros; discriminate ]
  | exists (ctx_app c t); trivial ].
Qed.

(****)

(*** A.19 Lemma ***)

Lemma local_preservation_app :
  forall (e : env) (t12 t2 : term) (T11 U : typ),
  typing e (app (abs T11 t12) t2) U -> typing e (subst t12 0 t2) U.
intros e t12 t2 T11 U H; cut (exists t, t = app (abs T11 t12) t2);
  [ intros (t, E); rewrite <- E in H; induction H; try discriminate;
      [ injection E; clear E; intros E1 E2; rewrite E2 in H;
        assert (H6 := proj1 (typing_wf H));
        assert (H7 := proj2 (proj2 (typing_wf H)));
        generalize (t_abs_inversion H (sub_reflexivity H6 H7));
        intros (H2, (T4, (H4, H5))); apply T_Sub with (2 := H4);
        apply (subst_preserves_typing (x := 0) (u := t2) (W := T11) H5);
        trivial; simpl; rewrite <- E1; exact (T_Sub H0 H2)
      | apply T_Sub with (2 := H0); auto ]
  | exists (app (abs T11 t12) t2); trivial ].
Qed.

Lemma local_preservation_tapp :
  forall (e : env) (t12 : term) (T11 T2 U : typ),
  typing e (tapp (tabs T11 t12) T2) U -> typing e (subst_typ t12 0 T2) U.
intros e t12 T11 T2 U H; cut (exists t, t = tapp (tabs T11 t12) T2);
  [ intros (t, E); rewrite <- E in H; induction H; try discriminate;
      [ injection E; clear E; intros E1 E2; rewrite E2 in H;
        assert (H7 := proj1 (typing_wf H));
        assert (H8 := proj2 (proj2 (typing_wf H)));
        generalize (t_tabs_inversion H (sub_reflexivity H7 H8));
        intros (H2, (T3, (H4, H5))); assert (H6 := T_Sub H5 H4);
        rewrite <- E1; exact (subst_typ_preserves_typing H6 H0)
      | apply T_Sub with (2 := H0); auto ]
  | exists (tapp (tabs T11 t12) T2); trivial ].
Qed.

Lemma local_preservation_proj :
  forall (e : env) (t1 : rec) (t1' : term) (l : lab) (U : typ),
  typing e (proj (record t1) l) U -> t1 l = Some t1' -> typing e t1' U.
intros e t1 t1' l U H; cut (exists t, t = proj (record t1) l);
  [ intros (t, E); rewrite <- E in H; induction H; try discriminate;
      [ intro E1; apply T_Sub with (2 := H0); auto
      | injection E; clear E; intros E1 E2 E3; rewrite E2 in H;
        rewrite E1 in H0; clear l0 t0 E1 E2 IHtyping;
        assert (H1 := proj1 (typing_wf H));
        assert (H2 := proj2 (proj2 (typing_wf H)));
        generalize (t_record_inversion H (sub_reflexivity H1 H2) H0);
        intros (t2, (E4, H3));
        rewrite E3 in E4; injection E4; intro E5; rewrite E5; trivial ]
  | exists (proj (record t1) l); trivial ].
Qed.

Lemma local_preservation_let :
  forall (e : env) (p : pat) (t1 t2 t : term) (U : typ),
  typing e (tlet p t1 t2) U -> pmatch p t1 t2 = Some t -> typing e t U.
intros e p t1 t2 t U H; cut (exists t', t' = tlet p t1 t2);
  [ intros (t', E); rewrite <- E in H; induction H; try discriminate;
      [ intro E1; apply T_Sub with (2 := H0); auto
      | injection E; clear E; intros E1 E2 E3; rewrite E1 in H1;
        rewrite E2 in H; rewrite E3 in H0;
        clear t3 t0 p0 E1 E2 E3 IHtyping1 IHtyping2;
        exact (matched_patterns_preserve_typing H0 H H1) ]
  | exists (tlet p t1 t2); trivial ].
Qed.

(****)

(*** A.20 Theorem [Preservation] ***)

Theorem preservation :
  forall (e : env) (t t' : term) (U : typ),
  typing e t U -> red t t' -> typing e t' U.
intros e t t' U H1 H2; generalize U H1; clear U H1; induction H2; intros U H1;
  [ exact (local_preservation_app H1)
  | exact (local_preservation_tapp H1)
  | exact (local_preservation_let H1 H0)
  | exact (local_preservation_proj H1 H0)
  | exact (context_replacement IHred H1) ].
Qed.

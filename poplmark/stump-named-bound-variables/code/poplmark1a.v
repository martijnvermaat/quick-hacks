(* Solution to POPLmark Challenge 1a, Coq V8.0, Aaron Stump, Dec. 29, 2005 *)
Require Import Arith.
Require Import Omega.
Require Import List.
Require Import Peano_dec.

Parameter name : Set.
Hypothesis eq_name_dec : forall n m : name, {n = m} + {n <> m}.

Inductive tp : Set :=
  var : name -> tp
| const : nat -> tp
| top : tp
| arrow : tp -> tp -> tp
| all : name -> tp -> tp -> tp.

Notation "'all' n <: x . y" := (all n x y) (at level 61, no associativity).
Notation "x --> y" := (arrow x y) (at level 60, right associativity).

(***********************************************************************)
(* size of type expressions                                            *)
(***********************************************************************)

Fixpoint size (T:tp) : nat :=
  match T with
  var _ => 1
| const _ => 1
| top => 1
| T1 --> T2 => 1 + size T1 + size T2
| all x <: T1. T2 => 1 + size T1 + size T2
end.

Lemma size_non_zero : forall Q : tp, size Q > 0.
intro Q; induction Q; simpl in |- *; omega.
Qed.

(**********************************************************************)
(* graft_tp                                                           *)
(**********************************************************************)

Fixpoint graft_tp (Q:tp) (x:name) (T:tp) {struct T} : tp :=
  match T with
    var y => match eq_name_dec y x with 
               left _ => Q
             | right _ => T
             end
  | const y => T
  | top => T
  | T1 --> T2 => (graft_tp Q x T1) --> (graft_tp Q x T2)
  | all y <: T1 . T2 =>
      let T1' := graft_tp Q x T1 in
      let T2' := match eq_name_dec y x with 
                   left _ => T2
                 | right _ => graft_tp Q x T2
                 end in
      all y <: T1' . T2'
  end.

Lemma size_graft_const : forall (x : nat) (y : name) (T : tp), 
                         size (graft_tp (const x) y T) = size T.
intros x y T; induction T; simpl in |- *; try tauto.
 case (eq_name_dec n y); intro; simpl in |- *; trivial.
 rewrite IHT1; rewrite IHT2; trivial.
 rewrite IHT1; case (eq_name_dec n y); intro; simpl in |- *;
  [ trivial | rewrite IHT2; trivial ].
Qed.

(**********************************************************************)
(* put_const                                                          *)
(**********************************************************************)

Fixpoint put_const(c' c:nat)(T:tp) {struct T} : tp :=
  match T with
    var x => T
  | top => T
  | const y => match (eq_nat_dec c y) with
                 left _ => const c'
               | right _ => T
               end
  | T1 --> T2 => (put_const c' c T1) --> (put_const c' c T2)
  | all x <: T1. T2 => all x <: (put_const c' c T1) . (put_const c' c T2)
  end.

Lemma commute_graft_put_const : forall (c1 c2 c3 : nat) (x : name) (T : tp),
                                c1 <> c3 ->
                                graft_tp (const c1) x (put_const c2 c3 T) =
                                put_const c2 c3 (graft_tp (const c1) x T).
intros c1 c2 c3 x T N; induction T; simpl in |- *; try tauto.
 case (eq_name_dec n x); intro B; simpl in |- *; try trivial;
  case (eq_nat_dec c3 c1); intro C; try trivial.
   elim N; congruence.
 case (eq_nat_dec c3 n); intro B; simpl in |- *; trivial.
 rewrite IHT1; rewrite IHT2; trivial.
 case (eq_name_dec n x); intro B; simpl in |- *.
  rewrite IHT1; trivial.
  rewrite IHT1; rewrite IHT2; trivial.
Qed.

(**********************************************************************)
(* const_in                                                           *)
(**********************************************************************)

Fixpoint const_in (n:nat) (T : tp) {struct T} : Prop :=
  match T with
  var x => False
| const x => n = x
| top => False
| T1 --> T2 => const_in n T1 \/ const_in n T2
| all x <: T1. T2 => const_in n T1 \/ const_in n T2
end.

Lemma const_in_graft : forall (c1 c2 :nat)(x:name) (T:tp),
                       const_in c1 (graft_tp (const c2) x T) ->
                       const_in c1 T \/ c1 = c2.
intros c1 c2 x T; induction T; simpl in |- *; try tauto.
 case (eq_name_dec n x); simpl in |- *; intros B C.
  right; assumption.
  elim C.
 case (eq_name_dec n x); tauto.
Qed.

Lemma const_in_put_const : forall (c1 c2 c3 : nat) (T : tp),
                           const_in c1 (put_const c2 c3 T) -> 
                           const_in c1 T \/ c1 = c2.
intros c1 c2 c3 T; induction T; simpl in |- *; try tauto.
case (eq_nat_dec c3 n); tauto.
Qed.

Lemma put_const_not_in : forall (T : tp) (c' c : nat), 
                         ~ const_in c T -> 
                         put_const c' c T = T.
intro T; induction T; simpl in |- *; intros c' c H; try tauto.
 case (eq_nat_dec c n); intro B.
  subst n; elim H; trivial.
  trivial.
 assert (~ const_in c T1 /\ ~ const_in c T2).
  tauto.
  elim H0; intros H0a H0b.
    rewrite (IHT1 c' c H0a); rewrite (IHT2 c' c H0b); trivial.
 assert (~ const_in c T1 /\ ~ const_in c T2).
  tauto.
  elim H0; intros H0a H0b.
    rewrite (IHT1 c' c H0a); rewrite (IHT2 c' c H0b); trivial.
Qed.

Lemma put_const_graft : forall (c' c : nat) (x : name) (T : tp),
            ~ const_in c T ->
            put_const c' c (graft_tp (const c) x T) = graft_tp (const c') x T.
intros c' c x T; induction T; simpl in |- *; intro I; try tauto;
 [ case (eq_name_dec n x); intro B; simpl in |- *; trivial;
    case (eq_nat_dec c c); intro B1; trivial; elim B1; 
    trivial
 | case (eq_nat_dec c n); congruence
 | idtac
 | idtac ]; assert (II : ~ const_in c T1 /\ ~ const_in c T2); 
 try tauto; elim II; clear II; intros Ia Ib; rewrite (IHT1 Ia).
 rewrite (IHT2 Ib); trivial.
 case (eq_name_dec n x); intro B.
  subst n.
    rewrite put_const_not_in; trivial || assumption.
  rewrite (IHT2 Ib).
    trivial.
Qed.

(**********************************************************************)
(* contexts                                                           *)
(**********************************************************************)

Inductive decl : Set :=  bound : tp -> decl.

Definition ctxt := list decl.

Notation "G ~:: d" := (cons d G) (at level 62, left associativity):list_scope.
Notation "G1 ~++ G2" := (G2 ++ G1) 
                                 (at level 62, left associativity):list_scope.

(**********************************************************************)
(* is_ground                                                          *)
(**********************************************************************)

Fixpoint is_ground_h(L:list name)(T:tp) {struct T} : Prop :=
  match T with
    const _ => True
  | var n => In n L
  | top => True
  | T1 --> T2 => is_ground_h L T1 /\ is_ground_h L T2
  | all x <: T1. T2 => is_ground_h L T1 /\ is_ground_h (x::L) T2
  end.

Definition is_ground (T:tp) : Prop := is_ground_h nil T.

Lemma is_ground_h_put_const : forall (T:tp)(L:list name)(c' c:nat), 
                              is_ground_h L T -> 
                              is_ground_h L (put_const c' c T).
intro T; induction T; simpl in |- *; intros; try tauto;
 try (case (eq_nat_dec c n); simpl in |- *; tauto);
 (split; [ apply IHT1 | apply IHT2 ]; tauto).
Qed.

Lemma is_ground_put_const : forall (c' c:nat)(T:tp), 
                            is_ground T -> 
                            is_ground (put_const c' c T).
unfold is_ground in |- *; intros.
apply is_ground_h_put_const; assumption.
Qed.

Lemma is_ground_graft : forall (T : tp) (L : list name) (c : nat) (x : name),
                        is_ground_h L T -> 
                        is_ground_h L (graft_tp (const c) x T).
intro T; induction T; simpl in |- *; intros; try tauto;
 try (case (eq_name_dec n x); simpl in |- *; tauto); 
 split; try (apply IHT1; tauto).
 apply IHT2; tauto.
 case (eq_name_dec n x); intro; [ tauto | apply IHT2; tauto ].
Qed.

Lemma is_ground_h_extend_ : forall (c n:nat) (x:name) (T:tp), 
                            size T <= n -> 
                            forall (L1 L2:list name),
                            is_ground_h (L1 ++ L2) (graft_tp (const c) x T) ->
                            is_ground_h (L1 ++ (x :: L2)) T.
intros c n x; induction n; intro T; case T; simpl in |- *;
 try (intros; elimtype False; omega); try (intros; tauto);
 try (split; apply IHn; tauto || omega); intro n0;
 (case (eq_name_dec n0 x); simpl in |- *; intros; [ subst n0 | idtac ]).
 apply in_or_app; right; apply in_eq.
 apply in_or_app.
   assert (In n0 L1 \/ In n0 L2); try (apply in_app_or; assumption).
   elim H1; clear H1; intro H1; [ left | right; apply in_cons ]; assumption.
 assert (R : L2 ~:: x ~++ L1 ~:: x = L2 ~:: x ~++ (L1 ~:: x));
  try (simpl in |- *; trivial); rewrite R; split; apply IHn;
  try tauto || omega.
   simpl in |- *.
   apply is_ground_graft.
   tauto.
 assert (R : L2 ~:: x ~++ L1 ~:: n0 = L2 ~:: x ~++ (L1 ~:: n0));
  try (simpl in |- *; trivial); rewrite R.
   split; apply IHn; tauto || omega.
Qed.

Lemma is_ground_h_extend : forall (c : nat) (x:name) (T:tp), 
                           forall (L1 L2:list name),
                           is_ground_h (L1 ++ L2) (graft_tp (const c) x T) ->
                           is_ground_h (L1 ++ (x :: L2)) T.
intros; apply is_ground_h_extend_ with (n := size T) (c := c);
  assumption || omega.
Qed.

(**********************************************************************)
(* ctxt_const_in                                                      *)
(**********************************************************************)
Fixpoint ctxt_const_in (n:nat) (G:ctxt) {struct G} : Prop :=
  match G with
    G' ~:: (bound T) => const_in n T \/ ctxt_const_in n G'
  | nil => False
  end.

(**********************************************************************)
(* length_append and tactics                                          *)
(**********************************************************************)
Lemma length_append : forall (A : Set) (L1 L2 : list A),
                      length (L1 ++ L2) = length L1 + length L2.
intros A L1; induction L1; intros L2; simpl in |- *; try trivial.
rewrite IHL1.
omega.
Qed.

Ltac lain H := repeat rewrite length_append in H.
Ltac la := repeat rewrite length_append.

(**********************************************************************)
(* ctxt_put_const                                                     *)
(**********************************************************************)

Fixpoint ctxt_put_const (c' c:nat)(G:ctxt) {struct G} : ctxt :=
  match G with
    G' ~:: (bound T) => (ctxt_put_const c' c G') ~:: (bound (put_const c' c T))
  | nil => nil
  end.

Lemma length_ctxt_put_const : forall (c' c : nat) (G : ctxt),
                              length (ctxt_put_const c' c G) = length G.
intros; induction G.
 simpl in |- *; trivial.
 case a; clear a.
   intro t; simpl in |- *; rewrite IHG; trivial.
Qed.

(**********************************************************************)
(* ctxt_is_ground                                                     *)
(**********************************************************************)

Fixpoint ctxt_is_ground(G:ctxt) : Prop :=
  match G with
    G' ~:: (bound T) => is_ground T /\ ctxt_is_ground G'
  | nil => True
  end.

Lemma ctxt_is_ground_put_const_append: forall (G2 G1:ctxt)(c' c:nat), 
                                 ctxt_is_ground (G2 ++ G1) -> 
                                 ctxt_is_ground ((ctxt_put_const c' c G2)++G1).
intro G2; induction G2.
 simpl in |- *; tauto.
 case a; clear a; simpl in |- *; intros; split.
  apply is_ground_put_const; tauto.
  apply IHG2; tauto.
Qed.

Lemma ctxt_is_ground_permute : forall (G2 G1 : ctxt) (U2 U1 : tp),
                          ctxt_is_ground (G2 ++ bound U2 :: bound U1 :: G1) ->
                          ctxt_is_ground (G2 ++ bound U1 :: bound U2 :: G1).
intro G2; induction G2.
 simpl in |- *; tauto.
 case a; clear a; simpl in |- *; intros; split; try tauto.
   apply IHG2; tauto.
Qed.

Lemma ctxt_is_ground_change : forall (G1 G2 : ctxt) (P Q : tp),
                              ctxt_is_ground (G1 ~:: bound Q ~++ G2) ->
                              is_ground P -> 
                              ctxt_is_ground (G1 ~:: bound P ~++ G2).
intros G1 G2 P Q; induction G2; simpl in |- *; try tauto; case a; clear a;
 simpl in |- *; tauto.
Qed.

Lemma ctxt_is_ground_split : forall G1 G2 : ctxt,
                             ctxt_is_ground (G1 ~++ G2) -> 
                             ctxt_is_ground G1 /\ ctxt_is_ground G2.
intros G1 G2; induction G2; simpl in |- *; try tauto; case a; clear a;
 simpl in |- *; intros; tauto.
Qed.

(**********************************************************************)
(* lookup                                                             *)
(**********************************************************************)

Inductive lookup : nat -> ctxt -> tp -> Prop :=
  lookup_s : forall (T:tp) (G:ctxt), lookup 0 (G ~:: (bound T)) T
| lookup_n : forall (n:nat) (T T':tp) (G:ctxt), 
                    lookup n G T ->
                    lookup (S n) (G ~:: (bound T')) T.

Lemma lookup_skip : forall (G2 G1 : ctxt) (U : tp),
                    lookup (length G2) (G2 ++ bound U :: G1) U.
intro G2; induction G2.
 intros; simpl in |- *; apply lookup_s.
 case a; clear a; intros; simpl in |- *.
   apply lookup_n; apply IHG2.
Qed.

Lemma lookup_skip1 : forall (G2 G1 : ctxt) (k : nat) (U : tp),
                     lookup k G1 U -> 
                     lookup (length G2 + k) (G2 ++ G1) U.
intro G2; induction G2.
 intros; simpl in |- *; assumption.
 intros G1 k U D; case a; clear a; simpl in |- *.
   intro T; apply lookup_n.
   apply IHG2; assumption.
Qed.

Lemma lookup_skip2 : forall (G2 G1 : ctxt) (k : nat) (U : tp),
                     lookup (length G2 + k) (G2 ++ G1) U ->
                     lookup k G1 U.
intro G2; induction G2.
 simpl in |- *; intros; assumption.
 case a; clear a; simpl in |- *; intros.
   apply IHG2.
   inversion H; assumption.
Qed.

Lemma lookup_start1 : forall (G2 G1 : ctxt) (x : nat) (U : tp),
                      x < length G2 -> 
                      lookup x (G2 ++ G1) U -> 
                      lookup x G2 U.
intro G2; induction G2.
 simpl in |- *; intros; elimtype False; omega.
 case a; clear a; simpl in |- *; intros.
   inversion H0.
  apply lookup_s.
  apply lookup_n.
    apply IHG2 with (G1 := G1); try assumption.
    subst x.
    omega.
Qed.

Lemma lookup_start2 : forall (G2 G1 : ctxt) (x : nat) (U : tp),
                      x < length G2 -> 
                      lookup x G2 U -> 
                      lookup x (G2 ++ G1) U.
intro G2; induction G2.
 simpl in |- *; intros; elimtype False; omega.
 case a; clear a; simpl in |- *; intros.
   inversion H0.
  apply lookup_s.
  apply lookup_n.
    apply IHG2; try assumption.
    omega.
Qed.

Lemma lookup_functional : forall (G : ctxt) (U1 U2 : tp) (n : nat),
                          lookup n G U1 -> 
                          lookup n G U2 -> 
                          U1 = U2.
intro G; induction G; intros U1 U2 n.
 intro H1; inversion H1.
 case a; clear a; intros T H1 H2.
   inversion H1; inversion H2; try congruence.
   apply IHG with (n := n1); try assumption.
   subst n.
   injection H7.
   intros; subst n0; assumption.
Qed.

Lemma lookup_greater : forall (G2 G1 : ctxt) (c n : nat) (U : tp),
                       lookup n (G2 ++ G1) U ->
                       n < length G2 -> 
                       ~ ctxt_const_in c G2 -> 
                       ~ const_in c U.
intro G2; induction G2.
 simpl in |- *; intros; elimtype False; omega.
 case a; clear a; simpl in |- *; intros.
   inversion H.
  subst U; tauto.
  apply IHG2 with (n := n0) (G1 := G1); try tauto.
    omega.
Qed.

Lemma lt_to_S : forall x y : nat, 
                x < y -> 
                exists z : nat, y - x = S z.
intros x y D; induction D.
 exists 0.
   omega.
 elim IHD; clear IHD; intros z D2.
   exists (S z); omega.
Qed.

Lemma lookup_ctxt_put_const : forall (G : ctxt) (c' c x : nat) (U : tp),
                           lookup x G U -> 
                           lookup x (ctxt_put_const c' c G) (put_const c' c U).
intro G; induction G.
 intros c' c x U D; inversion D.
 case a; clear a; simpl in |- *; intros.
   inversion H.
  apply lookup_s.
  apply lookup_n.
    apply IHG.
    assumption.
Qed.

(**********************************************************************)
(* consts_bounded                                                     *)
(**********************************************************************)

Fixpoint consts_bounded (n:nat) (T:tp) {struct T} : Prop :=
  match T with
  var x => True
| const x => x < n
| top => True
| T1 --> T2 => consts_bounded n T1 /\ consts_bounded n T2
| all x <: T1. T2 => consts_bounded n T1 /\ consts_bounded n T2
end.

Lemma consts_bounded_strengthen : forall (Q : tp) (m : nat),
                                  consts_bounded (S m) Q -> 
                                  ~ const_in m Q -> 
                                  consts_bounded m Q.
induction Q; simpl in |- *; intros m B C; try tauto || omega;
 (split; [ apply IHQ1 | apply IHQ2 ]; tauto).
Qed.

Lemma consts_bounded_graft : forall (Q : tp) (n :nat) (x : name),
                             consts_bounded (S n) Q ->
                             consts_bounded (S n) (graft_tp (const n) x Q).
intro Q; induction Q; simpl in |- *; intros m x B;
 [ case (eq_name_dec n x); simpl in |- *; intros; [ omega | trivial ]
 | omega
 | trivial
 | split
 | split ]; try (apply IHQ1; tauto).
 apply IHQ2; tauto.
 case (eq_name_dec n x); intros; try tauto.
   apply IHQ2; tauto.
Qed.

Lemma consts_bounded_graft2 : forall (Q : tp) (n :nat) (x : name),
                              consts_bounded (S n) (graft_tp (const n) x Q) ->
                              consts_bounded (S n) Q.
intro Q; induction Q; simpl in |- *; intros m x B;
 [ trivial | omega | trivial | split | split ];
 try (apply IHQ1 with (x := x); tauto); try (apply IHQ2 with (x := x); tauto).
generalize B; clear B; case (eq_name_dec n x); intros; try tauto.
apply IHQ2 with (x := x); tauto.
Qed.

Lemma consts_bounded_step : forall (Q : tp) (n : nat) (x : name),
                            ~ const_in n Q ->
                            consts_bounded (S n) (graft_tp (const n) x Q) ->
                            consts_bounded n Q.
intro Q; induction Q; simpl in |- *; intros m x C B; try tauto || omega;
 (repeat split;
   [ apply IHQ1 with (x := x); tauto
   | try (apply IHQ2 with (x := x); tauto) ]).
generalize B; clear B; case (eq_name_dec n x); intros;
 apply IHQ2 with (x := x); try tauto.
apply consts_bounded_graft; tauto.
Qed. 

Lemma consts_bounded_weaken : forall (T : tp) (x y : nat),
                              consts_bounded x T -> 
                              x <= y -> 
                              consts_bounded y T.
intro T; induction T; simpl in |- *; intros x y C L; try trivial || omega;
 (split; [ apply IHT1 with (x := x) | apply IHT2 with (x := x) ]); 
 tauto.
Qed.

Lemma consts_bounded_put_const : forall (c1 c2 c3 : nat) (T : tp),
                                 consts_bounded c1 T ->
                                 c2 < c1 -> 
                                 consts_bounded c1 (put_const c2 c3 T).
intros c1 c2 c3 T; induction T; simpl in |- *; try tauto.
case (eq_nat_dec c3 n); intro B; intros B1 B2; simpl in |- *; omega.
Qed.

Lemma consts_bounded_not_in : forall (U : tp) (n : nat), 
                              consts_bounded n U -> 
                              ~ const_in n U.
intro U; induction U; simpl in |- *; intros m D; try tauto || omega;
 assert (~ const_in m U1 /\ ~ const_in m U2); try tauto;
 (split; [ apply IHU1 | apply IHU2 ]; tauto).
Qed.

(**********************************************************************)
(* ctxt_consts_bounded                                                *)
(**********************************************************************)

Fixpoint ctxt_consts_bounded (G:ctxt) : Prop :=
  match G with
  G' ~:: (bound T) => consts_bounded (length G') T /\ ctxt_consts_bounded G'
| nil => True
end.

Lemma ctxt_consts_bounded_put_const : forall (G2 G1 : ctxt) (c' c : nat),
                            c' < length G1 ->
                            ctxt_consts_bounded (G2 ++ G1) ->
                            ctxt_consts_bounded (ctxt_put_const c' c G2 ++ G1).
intro G2; induction G2; simpl in |- *; intros G1 c' c; try tauto.
case a; clear a; simpl in |- *; intros; lain ipattern:H0; split.
 la; rewrite length_ctxt_put_const.
   apply consts_bounded_put_const; tauto || omega.
 apply IHG2; tauto || omega.
Qed.

Lemma permute_ctxt_consts_bounded : forall (G2 G1:ctxt) (U1 U2:tp), 
                   ctxt_consts_bounded (G2 ++ bound U2 :: bound U1 :: G1) ->
                   ~ const_in (length G1) U2 -> 
                   ctxt_consts_bounded (G2 ++ bound U1 :: bound U2 :: G1).
intro G2; induction G2.
 simpl in |- *; intros; repeat split; try tauto.
  apply consts_bounded_weaken with (x := length G1); tauto || omega.
  apply consts_bounded_strengthen; tauto.
 case a; clear a.
   simpl in |- *; intros.
   split.
  lain H; la; simpl in *; tauto.
  apply IHG2; tauto.
Qed.

Lemma ctxt_consts_bounded_not_in1 : forall (G2 G1 : ctxt)(n : nat)(U2 U1 : tp),
                    ctxt_consts_bounded (G2 ++ bound U2 :: bound U1 :: G1) ->
                    n >= length G1 -> 
                    ~ const_in n U1.
intro G2; induction G2; intros G1 n U2 U1.
 simpl in |- *; intros.
   apply consts_bounded_not_in.
   apply consts_bounded_weaken with (x := length G1).
  tauto.
  omega.
 case a; clear a.
   simpl in |- *; intros.
   elim H; clear H; intros Ha Hb.
   exact (IHG2 G1 n U2 U1 Hb H0).
Qed.

Lemma ctxt_consts_bounded_not_in2 : forall (x : nat) (G : ctxt) (U : tp),
                                    lookup x G U ->
                                    ctxt_consts_bounded G ->
                                    forall y : nat, 
                                    y >= length G ->
                                    ~ const_in y U.
intros x G U D; induction D; simpl in |- *; intro H; elim H; clear H;
 intros Ha Hb.
 intros; apply consts_bounded_not_in.
   apply consts_bounded_weaken with (x := length G).
  assumption.
  omega.
 intros.
   apply IHD.
  assumption.
  omega.
Qed.

Lemma lookup_const_not_in : forall (G2 G1 : ctxt) (x : nat) (U : tp),
                            x < length G1 ->
                            lookup (length G1 - 1 - x) G1 U ->
                            ctxt_consts_bounded (G2 ++ G1) ->
                            ~ const_in (length G1) U.
intro G2; induction G2; intros G1 x U B L.
 simpl in |- *; intro C.
   apply ctxt_consts_bounded_not_in2 with (x := length G1 - 1 - x) (G := G1);
    try assumption.
   omega.
 case a; clear a; simpl in |- *.
   intros T H; elim H; clear H; intros Ha Hb.
   apply IHG2 with (x := x); assumption.
Qed.

Lemma ctxt_consts_bounded_weaken : forall G2 G1 : ctxt,
                                   ctxt_consts_bounded (G2 ++ G1) -> 
                                   ctxt_consts_bounded G1.
intro G2; induction G2; intro G1.
 simpl in |- *; tauto.
 case a; clear a; simpl in |- *; intros.
   apply IHG2; tauto.
Qed.

Lemma ctxt_consts_bounded_change : forall (G1 G2 : ctxt) (P Q : tp),
                                 ctxt_consts_bounded (G1 ~:: bound Q ~++ G2) ->
                                 consts_bounded (length G1) P ->
                                 ctxt_consts_bounded (G1 ~:: bound P ~++ G2).
intros G1 G2 P Q; induction G2; simpl in |- *; try tauto; case a; clear a; la;
 simpl in |- *; intros; split; try tauto.
Qed.

(**********************************************************************)
(* subtyping                                                          *)
(**********************************************************************)

Reserved Notation "G |- Q <:: T" (at level 70, no associativity).

Inductive subtp : ctxt -> tp -> tp -> Prop :=
  sa_top : forall (G : ctxt) (Q : tp),
           consts_bounded (length G) Q ->
           ctxt_consts_bounded G -> 
           is_ground Q ->
           ctxt_is_ground G ->
	   G |- Q <:: top
| sa_refl_tvar : forall (G : ctxt) (x:nat),
                 ctxt_consts_bounded G ->
                 ctxt_is_ground G ->
                 x < length G ->
                 G |- (const x) <:: (const x)
| sa_trans_tvar : forall (G : ctxt) (x:nat) (T U : tp),
                  lookup (length G - 1 - x) G U ->
		  x < length G ->
                  G |- U <:: T -> 
                  G |- (const x) <:: T
| sa_arrow : forall (G:ctxt) (Q1 Q2 T1 T2:tp),
	     G |- T1 <:: Q1 ->
	     G |- Q2 <:: T2 ->
	     G |- (Q1 --> Q2) <:: (T1 --> T2)
| sa_all : forall (G:ctxt) (x1 x2 : name) (Q1 Q2 T1 T2 : tp),
           G |- T1 <:: Q1 ->
           ~ const_in (length G) Q2 ->
           ~ const_in (length G) T2 ->
           (G ~:: (bound T1)) |- (graft_tp (const (length G)) x1 Q2)
                                   <:: (graft_tp (const (length G)) x2 T2) ->
           G |- (all x1 <: Q1 . Q2) <:: (all x2 <: T1 . T2)

where "G |- Q <:: T" := (subtp G Q T).

(**********************************************************************)
(* subtp_ground, subtp_consts_bounded, etc.                           *)
(**********************************************************************)
Lemma subtp_ground : forall (G : ctxt) (S T : tp),
                     G |- S <:: T -> 
                     is_ground S /\ is_ground T.
unfold is_ground in |- *; intros G S T D; induction D; simpl in |- *;
 repeat split; try tauto;
 [ assert (R : x1 :: nil = nil ++ x1 :: nil)
 | assert (R : x2 :: nil = nil ++ x2 :: nil) ]; try (simpl in |- *; trivial);
 rewrite R; apply is_ground_h_extend with (c := length G); 
 simpl in |- *; tauto.
Qed.

Lemma subtp_ground1 : forall (G : ctxt) (S T : tp), 
                      G |- S <:: T -> 
                      is_ground S.
exact (fun G S T H => proj1 (subtp_ground G S T H)).
Qed.

Lemma subtp_ground2 : forall (G : ctxt) (S T : tp), 
                      G |- S <:: T -> 
                      is_ground T.
exact (fun G S T H => proj2 (subtp_ground G S T H)).
Qed.

Lemma subtp_consts_bounded : forall (G : ctxt) (S T : tp),
                    G |- S <:: T -> 
                    consts_bounded (length G) S /\ consts_bounded (length G) T.
intros G S T D; induction D; simpl in |- *; repeat split; try tauto.
 apply consts_bounded_step with (x := x1); tauto.
 apply consts_bounded_step with (x := x2); tauto.
Qed.

Lemma subtp_consts_bounded1 : forall (G : ctxt) (S T : tp), 
                              G |- S <:: T -> 
                              consts_bounded (length G) S.
exact (fun G S T H => proj1 (subtp_consts_bounded G S T H)).
Qed.

Lemma subtp_consts_bounded2 : forall (G : ctxt) (S T : tp), 
                              G |- S <:: T -> 
                              consts_bounded (length G) T.
exact (fun G S T H => proj2 (subtp_consts_bounded G S T H)).
Qed.

Lemma subtp_ctxt_consts_bounded : forall (G : ctxt) (T U : tp),
                                  G |- T <:: U -> 
                                  ctxt_consts_bounded G.
intros G T U D; induction D; tauto.
Qed.

Lemma subtp_ctxt_is_ground : forall (G : ctxt) (T U : tp), 
                             G |- T <:: U -> 
                             ctxt_is_ground G.
intros G T U D; induction D; tauto.
Qed.

(**********************************************************************)
(* permutation for subtyping                                          *)
(**********************************************************************)
Ltac ctxt_ground_permute := apply ctxt_is_ground_put_const_append;
    apply ctxt_is_ground_permute; assumption.

Ltac lax := la; rewrite length_ctxt_put_const; simpl.
Ltac laxo := lax; omega.

Lemma permutation_subtp : forall (G:ctxt)(Q T U1 U2:tp),
                          G |- Q <:: T ->
                          forall (G1 G2:ctxt), 
                          G = G1 ~:: bound U1 ~:: bound U2 ~++ G2 ->
                          ~ const_in (S (length G1)) Q ->
                          ~ const_in (S (length G1)) T ->
                          ~ const_in (length G1) U2 ->
                          ~ ctxt_const_in (S (length G1)) G2 ->
                          let G2' := ctxt_put_const (S (length G1)) 
                                       (length G1) G2 in
                          let G' := G1 ~:: bound U2 ~:: bound U1 ~++ G2' in
                          G' |- put_const (S (length G1)) (length G1) Q
                            <:: put_const (S (length G1)) (length G1) T.
intros G Q T U1 U2 D; induction D; simpl in |- *;
 intros G1 G2 EG cQ cT cU2 cG2; subst G.

(* sa_top *)

 apply sa_top.
  lain H; simpl in H; lax.
    apply consts_bounded_put_const; assumption || omega.
  apply ctxt_consts_bounded_put_const; simpl in |- *.
   omega.
   apply permute_ctxt_consts_bounded; assumption.
  apply is_ground_put_const; assumption.
  ctxt_ground_permute.

(* sa_refl_tvar *)

 lain H1; case (eq_nat_dec (length G1) x);
  (intro B; apply sa_refl_tvar; la; simpl in *;
    [ idtac | ctxt_ground_permute | rewrite length_ctxt_put_const; omega ]);
  (apply ctxt_consts_bounded_put_const;
    [ simpl in |- *; omega | apply permute_ctxt_consts_bounded; assumption ]).

(* sa_trans_tvar *)

 case (eq_nat_dec (length G1) x); intro B.
  subst x.
    clear H0 cQ.
    lain H; simpl in H.
    assert (length G2 + S (S (length G1)) - 1 - length G1 = S (length G2)).
   omega.
   rewrite H0 in H.
     clear H0.
     assert
      (G2 ++ bound U2 :: bound U1 :: G1 =
       (G2 ++ bound U2 :: nil) ++ bound U1 :: G1).
    rewrite app_ass; simpl; trivial.
    rewrite H0 in H.
      assert (S (length G2) = length (G2 ++ bound U2 :: nil)).
     la; simpl in |- *; omega.
     rewrite H1 in H.
       clear H0 H1.
       assert
        (lookup (length (G2 ++ bound U2 :: nil))
           ((G2 ++ bound U2 :: nil) ++ bound U1 :: G1) U1).
      apply lookup_skip.
      assert (U = U1).
       apply
        (lookup_functional ((G2 ++ bound U2 :: nil) ++ bound U1 :: G1) U U1
           (length (G2 ++ bound U2 :: nil)) H H0).
       subst U.
         apply sa_trans_tvar with (U := U1).
        lax.
          assert
           (length G2 + S (S (length G1)) - 1 - S (length G1) = length G2).
         omega.
         rewrite H1; clear H1.
           assert
            (length G2 =
             length (ctxt_put_const (S (length G1)) (length G1) G2)).
          rewrite length_ctxt_put_const; trivial.
          rewrite H1.
            apply lookup_skip.
        laxo.
        assert (U1 = put_const (S (length G1)) (length G1) U1).
         assert (put_const (S (length G1)) (length G1) U1 = U1).
          apply put_const_not_in.
            assert (ctxt_consts_bounded (G2 ++ bound U2 :: bound U1 :: G1)).
           apply subtp_ctxt_consts_bounded with (T := U1) (U := T);
            assumption.
           apply (ctxt_consts_bounded_not_in1 G2 G1 (length G1) U2 U1).
            assumption.
            omega.
          congruence.
         pattern U1 at 2 in |- *.
           rewrite H1; clear H1.
           apply IHD; try tauto.
           assert (ctxt_consts_bounded (G2 ++ bound U2 :: bound U1 :: G1)).
          apply subtp_ctxt_consts_bounded with (T := U1) (U := T); assumption.
          apply (ctxt_consts_bounded_not_in1 G2 G1 (S (length G1)) U2 U1).
           assumption.
           omega.
  lain H0; simpl in H0; lain H; simpl in H.
    assert (x < length G1 \/ x = S (length G1) \/ x > S (length G1)).
   omega.
   elim H1; clear H1; intro H1.
    apply sa_trans_tvar with (U := U).
     assert
      (ctxt_put_const (S (length G1)) (length G1) G2 ++
       bound U1 :: bound U2 :: G1 =
       (ctxt_put_const (S (length G1)) (length G1) G2 ++
        bound U1 :: bound U2 :: nil) ++ G1).
      rewrite app_ass; trivial.
      rewrite H2; clear H2.
        assert
         (length
            ((ctxt_put_const (S (length G1)) (length G1) G2 ++
              bound U1 :: bound U2 :: nil) ++ G1) - 1 - x =
          length
            (ctxt_put_const (S (length G1)) (length G1) G2 ++
             bound U1 :: bound U2 :: nil) + (length G1 - 1 - x)).
       laxo.
       rewrite H2; clear H2.
         apply lookup_skip1.
         apply lookup_skip2 with (G2 := G2 ++ bound U2 :: bound U1 :: nil).
         la; rewrite app_ass; simpl in |- *.
         assert
          (length G2 + 2 + (length G1 - 1 - x) =
           length G2 + S (S (length G1)) - 1 - x).
        omega.
        rewrite H2; clear H2; assumption.
     laxo.
     assert (lookup (length G1 - 1 - x) G1 U).
      apply lookup_skip2 with (G2 := G2 ++ bound U2 :: bound U1 :: nil).
        la; rewrite app_ass; simpl in |- *.
        assert
         (length G2 + 2 + (length G1 - 1 - x) =
          length G2 + S (S (length G1)) - 1 - x).
       omega.
       rewrite H2; clear H2; assumption.
      assert (~ const_in (length G1) U).
       apply
        lookup_const_not_in
         with (G2 := G2 ++ bound U2 :: bound U1 :: nil) (x := x);
        try assumption.
         rewrite app_ass; simpl in |- *.
         apply subtp_ctxt_consts_bounded with (T := U) (U := T); assumption.
       rewrite <- (put_const_not_in U (S (length G1)) (length G1) H3).
         apply IHD; try tauto.
         apply
          ctxt_consts_bounded_not_in2 with (x := length G1 - 1 - x) (G := G1);
          try tauto || omega.
         apply
          ctxt_consts_bounded_weaken
           with (G2 := G2 ++ bound U2 :: bound U1 :: nil).
         rewrite app_ass; simpl in |- *;
          apply subtp_ctxt_consts_bounded with (T := U) (U := T); 
          assumption.
    clear B; elim H1; clear H1; intro H1.
     subst x; elim cQ; trivial.
     apply
        sa_trans_tvar with (U := put_const (S (length G1)) (length G1) U).
      lax; apply lookup_start2.
       rewrite length_ctxt_put_const; omega.
       apply lookup_ctxt_put_const.
         apply lookup_start1 with (G1 := bound U2 :: bound U1 :: G1).
        omega.
        assumption.
      laxo.
      apply IHD; try assumption.
       trivial.
       apply
        lookup_greater
         with
           (G2 := G2)
           (G1 := bound U2 :: bound U1 :: G1)
           (n := length G2 + S (S (length G1)) - 1 - x); 
        assumption || omega.

(* sa_arrow *)

 apply sa_arrow; [ apply IHD1 | apply IHD2 ]; try tauto.

(* sa_all *)

 apply sa_all.
  apply IHD1; tauto.
  lax; intro.
    assert
     (A :
      const_in (length G2 + S (S (length G1))) Q2 \/
      length G2 + S (S (length G1)) = S (length G1)).
   apply const_in_put_const with (c3 := length G1); assumption.
   elim A; clear A; intro A; [ lain H; tauto | omega].
  lax; intro.
    assert
     (A :
      const_in (length G2 + S (S (length G1))) T2 \/
      length G2 + S (S (length G1)) = S (length G1)).
   apply const_in_put_const with (c3 := length G1); assumption.
   elim A; clear A; intro A; [ lain H0; tauto | omega].
  lain IHD2; simpl in IHD2; la; simpl in |- *.
    assert (length G2 + S (S (length G1)) <> length G1); try omega.
    repeat rewrite length_ctxt_put_const.
    rewrite
     (commute_graft_put_const (length G2 + S (S (length G1))) 
        (S (length G1)) (length G1) x1 Q2 H1).
    rewrite
     (commute_graft_put_const (length G2 + S (S (length G1))) 
        (S (length G1)) (length G1) x2 T2 H1).
    assert
     (R :
      bound (put_const (S (length G1)) (length G1) T1)
      :: ctxt_put_const (S (length G1)) (length G1) G2 ++
         bound U1 :: bound U2 :: G1 =
      ctxt_put_const (S (length G1)) (length G1) (bound T1 :: G2) ++
      bound U1 :: bound U2 :: G1).
   simpl in |- *; trivial.
   rewrite R; apply IHD2; simpl in |- *; try tauto; intro Z;
      [ assert
         (A :
          const_in (S (length G1)) Q2 \/
          S (length G1) = length G2 + S (S (length G1)));
         try (apply const_in_graft with (x := x1); tauto)
      | assert
         (A :
          const_in (S (length G1)) T2 \/
          S (length G1) = length G2 + S (S (length G1)));
         try (apply const_in_graft with (x := x2); tauto) ]; 
      elim A; try tauto || omega.
Qed.

(**********************************************************************)
(* weakening for subtyping                                            *)
(**********************************************************************)
Lemma weaken_subtp : forall (U:tp) (G:ctxt) (T Q : tp),
                     is_ground U ->
                     G |- T <:: Q ->
                     consts_bounded (length G) U ->
                     G ~:: (bound U) |- T <:: Q.
intros U G T Q iG D; induction D; simpl in |- *; intros.
 apply sa_top; try (simpl in |- *; tauto).
   apply consts_bounded_weaken with (x := length G);
    [ assumption | simpl in |- *; omega ].
 apply sa_refl_tvar; try (simpl in |- *; tauto || omega).
 apply sa_trans_tvar with (U := U0); try (simpl in |- *; tauto || omega).
   assert (length (bound U :: G) - 1 - x = S (length G - 1 - x)).
  simpl in |- *; omega.
  rewrite H2; apply lookup_n; assumption.
 apply sa_arrow; tauto.
 apply sa_all.
  tauto.
  simpl in |- *.
    apply consts_bounded_not_in.
    apply consts_bounded_graft2 with (x := x1).
    assert (S (length G) = length (bound T1 :: G));
     try (simpl in |- *; trivial).
    rewrite H2; clear H2.
    apply subtp_consts_bounded1 with (T := graft_tp (const (length G)) x2 T2).
    assumption.
  simpl in |- *.
    apply consts_bounded_not_in.
    apply consts_bounded_graft2 with (x := x2).
    assert (S (length G) = length (bound T1 :: G));
     try (simpl in |- *; trivial).
    rewrite H2; clear H2.
    apply subtp_consts_bounded2 with (S := graft_tp (const (length G)) x1 Q2).
    assumption.
  simpl in |- *;
   assert
    (bound T1 :: bound U :: G =
     ctxt_put_const (S (length G)) (length G) nil ++ bound T1 :: bound U :: G);
   try (simpl in |- *; trivial).
    rewrite H2; clear H2.
    rewrite <- (put_const_graft (S (length G)) (length G) x1 Q2 H).
    rewrite <- (put_const_graft (S (length G)) (length G) x2 T2 H0).
    apply permutation_subtp with (G := nil ++ bound U :: bound T1 :: G);
     simpl in |- *; try tauto.
   apply IHD2.
     simpl in |- *; apply consts_bounded_weaken with (x := length G);
      [ assumption | omega ].
   assert
    (consts_bounded (length (bound T1 :: G))
       (graft_tp (const (length G)) x1 Q2)).
    apply subtp_consts_bounded1 with (T := graft_tp (const (length G)) x2 T2);
     assumption.
    apply consts_bounded_not_in; assumption.
   assert
    (consts_bounded (length (bound T1 :: G))
       (graft_tp (const (length G)) x2 T2)).
    apply subtp_consts_bounded2 with (S := graft_tp (const (length G)) x1 Q2);
     assumption.
    apply consts_bounded_not_in; assumption.
   apply consts_bounded_not_in; assumption.
Qed.

Lemma multi_weaken_subtp : forall (T Q : tp) (G2:ctxt),
                           G2 |- T <:: Q ->
                           forall (G1:ctxt),
                           ctxt_is_ground G1 ->
                           ctxt_consts_bounded (G2 ~++ G1) ->
                           G2 ~++ G1 |- T <:: Q.
intros T Q G2 D G1; induction G1.
 simpl in |- *; tauto.
 case a; clear a; simpl in |- *; intros.
   apply weaken_subtp; tauto.
Qed.

(**********************************************************************)
(* transitivity of subtyping, narrowing of subtyping                  *)
(**********************************************************************)
Section tn_sec.

Let trans_stmt(Q:tp) := 
  (forall (G:ctxt) (S T : tp), 
      G |- S <:: Q -> 
      G |- Q <:: T -> 
      G |- S <:: T).

Let narrow_stmt(Q:tp) :=
  (forall (G:ctxt) (M N : tp),
                   G |- M <:: N ->
                   forall (G1 G2 : ctxt) (P : tp),
                   G = G1 ~:: bound Q ~++ G2 -> 
                   G1 |- P <:: Q -> 
                   G1 ~:: bound P ~++ G2 |- M <:: N).

(* The lemmas are structured here following Vouillon's development. *)

Lemma transitivity_case: forall Q:tp,
                         (forall Q':tp, size Q' < size Q -> trans_stmt(Q')) ->
                         (forall Q':tp, size Q' < size Q -> narrow_stmt(Q')) ->
                         trans_stmt(Q).
intros Q TransH NarrowH; unfold trans_stmt in |- *; intros G S T D1 D2;
 induction D1.
 inversion D2.
   apply sa_top; try tauto.
 assumption.
 apply sa_trans_tvar with (U := U); try tauto.
 inversion D2.
  apply sa_top; unfold is_ground in |- *; simpl in |- *; try tauto; split.
   apply subtp_consts_bounded2 with (S := T1); assumption.
   apply subtp_consts_bounded1 with (T := T2); assumption.
   fold (is_ground Q1) in |- *.
     apply subtp_ground2 with (G := G) (S := T1); assumption.
   fold (is_ground Q2) in |- *; apply subtp_ground1 with (G := G) (T := T2);
    assumption.
  unfold trans_stmt in TransH; apply sa_arrow;
   [ apply TransH with (Q' := T1) | apply TransH with (Q' := T2) ]; 
   try tauto; simpl in |- *; omega.
 inversion D2.
  apply sa_top; try assumption; unfold is_ground in |- *; simpl in |- *;
   split.
   apply subtp_consts_bounded2 with (S := T1) (G := G); assumption.
   assert
    (consts_bounded (length (G ~:: bound T1))
       (graft_tp (const (length G)) x1 Q2)).
    apply subtp_consts_bounded1 with (T := graft_tp (const (length G)) x2 T2);
     assumption.
    simpl in H8.
      apply consts_bounded_step with (x := x1); assumption.
   fold (is_ground Q1) in |- *; apply subtp_ground2 with (G := G) (S := T1);
    assumption.
   fold (nil ~:: x1 ~++ nil) in |- *;
    apply is_ground_h_extend with (c := length G); 
    simpl in |- *.
     apply
      subtp_ground1
       with (G := G ~:: bound T1) (T := graft_tp (const (length G)) x2 T2);
      assumption.
  clear H5 G0 H1 x0 H2 Q0 H3 Q3.
    rename x2 into y.
    rename x3 into x2.
    rename T1 into S1.
    rename T0 into T1.
    rename T2 into S2.
    rename T3 into T2.
    apply sa_all; try tauto.
   unfold trans_stmt in TransH; apply TransH with (Q' := S1); try assumption;
    simpl in |- *; omega.
   unfold narrow_stmt in NarrowH.
     assert
      (G ~:: bound T1 |- graft_tp (const (length G)) x1 Q2 <::
       graft_tp (const (length G)) y S2).
    fold (G ~:: bound T1 ~++ nil) in |- *;
     apply NarrowH with (Q' := S1) (G := G ~:: bound S1 ~++ nil);
     try assumption; simpl in |- *; reflexivity || omega.
    unfold trans_stmt in TransH;
     apply TransH with (Q' := graft_tp (const (length G)) y S2);
     try assumption.
      rewrite size_graft_const; simpl in |- *; omega.
Qed.

Lemma narrow_case: forall Q : tp,
                   (forall Q' : tp, size Q' = size Q -> trans_stmt Q') ->
                   narrow_stmt(Q).
intros Q TransH G M N D1; induction D1; intros G1 G2 P E; subst G; intro D2.
 apply sa_top; try assumption.
  lain H; simpl in H; la; simpl in |- *; assumption.
  apply ctxt_consts_bounded_change with (Q := Q); try assumption.
    apply subtp_consts_bounded1 with (T := Q); assumption.
  apply ctxt_is_ground_change with (Q := Q); try assumption.
    apply subtp_ground1 with (G := G1) (T := Q); assumption.
 apply sa_refl_tvar;
  [ apply ctxt_consts_bounded_change with (Q := Q);
     [ assumption | apply subtp_consts_bounded1 with (T := Q); assumption ]
  | apply ctxt_is_ground_change with (Q := Q);
     [ assumption | apply subtp_ground1 with (G := G1) (T := Q); assumption ]
  | lain H1; simpl in H1; la; simpl in |- *; omega ].
 assert (x = length G1 \/ x < length G1 \/ x > length G1); try omega.
   elim H1; clear H1; intro H1.
  subst x.
    clear H0.
    assert
     (lookup (length (G1 ~:: bound Q ~++ G2) - 1 - length G1)
        (G1 ~:: bound Q ~++ G2) Q).
   la; simpl in |- *.
     assert (length G2 + S (length G1) - 1 - length G1 = length G2);
      try omega.
     rewrite H0.
     apply lookup_skip.
   assert (U = Q).
    exact
     (lookup_functional (G1 ~:: bound Q ~++ G2) U Q
        (length (G1 ~:: bound Q ~++ G2) - 1 - length G1) H H0).
    subst U.
      apply sa_trans_tvar with (U := P).
     assert (length (G1 ~:: bound P ~++ G2) - 1 - length G1 = length G2);
      try (la; simpl in |- *; omega).
       rewrite H1.
       apply lookup_skip.
     la; simpl in |- *; omega.
     assert (G1 ~:: bound P ~++ G2 |- Q <:: T).
      apply IHD1; tauto.
      assert (G1 ~:: bound P ~++ G2 |- P <:: Q).
       apply multi_weaken_subtp.
        apply weaken_subtp.
         apply subtp_ground1 with (G := G1) (T := Q); assumption.
         assumption.
         apply subtp_consts_bounded1 with (T := Q); assumption.
        assert (ctxt_is_ground (G1 ~:: bound P ~++ G2)).
         apply (subtp_ctxt_is_ground (G1 ~:: bound P ~++ G2) Q T H1).
         exact (proj2 (ctxt_is_ground_split (G1 ~:: bound P) G2 H2)).
        apply subtp_ctxt_consts_bounded with (T := Q) (U := T).
          assumption.
       unfold trans_stmt in TransH.
         apply TransH with (Q' := Q); omega || tauto.
  lain H; lain H0; simpl in *; elim H1; clear H1; intro H1;
   (apply sa_trans_tvar with (U := U);
     [ idtac
     | la; simpl in |- *; omega
     | apply IHD1; try assumption || trivial ]); la; 
   simpl in |- *.
   assert
    (length G2 + S (length G1) - 1 - x = length G2 + (S (length G1) - 1 - x)).
    clear H0; omega.
    rewrite H2.
      apply lookup_skip1.
      clear H2.
      assert (exists z : nat, S (length G1) - S x = S z).
     apply lt_to_S.
       omega.
     elim H2; clear H2; intros z H2.
       assert (S (length G1) - 1 - x = S (length G1) - S x).
      omega.
      rewrite H3; clear H3.
        rewrite H2; apply lookup_n.
        apply lookup_skip2 with (G2 := nil ~:: bound Q ~++ G2).
        la; simpl in |- *.
        assert (length G2 + 1 + z = length G2 + S z); try omega.
        rewrite H3.
        rewrite <- H2.
        assert
         (length G2 + (S (length G1) - S x) =
          length G2 + S (length G1) - 1 - x).
       omega.
       rewrite H4.
         assert (G1 ~++ (nil ~:: bound Q ~++ G2) = G1 ~:: bound Q ~++ G2).
        rewrite app_ass.
          simpl in |- *.
          trivial.
        rewrite H5.
          assumption.
   apply lookup_start2.
    omega.
    apply lookup_start1 with (G1 := G1 ~:: bound Q).
     omega.
     assumption.
 apply sa_arrow; [ apply IHD1_1 | apply IHD1_2 ]; try tauto.
 apply sa_all.
  apply IHD1_1; tauto.
  lain H; simpl in H; la; simpl in |- *; assumption.
  lain H0; simpl in H0; la; simpl in |- *; assumption.
  assert (length (G1 ~:: bound P ~++ G2) = length (G1 ~:: bound Q ~++ G2));
   try (la; simpl in |- *; reflexivity).
    assert
     (G1 ~:: bound P ~++ G2 ~:: bound T1 =
      G1 ~:: bound P ~++ (G2 ~:: bound T1)).
   simpl in |- *; reflexivity.
   rewrite H1; rewrite H2; apply IHD1_2; simpl in |- *; tauto.
Qed.

Lemma both_at_once : forall (n : nat) (Q : tp),
                     size Q <= n -> 
                     trans_stmt Q /\ narrow_stmt Q.
intro n; induction n; intros Q sQ.
 assert (size Q > 0); [ apply size_non_zero | elimtype False; omega ].
 split.
  apply transitivity_case; intros; assert (trans_stmt Q' /\ narrow_stmt Q');
   try tauto; apply IHn; omega.
  apply narrow_case.
    intros.
    apply transitivity_case; intros Q1 sQ1;
     assert (trans_stmt Q1 /\ narrow_stmt Q1); try tauto; 
     apply IHn; omega.
Qed.

Theorem transitivity_subtp : forall (G : ctxt) (S Q T : tp),
                             G |- S <:: Q -> 
                             G |- Q <:: T -> 
                             G |- S <:: T.
intros G S Q; generalize G S; clear G S.
refine (proj1 (both_at_once (size Q) Q _)); omega.
Qed.

End tn_sec.
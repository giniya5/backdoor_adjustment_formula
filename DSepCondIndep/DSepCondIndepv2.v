From CausalDiagrams Require Import IntermediateNodes.
From CausalDiagrams Require Import DSeparation.
From CausalDiagrams Require Import Interventions.
From CausalDiagrams Require Import Assignments.
From DAGs Require Import Basics.
From DAGs Require Import CycleDetection.
From DAGs Require Import Descendants.
From DAGs Require Import PathFinding.
From Semantics Require Import FunctionRepresentation FindValue EquateValues.
From Utils Require Import Lists.
From Utils Require Import Logic.
From Experiment Require Import Main.
From Experiment Require Import Prob.
From CondIndep Require Import RandomVariableDef.
From CondIndep Require Import MarkovFactorization.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From mathcomp Require Import all_ssreflect ssralg ssrnum finalg reals matrix.
From infotheo Require Import ssr_ext ssralg_ext fdist proba.
Import Order.POrderTheory Order.TotalTheory GRing.Theory Num.Theory.

Import ListNotations.

(* ================================================================== *)
(* PLAN                                                                *)
(*                                                                     *)
(* dsep_implies_cond_indep  =  Lemma P  o  Lemma B                     *)
(*                                                                     *)
(*   Lemma B (graph only):                                             *)
(*     d_separated_bool X Y G S = true                                 *)
(*       ==> S separates X from Y in the moral graph of G[An(X,Y,S)]   *)
(*   Lemma P (probability only):                                       *)
(*     S separates X from Y in the moral graph of G[An(X,Y,S)]         *)
(*       ==> nodeRV X _|_ nodeRV Y | setRV S                           *)
(*                                                                     *)
(* Lemma P is assembled from:                                          *)
(*   1. pfwd1_ancestral          marginal law on an ancestral set      *)
(*   2. factor_split             the product splits across S           *)
(*   3. cinde_of_factorization   g(x,z) * h(y,z)  ==>  cond. indep.    *)
(*                                                                     *)
(* NOTE: nothing in this file has been compiled yet.                   *)
(* ================================================================== *)

(* ------------------------------------------------------------------ *)
(* Generic: a factorization g(x,z) * h(y,z) gives conditional          *)
(* independence.  No graphs involved.                                  *)
(* ------------------------------------------------------------------ *)
Section CIndepFactorization.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope ring_scope.

Variable R : realType.
Variable U : finType.
Variable P : R.-fdist U.
Variables A B C : finType.
Variable X : {RV P -> A}.
Variable Y : {RV P -> B}.
Variable Z : {RV P -> C}.

(* Proof sketch: with J = Pr[X=x,Y=y,Z=z] = g x z * h y z,
     Pr[X=x,Z=z] = g x z * sum_y h y z
     Pr[Y=y,Z=z] = h y z * sum_x g x z
     Pr[Z=z]     = (sum_x g x z) * (sum_y h y z)
   and the cross-multiplied identity follows.  (Check that the notation
   [P |= X _|_ Y | Z] matches your infotheo version.) *)
Lemma cinde_of_factorization (g : A -> C -> R) (h : B -> C -> R) :
  (forall x y z, `Pr[ [% X, Y, Z] = (x, y, z) ] = g x z * h y z) ->
  P |= X _|_ Y | Z.
Proof.
move=> H.
(* ---- events as sums over the sample space ---- *)
have E3 : forall x y z, `Pr[ [% X, Y, Z] = (x, y, z) ]
    = \sum_(u | ((X u == x) && (Y u == y)) && (Z u == z)) P u.
  by move=> x y z; rewrite pfwd1E /Pr; apply: eq_bigl => u;
     rewrite !inE /= !xpair_eqE.
have E2x : forall x z, `Pr[ [% X, Z] = (x, z) ]
    = \sum_(u | (X u == x) && (Z u == z)) P u.
  by move=> x z; rewrite pfwd1E /Pr; apply: eq_bigl => u;
     rewrite !inE /= xpair_eqE.
have E2y : forall y z, `Pr[ [% Y, Z] = (y, z) ]
    = \sum_(u | (Y u == y) && (Z u == z)) P u.
  by move=> y z; rewrite pfwd1E /Pr; apply: eq_bigl => u;
     rewrite !inE /= xpair_eqE.
have E1 : forall z, `Pr[ Z = z ] = \sum_(u | Z u == z) P u.
  by move=> z; rewrite pfwd1E /Pr; apply: eq_bigl => u; rewrite !inE.
(* ---- marginalisation: split a sum according to the value of Y / X ---- *)
have mx : forall x z, `Pr[ [% X, Z] = (x, z) ]
    = \sum_(y : B) `Pr[ [% X, Y, Z] = (x, y, z) ].
  move=> x z; rewrite E2x (partition_big Y xpredT) //=.
  apply: eq_bigr => y _; rewrite E3; apply: eq_bigl => u.
  by case: (X u == x); case: (Y u == y); case: (Z u == z).
have my : forall y z, `Pr[ [% Y, Z] = (y, z) ]
    = \sum_(x : A) `Pr[ [% X, Y, Z] = (x, y, z) ].
  move=> y z; rewrite E2y (partition_big X xpredT) //=.
  apply: eq_bigr => x _; rewrite E3; apply: eq_bigl => u.
  by case: (X u == x); case: (Y u == y); case: (Z u == z).
have pz : forall z, `Pr[ Z = z ] = \sum_(x : A) `Pr[ [% X, Z] = (x, z) ].
  move=> z; rewrite E1 (partition_big X xpredT) //=.
  apply: eq_bigr => x _; rewrite E2x; apply: eq_bigl => u.
  by case: (X u == x); case: (Z u == z).
(* ---- the final field identity (also covers a zero denominator) ---- *)
have alg : forall x y s t : R,
    (x * y) / (s * t) = (x * t) / (s * t) * ((s * y) / (s * t)).
  move=> x y s t; case: (eqVneq (s * t) 0) => [H0 | Hd].
  - by rewrite H0 !invr0 !mulr0.
  - rewrite mulf_div.
    have -> : x * t * (s * y) = x * y * (s * t).
      by rewrite [x * t]mulrC (mulrACA t x s y) [t * s]mulrC; exact: mulrC.
    by rewrite -(mulf_div (x * y) (s * t) (s * t) (s * t)) divff // mulr1.
move=> a b c.
(* ---- the three marginals in terms of g and h ---- *)
have e1 : forall x, `Pr[ [% X, Z] = (x, c) ] = g x c * \sum_(y : B) h y c.
  move=> x; rewrite mx.
  rewrite (eq_bigr (fun y => g x c * h y c)); last by move=> y _; exact: H x y c.
  by rewrite -big_distrr.
have e2 : forall y, `Pr[ [% Y, Z] = (y, c) ] = (\sum_(x : A) g x c) * h y c.
  move=> y; rewrite my.
  rewrite (eq_bigr (fun x => g x c * h y c)); last by move=> x _; exact: H x y c.
  by rewrite -big_distrl.
have e3 : `Pr[ Z = c ] = (\sum_(x : A) g x c) * (\sum_(y : B) h y c).
  rewrite pz.
  rewrite (eq_bigr (fun x => g x c * \sum_(y : B) h y c));
    last by move=> x _; exact: e1 x.
  by rewrite -big_distrl.
(* ---- unfold the conditional probabilities ---- *)
have kXY : `Pr[ [% X, Y] = (a, b) | Z = c ]
         = `Pr[ [% X, Y, Z] = (a, b, c) ] / `Pr[ Z = c ] by rewrite cpr_eqE.
have kX : `Pr[ X = a | Z = c ] = `Pr[ [% X, Z] = (a, c) ] / `Pr[ Z = c ]
  by rewrite cpr_eqE.
have kY : `Pr[ Y = b | Z = c ] = `Pr[ [% Y, Z] = (b, c) ] / `Pr[ Z = c ]
  by rewrite cpr_eqE.
rewrite kXY kX kY (H a b c) e1 e2 e3.
exact: alg.
Qed.

(* If X is a function of Z, then X is independent of any Y given Z. *)
Lemma cinde_of_det (s : C -> A) :
  (forall u, X u = s (Z u)) ->
  P |= X _|_ Y | Z.
Proof.
move=> Hs.
apply cinde_of_factorization with
    (g := fun x z => if x == s z then 1 else 0)
    (h := fun y z => `Pr[ [% Y, Z] = (y, z) ]).
move=> x y z; cbv beta.
case: ifP => Hx.
- rewrite mul1r !pfwd1E /Pr; apply: eq_bigl => u.
  rewrite !inE /= !xpair_eqE.
  case Hzu : (Z u == z); last by rewrite !andbF.
  have HXu : X u == x by rewrite (Hs u) (eqP Hzu) (eqP Hx) eqxx.
  by rewrite HXu.
- rewrite mul0r pfwd1E /Pr big_pred0 // => u.
  rewrite !inE /= !xpair_eqE.
  case Hzu : (Z u == z); last by rewrite andbF.
  have HXu : (X u == x) = false.
    by rewrite (Hs u) (eqP Hzu) eq_sym; exact: Hx.
  by rewrite HXu.
Qed.

(* symmetric version: Y is a function of Z *)
Lemma cinde_of_det_r (s : C -> B) :
  (forall u, Y u = s (Z u)) ->
  P |= X _|_ Y | Z.
Proof.
move=> Hs.
apply cinde_of_factorization with
    (g := fun x z => `Pr[ [% X, Z] = (x, z) ])
    (h := fun y z => if y == s z then 1 else 0).
move=> x y z; cbv beta.
case: ifP => Hy.
- rewrite mulr1 !pfwd1E /Pr; apply: eq_bigl => u.
  rewrite !inE /= !xpair_eqE.
  case Hzu : (Z u == z); last by rewrite !andbF.
  have HYu : Y u == y by rewrite (Hs u) (eqP Hzu) (eqP Hy) eqxx.
  by rewrite HYu !andbT.
- rewrite mulr0 pfwd1E /Pr big_pred0 // => u.
  rewrite !inE /= !xpair_eqE.
  case Hzu : (Z u == z); last by rewrite andbF.
  have HYu : (Y u == y) = false.
    by rewrite (Hs u) (eqP Hzu) eq_sym; exact: Hy.
  by rewrite HYu andbF.
Qed.

(* Marginalise a factorization along maps f, f' on the first two components:
   the pushforward of g x z * h y z is (sum of g over a fibre) * (sum of h). *)
Lemma fact_comp (A' B' : finType) (f : A -> A') (f' : B -> B')
    (X' : {RV P -> A'}) (Y' : {RV P -> B'})
    (HX : forall u, X' u = f (X u)) (HY : forall u, Y' u = f' (Y u))
    (g : A -> C -> R) (h : B -> C -> R) :
  (forall x y z, `Pr[ [% X, Y, Z] = (x, y, z) ] = g x z * h y z) ->
  forall a' b' z,
    `Pr[ [% X', Y', Z] = (a', b', z) ]
    = (\sum_(x | f x == a') g x z) * (\sum_(y | f' y == b') h y z).
Proof.
move=> H a' b' z.
have L : `Pr[ [% X', Y', Z] = (a', b', z) ]
    = \sum_(u | ((X' u == a') && (Y' u == b')) && (Z u == z)) P u.
  by rewrite pfwd1E /Pr; apply: eq_bigl => u; rewrite !inE /= !xpair_eqE.
have E : forall (x : A) (y : B), f x == a' -> f' y == b' ->
    \sum_(u | ((((X' u == a') && (Y' u == b')) && (Z u == z)) && (X u == x))
              && (Y u == y)) P u = g x z * h y z.
  move=> x y Hx Hy.
  rewrite -H pfwd1E /Pr; apply: eq_bigl => u.
  rewrite !inE /= !xpair_eqE HX HY.
  apply/idP/idP.
  - move=> /andP [/andP [/andP [_ Hz] Hx'] Hy'].
    by apply/andP; split; [apply/andP; split | exact: Hz].
  - move=> /andP [/andP [Hx' Hy'] Hz].
    have Ha : f (X u) == a' by rewrite (eqP Hx').
    have Hb : f' (Y u) == b' by rewrite (eqP Hy').
    by rewrite Ha Hb Hz Hx' Hy'.
have Hp1 : forall u, ((X' u == a') && (Y' u == b')) && (Z u == z) ->
    f (X u) == a'.
  by move=> u /andP [/andP [Hx' _] _]; rewrite -(HX u).
rewrite big_distrlr L (partition_big X (fun x => f x == a') Hp1).
apply: eq_bigr => x Hx.
have Hp2 : forall u,
    (((X' u == a') && (Y' u == b')) && (Z u == z)) && (X u == x) ->
    f' (Y u) == b'.
  by move=> u /andP [/andP [/andP [_ Hy'] _] _]; rewrite -(HY u).
rewrite (partition_big Y (fun y => f' y == b') Hp2).
apply: eq_bigr => y Hy.
exact: E x y Hx Hy.
Qed.

End CIndepFactorization.

Section DSepImpliesCondIndep.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope ring_scope.

Variable R : realType.
Variable G : graph.
Variable dom : Node G -> finType.
Variable enc : forall n, dom n -> nat.
Variable dec : forall n, nat -> dom n.
Variable Pn : forall n, R.-fdist (dom n).
Variable tF : tgraphfun dom.

Hypothesis encK : forall n : Node G, cancel (enc n) (dec n).

Local Notation Pc     := (@Pc R G dom Pn).
Local Notation nodeRV := (@nodeRV R G dom enc dec Pn tF).
(* [A_set] lives inside the section of MarkovFactorization.v; check that
   this argument order matches what Coq infers for it after [End]. *)
Local Notation A_set  := (@A_set G dom tF).
(* Lemmas of MarkovFactorization.v, with their section variables applied.
   If Coq complains about argument order, run [About <name>.] on each. *)
Local Notation pa_view     := (@pa_view G dom).
Local Notation Pr_prod_set := (@Pr_prod_set R G dom Pn).
Local Notation solve_eq    := (@solve_eq G dom enc dec tF encK).
Local Notation parent_wf   := (@parent_wf G).
Local Notation is_parent_edge := (@is_parent_edge G).
Local Notation child_not_ancestor_of_parent := (@child_not_ancestor_of_parent G).
Local Notation self_in_ancestors := (@self_in_ancestors G).
Local Notation parent_is_descendant := (@parent_is_descendant G).
Local Notation j0 := (@j0 R G dom Pn).


(* ------------------------------------------------------------------ *)
(* Definitions                                                         *)
(* ------------------------------------------------------------------ *)

(* The conditioning set is a set of nodes, so we bundle the solved values of
   the nodes in S into one RV with values in [world dom]: node n keeps its
   solved value when n \in S, and is masked to the default [j0 n] otherwise.
   Using full worlds (rather than dependent functions on the subtype
   {p | p \in S}) means no casts are ever needed. *)
Definition setRV (S : {set Node G}) : {RV Pc -> world dom} :=
  fun w => [ffun n => if n \in S then nodeRV n w else j0 n].

(* [d_separated_bool] works on raw [nat] ids and a [nodes] list, so we
   forget the [Node G] wrapper on the way in. *)
Definition set_nodes (S : {set Node G}) : nodes :=
  [seq ssval z | z <- enum S].

(* all ancestors (self included) of the nodes of T *)
Definition anc_set (T : {set Node G}) : {set Node G} :=
  [set m : Node G | [exists t in T, ssval m \in find_ancestors (ssval t) G]].

(* A is closed under taking parents *)
Definition ancestral (A : {set Node G}) : Prop :=
  forall n m : Node G, n \in A -> is_parent n m -> m \in A.

(* moral graph of G[A]: a, b in A, joined by an edge in either direction,
   or sharing a child c in A *)
Definition moral_adj (A : {set Node G}) (a b : Node G) : bool :=
  (a != b) && (a \in A) && (b \in A) &&
  ( is_edge (ssval a, ssval b) G || is_edge (ssval b, ssval a) G
  || [exists c in A, is_edge (ssval a, ssval c) G
                   && is_edge (ssval b, ssval c) G] ).

(* moral steps that stay out of S *)
Definition moral_adj_avoid (A S : {set Node G}) (a b : Node G) : bool :=
  moral_adj A a b && (a \notin S) && (b \notin S).

(* S separates x from y in the moral graph of G[A] *)
Definition moral_sep (A S : {set Node G}) (x y : Node G) : Prop :=
  ~~ connect (moral_adj_avoid A S) x y.

(* ------------------------------------------------------------------ *)
(* Trivial cases: a conditioned-on variable is a function of setRV S   *)
(* ------------------------------------------------------------------ *)

(* [nodeRV X] is the [X]-coordinate of [setRV S], so [cinde_of_det] applies. *)
Lemma cinde_X_in_S (X Y : Node G) (S : {set Node G}) :
  X \in S ->
  Pc |= nodeRV X _|_ nodeRV Y | setRV S.
Proof.
move=> HX.
pose f := fun z : world dom => z X.
have Hs : forall u : context dom, nodeRV X u = f (setRV S u).
  move=> u.
  have Hh : setRV S u X = nodeRV X u by rewrite /setRV ffunE HX.
  exact: esym Hh.
exact: (@cinde_of_det _ _ _ _ _ _ (nodeRV X) (nodeRV Y) (setRV S) f Hs).
Qed.

(* symmetric case, via [cinde_of_det_r] *)
Lemma cinde_Y_in_S (X Y : Node G) (S : {set Node G}) :
  Y \in S ->
  Pc |= nodeRV X _|_ nodeRV Y | setRV S.
Proof.
move=> HY.
pose f := fun z : world dom => z Y.
have Hs : forall u : context dom, nodeRV Y u = f (setRV S u).
  move=> u.
  have Hh : setRV S u Y = nodeRV Y u by rewrite /setRV ffunE HY.
  exact: esym Hh.
exact: (@cinde_of_det_r _ _ _ _ _ _ (nodeRV X) (nodeRV Y) (setRV S) f Hs).
Qed.

(* ------------------------------------------------------------------ *)
(* Lemma P, step 1: law of the nodes of an ancestral set               *)
(* ------------------------------------------------------------------ *)

(* Mirrors [pfwd1_worldRV]: the event {nodeRV n = a n for all n in A}
   equals {noise_n in A_set a n for all n in A}, because A is closed under
   parents (use [solve_eq] one way, induction as in [world_of_char] the
   other).  Then apply [Pr_prod_set] with S n = setT for n outside A. *)
Lemma pfwd1_ancestral (A : {set Node G}) (a : world dom) :
  G_well_formed G = true /\ contains_cycle G = false ->
  ancestral A ->
  Pr Pc [set w : context dom | [forall n, (n \in A) ==> (nodeRV n w == a n)]]
  = (\prod_(n in A) Pr (Pn n) (A_set a n))%R.
Proof using encK.
move=> Hdag Hanc.
(* the noise sets: node n's own equation at a for n in A, no constraint else *)
pose S (n : Node G) : {set dom n} := if n \in A then A_set a n else setT.
(* if every parent of n solves to a, n's parent view is [pa_view a n] *)
have Hpv : forall (w : context dom) (n : Node G),
    (forall p : Node G, is_parent n p -> solve enc dec tF w p = a p) ->
    (fun p (_ : is_parent n p) => solve enc dec tF w p) = pa_view a n.
  move=> w n Hp.
  apply: boolp.functional_extensionality_dep => p.
  by apply: boolp.funext => hp; rewrite /pa_view; exact: Hp p hp.
(* the event is a product set in the noise *)
have Hev : [set w : context dom | [forall n, (n \in A) ==> (nodeRV n w == a n)]]
         = [set w : context dom | [forall n, w n \in S n]].
  apply/setP => w; rewrite !inE.
  apply/forallP/forallP => [H n | H].
  - (* (=>) n's equation holds at a, because its parents are in A *)
    rewrite /S; case: (boolP (n \in A)) => HnA; last by rewrite inE.
    have Hpar : forall p : Node G, is_parent n p -> solve enc dec tF w p = a p.
      move=> p hp.
      exact: (eqP (elimT implyP (H p) (Hanc n p HnA hp))).
    rewrite /A_set inE; apply/eqP.
    rewrite -(Hpv w n Hpar) -(solve_eq w n Hdag).
    exact: (eqP (elimT implyP (H n) HnA)).
  - (* (<=) induction along the parent relation, inside A *)
    have Hall : forall n : Node G, n \in A -> solve enc dec tF w n = a n.
      move=> n; elim/(well_founded_ind (parent_wf Hdag)): n => n IH HnA.
      have Hpar : forall p : Node G, is_parent n p -> solve enc dec tF w p = a p.
        move=> p hp; exact: IH p hp (Hanc n p HnA hp).
      have Hn : w n \in A_set a n.
        by have Hn := H n; rewrite /S HnA in Hn; exact: Hn.
      move: Hn; rewrite /A_set inE => /eqP Hn.
      by rewrite (solve_eq w n Hdag) (Hpv w n Hpar); exact: Hn.
    move=> n; apply/implyP => HnA; apply/eqP.
    exact: Hall n HnA.
rewrite Hev (Pr_prod_set S) [in RHS]big_mkcond.
apply: eq_bigr => n _.
rewrite /S; case: (boolP (n \in A)) => HnA.
- reflexivity.
- by rewrite Pr_setT.
Qed.

(* ------------------------------------------------------------------ *)
(* Lemma P, step 2: the product splits across a moral separator        *)
(* ------------------------------------------------------------------ *)

(* Every family {n} U pa(n) is a clique of the moral graph of G[A].
   If C is closed under moral neighbours except through S, a family that
   meets C lies inside C U S, so each factor goes to psi1 or psi2. *)
Lemma factor_split (A S C : {set Node G}) :
  G_well_formed G = true /\ contains_cycle G = false ->
  ancestral A ->
  S \subset A -> C \subset A -> (forall n : Node G, n \in C -> n \notin S) ->
  (forall a b : Node G, a \in C -> moral_adj A a b -> b \in C \/ b \in S) ->
  exists psi1 psi2 : world dom -> R,
    (forall v v' : world dom,
        (forall n, n \in C :|: S -> v n = v' n) -> psi1 v = psi1 v')
 /\ (forall v v' : world dom,
        (forall n, n \in A :\: C -> v n = v' n) -> psi2 v = psi2 v')
 /\ (forall v : world dom,
        (\prod_(n in A) Pr (Pn n) (A_set v n))%R = psi1 v * psi2 v).
Proof.
move=> Hdag Hanc _ _ _ Hclosed.
(* a parent p of n in A is in A, differs from n, and p -> n is an edge *)
have Hpar : forall n p : Node G, n \in A -> is_parent n p ->
    p \in A /\ p != n /\ is_edge (ssval p, ssval n) G = true.
  move=> n p HnA Hp; split; first exact: Hanc n p HnA Hp.
  split.
  - apply/negP => /eqP Hpn.
    rewrite Hpn in Hp.
    exact: (elimT negP (child_not_ancestor_of_parent n n Hdag Hp)
                  (self_in_ancestors n)).
  - exact: is_parent_edge n p Hdag.1 Hp.
(* building a moral adjacency *)
have Hma : forall a b : Node G, a != b -> a \in A -> b \in A ->
    (is_edge (ssval a, ssval b) G || is_edge (ssval b, ssval a) G
     || [exists c in A, is_edge (ssval a, ssval c) G
                      && is_edge (ssval b, ssval c) G]) ->
    moral_adj A a b.
  move=> a b Hab Ha Hb Hx.
  by rewrite /moral_adj Hab Ha Hb !andTb.
(* a node and its parent are moral neighbours, in both directions *)
have Hadj1 : forall n p : Node G, n \in A -> is_parent n p ->
    moral_adj A n p /\ moral_adj A p n.
  move=> n p HnA Hp.
  have [HpA [Hpn Hep]] := Hpar n p HnA Hp.
  have Hnp : n != p by rewrite eq_sym.
  split.
  - apply: (Hma n p Hnp HnA HpA).
    by apply/orP; left; apply/orP; right.
  - apply: (Hma p n Hpn HpA HnA).
    by apply/orP; left; apply/orP; left.
(* two parents of the same node are moral neighbours *)
have Hcop : forall n p q : Node G, n \in A ->
    is_parent n p -> is_parent n q -> p != q -> moral_adj A p q.
  move=> n p q HnA Hp Hq Hpq.
  have [HpA [_ Hep]] := Hpar n p HnA Hp.
  have [HqA [_ Heq]] := Hpar n q HnA Hq.
  apply: (Hma p q Hpq HpA HqA).
  apply/orP; right.
  apply/existsP; exists n.
  by rewrite HnA Hep Heq.
(* the factor of n only reads n and its parents *)
have Hdep : forall (v v' : world dom) (n : Node G), v n = v' n ->
    (forall p : Node G, is_parent n p -> v p = v' p) ->
    Pr (Pn n) (A_set v n) = Pr (Pn n) (A_set v' n).
  move=> v v' n Hn Hp.
  have Hpv : pa_view v n = pa_view v' n.
    apply: boolp.functional_extensionality_dep => p.
    by apply: boolp.funext => hp; rewrite /pa_view; exact: Hp p hp.
  by rewrite /A_set Hpv Hn.
(* the family {n} U pa(n) meets C *)
pose touch (n : Node G) : bool :=
  (n \in C) || [exists p, is_parent n p && (p \in C)].
(* a touching family lies inside C U S *)
have Hfam : forall n : Node G, n \in A -> touch n ->
    (n \in C :|: S) /\ (forall p : Node G, is_parent n p -> p \in C :|: S).
  move=> n HnA Ht; move: Ht; rewrite /touch => /orP [HnC | /existsP [p0 /andP [Hp0 Hp0C]]].
  - split; first by rewrite in_setU HnC.
    move=> p Hp.
    case: (Hclosed n p HnC (Hadj1 n p HnA Hp).1) => [H | H];
      by rewrite in_setU H ?orbT.
  - have HnCS : n \in C :|: S.
      case: (Hclosed p0 n Hp0C (Hadj1 n p0 HnA Hp0).2) => [H | H];
        by rewrite in_setU H ?orbT.
    split; first exact: HnCS.
    move=> p Hp.
    case: (eqVneq p p0) => [-> | Hne].
    + by rewrite in_setU Hp0C.
    + have Hne' : p0 != p by rewrite eq_sym.
      case: (Hclosed p0 p Hp0C (Hcop n p0 p HnA Hp0 Hp Hne')) => [H | H];
        by rewrite in_setU H ?orbT.
(* a non-touching family lies inside A \ C *)
have Hnot : forall n : Node G, n \in A -> ~~ touch n ->
    (n \in A :\: C) /\ (forall p : Node G, is_parent n p -> p \in A :\: C).
  move=> n HnA; rewrite /touch negb_or => /andP [HnC Hex].
  split; first by rewrite in_setD HnC HnA.
  move=> p Hp.
  have HpC : p \notin C.
    apply/negP => HpC'.
    have Hex' : [exists p0, is_parent n p0 && (p0 \in C)].
      by apply/existsP; exists p; rewrite Hp HpC'.
    exact: (elimT negP Hex Hex').
  by rewrite in_setD HpC (Hpar n p HnA Hp).1.
exists (fun v => \prod_(n in A | touch n) Pr (Pn n) (A_set v n)),
       (fun v => \prod_(n in A | ~~ touch n) Pr (Pn n) (A_set v n)).
split; last split.
- move=> v v' Hv; apply: eq_bigr => n /andP [HnA Ht].
  have [Hn Hp] := Hfam n HnA Ht.
  apply: Hdep; first exact: Hv n Hn.
  by move=> p hp; exact: Hv p (Hp p hp).
- move=> v v' Hv; apply: eq_bigr => n /andP [HnA Ht].
  have [Hn Hp] := Hnot n HnA Ht.
  apply: Hdep; first exact: Hv n Hn.
  by move=> p hp; exact: Hv p (Hp p hp).
- move=> v.
  by rewrite (bigID touch).
Qed.

(* ------------------------------------------------------------------ *)
(* Ancestral sets                                                      *)
(* ------------------------------------------------------------------ *)

(* the set of ancestors of T is closed under taking parents *)
Lemma anc_set_ancestral (T : {set Node G}) :
  G_well_formed G = true /\ contains_cycle G = false ->
  ancestral (anc_set T).
Proof.
move=> [Hwf Hcyc] n p Hn Hp.
move: Hn; rewrite /anc_set inE => /existsP [t /andP [Ht Hnt]].
rewrite /anc_set inE; apply/existsP; exists t.
apply/andP; split; first exact: Ht.
apply: In_mem.
apply (proj1 (descendants_ancestors_correct G (ssval t) (ssval p)
        (conj (node_in_graph_ssval t) (node_in_graph_ssval p)))).
apply: (descendants_transitive G (ssval t) (ssval n) (ssval p) Hwf Hcyc).
split.
- exact: (parent_is_descendant n p Hwf Hcyc Hp).
- exact: (proj2 (descendants_ancestors_correct G (ssval t) (ssval n)
          (conj (node_in_graph_ssval t) (node_in_graph_ssval n))) (mem_In Hnt)).
Qed.

(* ------------------------------------------------------------------ *)
(* Lemma P, core: a moral separator C | S | rest gives X _|_ Y | S     *)
(* ------------------------------------------------------------------ *)

(* Blocks: C (the X-side), Rs := A \ (C U S) (the Y-side) and S.  Their
   masked worlds [setRV C], [setRV Rs], [setRV S] have a joint law
   g0(al, ga) * h0(be, ga) by [pfwd1_ancestral] and [factor_split];
   [fact_comp] then pushes this down to the X- and Y-coordinates. *)
(* Blocks: C (the X-side), Rs := A \ (C U S) (the Y-side) and S.  Their
   masked worlds [setRV C], [setRV Rs], [setRV S] have a joint law
   g0(al, ga) * h0(be, ga) by [pfwd1_ancestral] and [factor_split];
   [fact_comp] then pushes this down to the X- and Y-coordinates. *)
Lemma cinde_of_blocks (A S C : {set Node G}) (X Y : Node G) :
  G_well_formed G = true /\ contains_cycle G = false ->
  ancestral A ->
  S \subset A -> C \subset A -> (forall n : Node G, n \in C -> n \notin S) ->
  (forall a b : Node G, a \in C -> moral_adj A a b -> b \in C \/ b \in S) ->
  X \in C -> Y \in A -> Y \notin C -> Y \notin S ->
  Pc |= nodeRV X _|_ nodeRV Y | setRV S.
Proof using encK.
move=> Hdag Hanc HSA HCA Hdis Hclosed HXC HYA HYC HYS.
have [psi1 [psi2 [Hp1 [Hp2 Hp3]]]] :=
  factor_split A S C Hdag Hanc HSA HCA Hdis Hclosed.
pose Rs : {set Node G} := A :\: (C :|: S).
have HRnC : forall n, n \in Rs -> n \notin C.
  move=> n; rewrite /Rs in_setD in_setU negb_or => /andP [/andP [HnC _] _].
  exact: HnC.
have HRnS : forall n, n \in Rs -> n \notin S.
  move=> n; rewrite /Rs in_setD in_setU negb_or => /andP [/andP [_ HnS] _].
  exact: HnS.
have HRnA : forall n, n \in Rs -> n \in A.
  move=> n; rewrite /Rs in_setD => /andP [_ HnA]; exact: HnA.
have HSnC : forall n, n \in S -> n \notin C.
  move=> n HnS; apply/negP => HnC.
  exact: (elimT negP (Hdis n HnC) HnS).
have HSnR : forall n, n \in S -> n \notin Rs.
  move=> n HnS; apply/negP => HnR.
  exact: (elimT negP (HRnS n HnR) HnS).
have HAcases : forall n, n \in A -> n \notin C -> n \notin S -> n \in Rs.
  move=> n HnA HnC HnS.
  by rewrite /Rs in_setD in_setU (negbTE HnC) (negbTE HnS) HnA.
have HYR : Y \in Rs := HAcases Y HYA HYC HYS.
(* masks and merges *)
pose isM (T : {set Node G}) (al : world dom) : bool :=
  [forall n, (n \notin T) ==> (al n == j0 n)].
pose gm (al ga : world dom) : world dom :=
  [ffun n => if n \in C then al n else ga n].
pose hm (be ga : world dom) : world dom :=
  [ffun n => if n \in Rs then be n else ga n].
pose mm (al be ga : world dom) : world dom :=
  [ffun n => if n \in C then al n else if n \in Rs then be n else ga n].
pose g0 (al ga : world dom) : R :=
  if isM C al && isM S ga then psi1 (gm al ga) else 0.
pose h0 (be ga : world dom) : R :=
  if isM Rs be && isM S ga then psi2 (hm be ga) else 0.
have mmC : forall al be ga n, n \in C -> mm al be ga n = al n.
  by move=> al be ga n HnC; rewrite /mm ffunE HnC.
have mmR : forall al be ga n, n \in Rs -> mm al be ga n = be n.
  by move=> al be ga n HnR; rewrite /mm ffunE (negbTE (HRnC n HnR)) HnR.
have mmS : forall al be ga n, n \in S -> mm al be ga n = ga n.
  move=> al be ga n HnS.
  by rewrite /mm ffunE (negbTE (HSnC n HnS)) (negbTE (HSnR n HnS)).
have gmC : forall al ga n, n \in C -> gm al ga n = al n.
  by move=> al ga n HnC; rewrite /gm ffunE HnC.
have gmnC : forall al ga n, n \notin C -> gm al ga n = ga n.
  by move=> al ga n HnC; rewrite /gm ffunE (negbTE HnC).
have hmR : forall be ga n, n \in Rs -> hm be ga n = be n.
  by move=> be ga n HnR; rewrite /hm ffunE HnR.
have hmnR : forall be ga n, n \notin Rs -> hm be ga n = ga n.
  by move=> be ga n HnR; rewrite /hm ffunE (negbTE HnR).
(* psi1 / psi2 only see the relevant coordinates *)
have Hd1 : forall al be ga, psi1 (mm al be ga) = psi1 (gm al ga).
  move=> al be ga; apply: Hp1 => n; rewrite in_setU => /orP [HnC | HnS].
  - by rewrite (mmC al be ga n HnC) (gmC al ga n HnC).
  - by rewrite (mmS al be ga n HnS) (gmnC al ga n (HSnC n HnS)).
have Hd2 : forall al be ga, psi2 (mm al be ga) = psi2 (hm be ga).
  move=> al be ga; apply: Hp2 => n; rewrite in_setD => /andP [HnC HnA].
  case: (boolP (n \in Rs)) => HnR.
  - by rewrite (mmR al be ga n HnR) (hmR be ga n HnR).
  - have HnS : n \in S.
      case: (boolP (n \in S)) => // HnS'.
      exfalso; exact: (elimT negP HnR (HAcases n HnA HnC HnS')).
    by rewrite (mmS al be ga n HnS) (hmnR be ga n HnR).
(* a masked world records its block *)
have Hmask : forall (T : {set Node G}) (a : world dom) (w : context dom),
    setRV T w == a -> isM T a.
  move=> T a w /eqP <-.
  apply/forallP => n; apply/implyP => Hn.
  by rewrite /setRV ffunE (negbTE Hn) eqxx.
have Hsel : forall (T : {set Node G}) (a : world dom) (w : context dom)
    (n : Node G), setRV T w == a -> n \in T -> nodeRV n w = a n.
  move=> T a w n /eqP <- Hn.
  by rewrite /setRV ffunE Hn.
(* joint law of the three blocks *)
have Hfac : forall al be ga : world dom,
    `Pr[ [% setRV C, setRV Rs, setRV S] = (al, be, ga) ] = g0 al ga * h0 be ga.
  move=> al be ga.
  rewrite pfwd1E.
  case Hm : (isM C al && isM Rs be && isM S ga).
  - (* the masks are consistent *)
    move/andP: Hm => [/andP [MC MR] MS].
    have Hev : finset ([% setRV C, setRV Rs, setRV S] @^-1 (al, be, ga))
        = [set w : context dom |
             [forall n, (n \in A) ==> (nodeRV n w == mm al be ga n)]].
      apply/setP => w; rewrite !inE; cbv beta; rewrite !xpair_eqE.
      apply/idP/idP.
      + move=> /andP [/andP [Hc Hr] Hs].
        apply/forallP => n; apply/implyP => HnA; apply/eqP.
        case: (boolP (n \in C)) => HnC.
        * by rewrite (mmC al be ga n HnC); exact: Hsel C al w n Hc HnC.
        * case: (boolP (n \in Rs)) => HnR.
          -- by rewrite (mmR al be ga n HnR); exact: Hsel Rs be w n Hr HnR.
          -- have HnS : n \in S.
               case: (boolP (n \in S)) => // HnS'.
               exfalso; exact: (elimT negP HnR (HAcases n HnA HnC HnS')).
             by rewrite (mmS al be ga n HnS); exact: Hsel S ga w n Hs HnS.
      + move/forallP => Hall.
        have Hn : forall n, n \in A -> nodeRV n w = mm al be ga n.
          move=> n HnA; exact: (eqP (elimT implyP (Hall n) HnA)).
        have Hblk : forall (T : {set Node G}) (a : world dom), isM T a ->
            (forall n, n \in T -> nodeRV n w = a n) -> setRV T w == a.
          move=> T a MT HT; apply/eqP; apply/ffunP => n.
          rewrite /setRV ffunE.
          case: (boolP (n \in T)) => HnT.
          * pose proof (HT n HnT). exact H.
          * rewrite ?(negbTE HnT).
            exact: esym (eqP (elimT implyP (elimT forallP MT n) HnT)).
        apply/andP; split.
        * apply/andP; split.
          -- apply: (Hblk C al MC) => n HnC.
             by rewrite (Hn n (subsetP HCA n HnC)) (mmC al be ga n HnC).
          -- apply: (Hblk Rs be MR) => n HnR.
             by rewrite (Hn n (HRnA n HnR)) (mmR al be ga n HnR).
        * apply: (Hblk S ga MS) => n HnS.
          by rewrite (Hn n (subsetP HSA n HnS)) (mmS al be ga n HnS).
    have Hg : g0 al ga = psi1 (gm al ga) by rewrite /g0 MC MS.
    have Hh : h0 be ga = psi2 (hm be ga) by rewrite /h0 MR MS.
    by rewrite Hev (pfwd1_ancestral A (mm al be ga) Hdag Hanc)
               (Hp3 (mm al be ga)) (Hd1 al be ga) (Hd2 al be ga) Hg Hh.
  - (* inconsistent masks: the event is empty and a factor vanishes *)
    have Hempty : forall w : context dom,
        (w \in finset ([% setRV C, setRV Rs, setRV S] @^-1 (al, be, ga)))
        = false.
      move=> w; apply/negbTE/negP => Hin.
      move: Hin; rewrite !inE; cbv beta; rewrite !xpair_eqE.
      move=> /andP [/andP [Hc Hr] Hs].
      have Hcontra : isM C al && isM Rs be && isM S ga.
        by rewrite (Hmask _ _ _ Hc) (Hmask _ _ _ Hr) (Hmask _ _ _ Hs).
      by rewrite Hm in Hcontra.
    have Hz : g0 al ga * h0 be ga = 0.
      rewrite /g0 /h0; case: ifP => Hg; last by rewrite mul0r.
      case: ifP => Hh; last by rewrite mulr0.
      exfalso; move/andP: Hg => [MC MS]; move/andP: Hh => [MR _].
      have Hcontra : isM C al && isM Rs be && isM S ga by rewrite MC MR MS.
      by rewrite Hm in Hcontra.
    rewrite Hz /Pr big_pred0 // => w; exact: Hempty w.
(* push the block law down to the X- and Y-coordinates *)
have HXe : forall u : context dom, nodeRV X u = (setRV C u) X.
  by move=> u; rewrite /setRV ffunE HXC.
have HYe : forall u : context dom, nodeRV Y u = (setRV Rs u) Y.
  by move=> u; rewrite /setRV ffunE HYR.
have Hfc := @fact_comp _ _ _ _ _ _ (setRV C) (setRV Rs) (setRV S)
    (dom X) (dom Y) (fun al : world dom => al X) (fun be : world dom => be Y)
    (nodeRV X) (nodeRV Y) HXe HYe g0 h0 Hfac.
exact: (@cinde_of_factorization _ _ _ _ _ _ (nodeRV X) (nodeRV Y) (setRV S)
    (fun (x : dom X) (z : world dom) => \sum_(al : world dom | al X == x) g0 al z)
    (fun (y : dom Y) (z : world dom) => \sum_(be : world dom | be Y == y) h0 be z) Hfc).
Qed.

(* ------------------------------------------------------------------ *)
(* Lemma P: moral separation implies conditional independence          *)
(* ------------------------------------------------------------------ *)

(* Let A := anc_set (X |: (Y |: S)) and C the nodes reachable from X by
   [moral_adj_avoid]; moral separation gives Y \notin C, and C is closed in
   the sense [cinde_of_blocks] needs. *)
Lemma cinde_of_moral_sep (X Y : Node G) (S : {set Node G}) :
  G_well_formed G = true /\ contains_cycle G = false ->
  X != Y -> X \notin S -> Y \notin S ->
  moral_sep (anc_set (X |: (Y |: S))) S X Y ->
  Pc |= nodeRV X _|_ nodeRV Y | setRV S.
Proof using encK.
move=> Hdag Hne HXS HYS Hsep.
pose A := anc_set (X |: (Y |: S)).
have Hanc : ancestral A := anc_set_ancestral _ Hdag.
have HsepA : moral_sep A S X Y := Hsep.
have HinA : forall t, t \in X |: (Y |: S) -> t \in A.
  move=> t Ht; rewrite /A /anc_set inE; apply/existsP; exists t.
  by rewrite Ht (self_in_ancestors t).
have HXA : X \in A by apply: HinA; rewrite !inE eqxx.
have HYA : Y \in A by apply: HinA; rewrite !inE eqxx orbT.
have HSA : S \subset A.
  apply/subsetP => t HtS; apply: HinA; rewrite !inE HtS !orbT //.
have Hma_r : forall a b, moral_adj A a b -> b \in A.
  move=> a b; rewrite /moral_adj => /andP [/andP [/andP [_ _] Hb] _].
  exact: Hb.
pose C : {set Node G} := [set n | connect (moral_adj_avoid A S) X n].
have Hpath : forall (p : seq (Node G)) (x : Node G),
    path (moral_adj_avoid A S) x p -> x \in A -> x \notin S ->
    last x p \in A /\ last x p \notin S.
  move=> p; elim: p => [| y p IH] x /=.
  - by move=> _ HxA HxS; split; [exact: HxA | exact: HxS].
  - move=> /andP [Hxy Hp] _ _.
    move: Hxy; rewrite /moral_adj_avoid => /andP [/andP [Hm _] HyS].
    exact: IH y Hp (Hma_r x y Hm) HyS.
have HXC : X \in C by rewrite /C inE connect0.
have HCsub : forall n, n \in C -> n \in A /\ n \notin S.
  move=> n; rewrite /C inE => /connectP [p Hp ->].
  exact: Hpath p X Hp HXA HXS.
have HCA : C \subset A.
  by apply/subsetP => n Hn; exact: (HCsub n Hn).1.
have Hdis : forall n : Node G, n \in C -> n \notin S :=
  fun n HnC => (HCsub n HnC).2.
have Hclosed : forall a b : Node G, a \in C -> moral_adj A a b ->
    b \in C \/ b \in S.
  move=> a b HaC Hab.
  case: (boolP (b \in S)) => [HbS | HbS]; first by right.
  left.
  have HaS := (HCsub a HaC).2.
  move: HaC; rewrite /C !inE => HaC.
  apply: (connect_trans HaC).
  apply: connect1.
  by rewrite /moral_adj_avoid Hab HaS HbS.
have HYC : Y \notin C.
  apply/negP => HYC'.
  move: HYC'; rewrite /C inE => HYC'.
  exact: (elimT negP HsepA HYC').
exact: (cinde_of_blocks A S C X Y Hdag Hanc HSA HCA Hdis Hclosed
          HXC HYA HYC HYS).
Qed.

(* ------------------------------------------------------------------ *)
(* Lemma B: d-separation implies moral separation (pure graph theory)  *)
(* ------------------------------------------------------------------ *)

(* Proof sketch: contrapositive.  A moral path from X to Y avoiding S
   (take a shortest one) lifts to a path in G: keep real edges, replace
   each co-parent step a -- b by a -> c <- b.  Each such collider c is in
   An(X,Y,S), so it has a descendant in X, Y or S; when that descendant is
   X or Y, reroute along the directed path.  Keep the path NoDup
   ([nodup_acyclic2]).  Conclude with [d_separated_vs_connected].
   Reusable machinery lives in DSepHPaT.v: open_path, d_connected_open,
   open_d_connected, adj_path, reroute, sweep. *)
Lemma dsep_implies_moral_sep (X Y : Node G) (S : {set Node G}) :
  G_well_formed G = true /\ contains_cycle G = false ->
  X != Y -> X \notin S -> Y \notin S ->
  d_separated_bool (ssval X) (ssval Y) G (set_nodes S) = true ->
  moral_sep (anc_set (X |: (Y |: S))) S X Y.
Proof.
Admitted.

(* ------------------------------------------------------------------ *)
(* Main lemma                                                          *)
(* ------------------------------------------------------------------ *)

(* d-separation implies conditional independence (global Markov property):
   if X and Y are d-separated by S in a well-formed acyclic G, then the solved
   values of X and Y are independent given the solved values of S. *)
Lemma dsep_implies_cond_indep (X Y : Node G) (Z : {set Node G}) :
  G_well_formed G = true /\ contains_cycle G = false ->
  X != Y ->
  d_separated_bool (ssval X) (ssval Y) G (set_nodes Z) = true ->
  Pc |= nodeRV X _|_ nodeRV Y | setRV Z.
Proof.
move=> Hdag Hne Hd.
case: (boolP (X \in Z)) => [HX | HX]; first exact: cinde_X_in_S.
case: (boolP (Y \in Z)) => [HY | HY]; first exact: cinde_Y_in_S.
have Hm := dsep_implies_moral_sep X Y Z Hdag Hne HX HY Hd.
exact: (cinde_of_moral_sep X Y Z Hdag Hne HX HY Hm).
Qed.

End DSepImpliesCondIndep.
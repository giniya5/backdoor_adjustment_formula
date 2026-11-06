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
From CondIndep Require Import DSepTZ.
From CondIndep Require Import DSepHPaT.
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
(*     d_separated_bool X Y G Z = true                                 *)
(*       ==> Z separates X from Y in the moral graph of G[An(X,Y,S)]   *)
(*   Lemma P (probability only):                                       *)
(*     Z separates X from Y in the moral graph of G[An(X,Y,S)]         *)
(*       ==> nodeRV X _|_ nodeRV Y | setRV Z                           *)
(*                                                                     *)
(* Lemma P is assembled from:                                          *)
(*   1. pfwd1_ancestral          marginal law on an ancestral set      *)
(*   2. factor_split             the product splits across Z           *)
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
   the nodes in Z into one RV with values in [world dom]: node n keeps its
   solved value when n \in Z, and is masked to the default [j0 n] otherwise.
   Using full worlds (rather than dependent functions on the subtype
   {p | p \in Z}) means no casts are ever needed. *)
Definition setRV (Z : {set Node G}) : {RV Pc -> world dom} :=
  fun w => [ffun n => if n \in Z then nodeRV n w else j0 n].

(* [d_separated_bool] works on raw [nat] ids and a [nodes] list, so we
   forget the [Node G] wrapper on the way in. *)
Definition set_nodes (Z : {set Node G}) : nodes :=
  [seq ssval z | z <- enum Z].

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

(* moral steps that stay out of Z *)
Definition moral_adj_avoid (A Z : {set Node G}) (a b : Node G) : bool :=
  moral_adj A a b && (a \notin Z) && (b \notin Z).

(* Z separates x from y in the moral graph of G[A] *)
Definition moral_sep (A Z : {set Node G}) (x y : Node G) : Prop :=
  ~~ connect (moral_adj_avoid A Z) x y.

(* ------------------------------------------------------------------ *)
(* Trivial cases: a conditioned-on variable is a function of setRV Z   *)
(* ------------------------------------------------------------------ *)

(* [nodeRV X] is the [X]-coordinate of [setRV Z], so [cinde_of_det] applies. *)
Lemma cinde_X_in_Z (X Y : Node G) (Z : {set Node G}) :
  X \in Z ->
  Pc |= nodeRV X _|_ nodeRV Y | setRV Z.
Proof.
  move=> HX.
  pose f := fun z : world dom => z X.
  have Hs : forall u : context dom, nodeRV X u = f (setRV Z u).
    move=> u.
    have Hh : setRV Z u X = nodeRV X u by rewrite /setRV ffunE HX.
    exact: esym Hh.
  exact: (@cinde_of_det _ _ _ _ _ _ (nodeRV X) (nodeRV Y) (setRV Z) f Hs).
Qed.

(* symmetric case, via [cinde_of_det_r] *)
Lemma cinde_Y_in_Z (X Y : Node G) (Z : {set Node G}) :
  Y \in Z ->
  Pc |= nodeRV X _|_ nodeRV Y | setRV Z.
Proof.
  move=> HY.
  pose f := fun z : world dom => z Y.
  have Hs : forall u : context dom, nodeRV Y u = f (setRV Z u).
    move=> u.
    have Hh : setRV Z u Y = nodeRV Y u by rewrite /setRV ffunE HY.
    exact: esym Hh.
  exact: (@cinde_of_det_r _ _ _ _ _ _ (nodeRV X) (nodeRV Y) (setRV Z) f Hs).
Qed.

(* ------------------------------------------------------------------ *)
(* Lemma P, step 1: law of the nodes of an ancestral set               *)
(* ------------------------------------------------------------------ *)

(* Mirrors [pfwd1_worldRV]: the event {nodeRV n = a n for all n in A}
   equals {noise_n in A_set a n for all n in A}, because A is closed under
   parents (use [solve_eq] one way, induction as in [world_of_char] the
   other).  Then apply [Pr_prod_set] with Z n = setT for n outside A. *)
Lemma pfwd1_ancestral (A : {set Node G}) (a : world dom) :
  G_well_formed G = true /\ contains_cycle G = false ->
  ancestral A ->
  Pr Pc [set w : context dom | [forall n, (n \in A) ==> (nodeRV n w == a n)]]
  = (\prod_(n in A) Pr (Pn n) (A_set a n))%R.
Proof using encK.
  move=> Hdag Hanc.
  (* the noise sets: node n's own equation at a for n in A, no constraint else *)
  pose Z (n : Node G) : {set dom n} := if n \in A then A_set a n else setT.
  (* if every parent of n solves to a, n's parent view is [pa_view a n] *)
  have Hpv : forall (w : context dom) (n : Node G),
      (forall p : Node G, is_parent n p -> solve enc dec tF w p = a p) ->
      (fun p (_ : is_parent n p) => solve enc dec tF w p) = pa_view a n.
    move=> w n Hp.
    apply: boolp.functional_extensionality_dep => p.
    by apply: boolp.funext => hp; rewrite /pa_view; exact: Hp p hp.
  (* the event is a product set in the noise *)
  have Hev : [set w : context dom | [forall n, (n \in A) ==> (nodeRV n w == a n)]]
          = [set w : context dom | [forall n, w n \in Z n]].
    apply/setP => w; rewrite !inE.
    apply/forallP/forallP => [H n | H].
    - (* (=>) n's equation holds at a, because its parents are in A *)
      rewrite /Z; case: (boolP (n \in A)) => HnA; last by rewrite inE.
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
          by have Hn := H n; rewrite /Z HnA in Hn; exact: Hn.
        move: Hn; rewrite /A_set inE => /eqP Hn.
        by rewrite (solve_eq w n Hdag) (Hpv w n Hpar); exact: Hn.
      move=> n; apply/implyP => HnA; apply/eqP.
      exact: Hall n HnA.
  rewrite Hev (Pr_prod_set Z) [in RHS]big_mkcond.
  apply: eq_bigr => n _.
  rewrite /Z; case: (boolP (n \in A)) => HnA.
  - reflexivity.
  - by rewrite Pr_setT.
Qed.

(* ------------------------------------------------------------------ *)
(* Lemma P, step 2: the product splits across a moral separator        *)
(* ------------------------------------------------------------------ *)

(* Every family {n} U pa(n) is a clique of the moral graph of G[A].
   If C is closed under moral neighbours except through Z, a family that
   meets C lies inside C U Z, so each factor goes to psi1 or psi2. *)
Lemma factor_split (A Z C : {set Node G}) :
  G_well_formed G = true /\ contains_cycle G = false ->
  ancestral A ->
  Z \subset A -> C \subset A -> (forall n : Node G, n \in C -> n \notin Z) ->
  (forall a b : Node G, a \in C -> moral_adj A a b -> b \in C \/ b \in Z) ->
  exists psi1 psi2 : world dom -> R,
    (forall v v' : world dom,
        (forall n, n \in C :|: Z -> v n = v' n) -> psi1 v = psi1 v')
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
  (* a touching family lies inside C U Z *)
  have Hfam : forall n : Node G, n \in A -> touch n ->
      (n \in C :|: Z) /\ (forall p : Node G, is_parent n p -> p \in C :|: Z).
    move=> n HnA Ht; move: Ht; rewrite /touch => /orP [HnC | /existsP [p0 /andP [Hp0 Hp0C]]].
    - split; first by rewrite in_setU HnC.
      move=> p Hp.
      case: (Hclosed n p HnC (Hadj1 n p HnA Hp).1) => [H | H];
        by rewrite in_setU H ?orbT.
    - have HnCZ : n \in C :|: Z.
        case: (Hclosed p0 n Hp0C (Hadj1 n p0 HnA Hp0).2) => [H | H];
          by rewrite in_setU H ?orbT.
      split; first exact: HnCZ.
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
(* Lemma P, core: a moral separator C | Z | rest gives X _|_ Y | Z     *)
(* ------------------------------------------------------------------ *)

(* Blocks: C (the X-side), Rs := A \ (C U Z) (the Y-side) and Z.  Their
   masked worlds [setRV C], [setRV Rs], [setRV Z] have a joint law
   g0(al, ga) * h0(be, ga) by [pfwd1_ancestral] and [factor_split];
   [fact_comp] then pushes this down to the X- and Y-coordinates. *)
(* Blocks: C (the X-side), Rs := A \ (C U Z) (the Y-side) and Z.  Their
   masked worlds [setRV C], [setRV Rs], [setRV Z] have a joint law
   g0(al, ga) * h0(be, ga) by [pfwd1_ancestral] and [factor_split];
   [fact_comp] then pushes this down to the X- and Y-coordinates. *)
Lemma cinde_of_blocks (A Z C : {set Node G}) (X Y : Node G) :
  G_well_formed G = true /\ contains_cycle G = false ->
  ancestral A ->
  Z \subset A -> C \subset A -> (forall n : Node G, n \in C -> n \notin Z) ->
  (forall a b : Node G, a \in C -> moral_adj A a b -> b \in C \/ b \in Z) ->
  X \in C -> Y \in A -> Y \notin C -> Y \notin Z ->
  Pc |= nodeRV X _|_ nodeRV Y | setRV Z.
Proof using encK.
  move=> Hdag Hanc HSA HCA Hdis Hclosed HXC HYA HYC HYS.
  have [psi1 [psi2 [Hp1 [Hp2 Hp3]]]] :=
    factor_split A Z C Hdag Hanc HSA HCA Hdis Hclosed.
  pose Rs : {set Node G} := A :\: (C :|: Z).
  have HRnC : forall n, n \in Rs -> n \notin C.
    move=> n; rewrite /Rs in_setD in_setU negb_or => /andP [/andP [HnC _] _].
    exact: HnC.
  have HRnZ : forall n, n \in Rs -> n \notin Z.
    move=> n; rewrite /Rs in_setD in_setU negb_or => /andP [/andP [_ HnS] _].
    exact: HnS.
  have HRnA : forall n, n \in Rs -> n \in A.
    move=> n; rewrite /Rs in_setD => /andP [_ HnA]; exact: HnA.
  have HSnC : forall n, n \in Z -> n \notin C.
    move=> n HnS; apply/negP => HnC.
    exact: (elimT negP (Hdis n HnC) HnS).
  have HSnR : forall n, n \in Z -> n \notin Rs.
    move=> n HnS; apply/negP => HnR.
    exact: (elimT negP (HRnZ n HnR) HnS).
  have HAcases : forall n, n \in A -> n \notin C -> n \notin Z -> n \in Rs.
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
    if isM C al && isM Z ga then psi1 (gm al ga) else 0.
  pose h0 (be ga : world dom) : R :=
    if isM Rs be && isM Z ga then psi2 (hm be ga) else 0.
  have mmC : forall al be ga n, n \in C -> mm al be ga n = al n.
    by move=> al be ga n HnC; rewrite /mm ffunE HnC.
  have mmR : forall al be ga n, n \in Rs -> mm al be ga n = be n.
    by move=> al be ga n HnR; rewrite /mm ffunE (negbTE (HRnC n HnR)) HnR.
  have mmS : forall al be ga n, n \in Z -> mm al be ga n = ga n.
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
    - have HnS : n \in Z.
        case: (boolP (n \in Z)) => // HnS'.
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
      `Pr[ [% setRV C, setRV Rs, setRV Z] = (al, be, ga) ] = g0 al ga * h0 be ga.
    move=> al be ga.
    rewrite pfwd1E.
    case Hm : (isM C al && isM Rs be && isM Z ga).
    - (* the masks are consistent *)
      move/andP: Hm => [/andP [MC MR] MS].
      have Hev : finset ([% setRV C, setRV Rs, setRV Z] @^-1 (al, be, ga))
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
            -- have HnS : n \in Z.
                case: (boolP (n \in Z)) => // HnS'.
                exfalso; exact: (elimT negP HnR (HAcases n HnA HnC HnS')).
              by rewrite (mmS al be ga n HnS); exact: Hsel Z ga w n Hs HnS.
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
          * apply: (Hblk Z ga MS) => n HnS.
            by rewrite (Hn n (subsetP HSA n HnS)) (mmS al be ga n HnS).
      have Hg : g0 al ga = psi1 (gm al ga) by rewrite /g0 MC MS.
      have Hh : h0 be ga = psi2 (hm be ga) by rewrite /h0 MR MS.
      by rewrite Hev (pfwd1_ancestral A (mm al be ga) Hdag Hanc)
                (Hp3 (mm al be ga)) (Hd1 al be ga) (Hd2 al be ga) Hg Hh.
    - (* inconsistent masks: the event is empty and a factor vanishes *)
      have Hempty : forall w : context dom,
          (w \in finset ([% setRV C, setRV Rs, setRV Z] @^-1 (al, be, ga)))
          = false.
        move=> w; apply/negbTE/negP => Hin.
        move: Hin; rewrite !inE; cbv beta; rewrite !xpair_eqE.
        move=> /andP [/andP [Hc Hr] Hs].
        have Hcontra : isM C al && isM Rs be && isM Z ga.
          by rewrite (Hmask _ _ _ Hc) (Hmask _ _ _ Hr) (Hmask _ _ _ Hs).
        by rewrite Hm in Hcontra.
      have Hz : g0 al ga * h0 be ga = 0.
        rewrite /g0 /h0; case: ifP => Hg; last by rewrite mul0r.
        case: ifP => Hh; last by rewrite mulr0.
        exfalso; move/andP: Hg => [MC MS]; move/andP: Hh => [MR _].
        have Hcontra : isM C al && isM Rs be && isM Z ga by rewrite MC MR MS.
        by rewrite Hm in Hcontra.
      rewrite Hz /Pr big_pred0 // => w; exact: Hempty w.
  (* push the block law down to the X- and Y-coordinates *)
  have HXe : forall u : context dom, nodeRV X u = (setRV C u) X.
    by move=> u; rewrite /setRV ffunE HXC.
  have HYe : forall u : context dom, nodeRV Y u = (setRV Rs u) Y.
    by move=> u; rewrite /setRV ffunE HYR.
  have Hfc := @fact_comp _ _ _ _ _ _ (setRV C) (setRV Rs) (setRV Z)
      (dom X) (dom Y) (fun al : world dom => al X) (fun be : world dom => be Y)
      (nodeRV X) (nodeRV Y) HXe HYe g0 h0 Hfac.
  exact: (@cinde_of_factorization _ _ _ _ _ _ (nodeRV X) (nodeRV Y) (setRV Z)
      (fun (x : dom X) (z : world dom) => \sum_(al : world dom | al X == x) g0 al z)
      (fun (y : dom Y) (z : world dom) => \sum_(be : world dom | be Y == y) h0 be z) Hfc).
Qed.

(* ------------------------------------------------------------------ *)
(* Lemma P: moral separation implies conditional independence          *)
(* ------------------------------------------------------------------ *)

(* Let A := anc_set (X |: (Y |: Z)) and C the nodes reachable from X by
   [moral_adj_avoid]; moral separation gives Y \notin C, and C is closed in
   the sense [cinde_of_blocks] needs. *)
Lemma cinde_of_moral_sep (X Y : Node G) (Z : {set Node G}) :
  G_well_formed G = true /\ contains_cycle G = false ->
  X != Y -> X \notin Z -> Y \notin Z ->
  moral_sep (anc_set (X |: (Y |: Z))) Z X Y ->
  Pc |= nodeRV X _|_ nodeRV Y | setRV Z.
Proof using encK.
  move=> Hdag Hne HXS HYS Hsep.
  pose A := anc_set (X |: (Y |: Z)).
  have Hanc : ancestral A := anc_set_ancestral _ Hdag.
  have HsepA : moral_sep A Z X Y := Hsep.
  have HinA : forall t, t \in X |: (Y |: Z) -> t \in A.
    move=> t Ht; rewrite /A /anc_set inE; apply/existsP; exists t.
    by rewrite Ht (self_in_ancestors t).
  have HXA : X \in A by apply: HinA; rewrite !inE eqxx.
  have HYA : Y \in A by apply: HinA; rewrite !inE eqxx orbT.
  have HSA : Z \subset A.
    apply/subsetP => t HtS; apply: HinA; rewrite !inE HtS !orbT //.
  have Hma_r : forall a b, moral_adj A a b -> b \in A.
    move=> a b; rewrite /moral_adj => /andP [/andP [/andP [_ _] Hb] _].
    exact: Hb.
  pose C : {set Node G} := [set n | connect (moral_adj_avoid A Z) X n].
  have Hpath : forall (p : seq (Node G)) (x : Node G),
      path (moral_adj_avoid A Z) x p -> x \in A -> x \notin Z ->
      last x p \in A /\ last x p \notin Z.
    move=> p; elim: p => [| y p IH] x /=.
    - by move=> _ HxA HxS; split; [exact: HxA | exact: HxS].
    - move=> /andP [Hxy Hp] _ _.
      move: Hxy; rewrite /moral_adj_avoid => /andP [/andP [Hm _] HyS].
      exact: IH y Hp (Hma_r x y Hm) HyS.
  have HXC : X \in C by rewrite /C inE connect0.
  have HCsub : forall n, n \in C -> n \in A /\ n \notin Z.
    move=> n; rewrite /C inE => /connectP [p Hp ->].
    exact: Hpath p X Hp HXA HXS.
  have HCA : C \subset A.
    by apply/subsetP => n Hn; exact: (HCsub n Hn).1.
  have Hdis : forall n : Node G, n \in C -> n \notin Z :=
    fun n HnC => (HCsub n HnC).2.
  have Hclosed : forall a b : Node G, a \in C -> moral_adj A a b ->
      b \in C \/ b \in Z.
    move=> a b HaC Hab.
    case: (boolP (b \in Z)) => [HbS | HbS]; first by right.
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
  exact: (cinde_of_blocks A Z C X Y Hdag Hanc HSA HCA Hdis Hclosed
            HXC HYA HYC HYS).
Qed.

(* ------------------------------------------------------------------ *)
(* Lemma B: d-separation implies moral separation (pure graph theory)  *)
(* ------------------------------------------------------------------ *)

(* Strategy (contrapositive).  Suppose X and Y are joined by a moral path
   avoiding S.  We build an open *walk* from X to Y by a state machine along
   the moral path.  Walks are stored REVERSED (head = current endpoint), as in
   DSepHPaT.v, so every extension is a cons at the front.  At a "bad" collider
   (no descendant in S) we reroute along a directed path to X or to Y.  A walk
   is then shortened to a NoDup path ([walk_to_path]) and handed to
   [d_separated_vs_connected]. *)

(* an open walk, stored reversed: adjacent, and every interior triple ok *)
Definition OW (Z : nodes) (K : nodes) : Prop :=
  adj K G /\ open_path G Z K.

(* Wk Z X v dir: there is an open walk from X to v (stored reversed, so it
   starts with v and ends with X); [dir] records whether the last edge points
   into v (true) or out of v (false).  The trivial walk v = X counts for both. *)
Definition Wk (Z : nodes) (X v : node) (dir : bool) : Prop :=
  v = X \/ exists w K, OW Z (v :: w :: K) /\
     (exists K', v :: w :: K = app K' [X]) /\
     (if dir then is_edge (w, v) G = true else is_edge (v, w) G = true).

Lemma triple_noncol (Z : nodes) (a b c : node) :
  ~ (is_edge (a, b) G = true /\ is_edge (c, b) G = true) -> ~ In b Z ->
  triple_ok G Z a b c.
Proof.
move=> Hn HbZ; split.
- move=> Hc; exfalso; exact: Hn Hc.
- move=> _; exact: HbZ.
Qed.

Lemma triple_col (Z : nodes) (a b c : node) :
  is_edge (a, b) G = true -> is_edge (c, b) G = true ->
  (exists d, In d (find_descendants b G) /\ In d Z) ->
  triple_ok G Z a b c.
Proof.
move=> Hab Hcb Hd; split.
- move=> _; exact: Hd.
- move=> Hn; exfalso; apply: Hn; split; [exact: Hab | exact: Hcb].
Qed.

Lemma ow_ext (Z : nodes) (y v w : node) (K : nodes) :
  OW Z (v :: w :: K) ->
  (is_edge (y, v) G = true \/ is_edge (v, y) G = true) ->
  triple_ok G Z y v w ->
  OW Z (y :: v :: w :: K).
Proof.
move=> [Hadj Hopen] Hyv Ht; split.
- exact: (adj_cons_front G y v (w :: K) Hadj Hyv).
- apply: (open_cons_front G Z y v (w :: K) Hopen).
  move=> w' Bt' E; case: E => <- _; exact: Ht.
Qed.

Lemma ow_ext0 (Z : nodes) (y v : node) :
  (is_edge (y, v) G = true \/ is_edge (v, y) G = true) -> OW Z [y; v].
Proof.
move=> H; split.
- rewrite adj_cons; split; [exact: H | exact: I].
- exact: I.
Qed.

(* extend along an edge leaving v: v is a non-collider, so it must avoid Z *)
Lemma wk_out (Z : nodes) (X v y : node) (d : bool) :
  G_well_formed G = true /\ contains_cycle G = false ->
  Wk Z X v d -> ~ In v Z -> is_edge (v, y) G = true -> Wk Z X y true.
Proof.
move=> Hdag [Hv | [w [K [Hw [[K' HK] _]]]]] HvZ Hvy.
- subst v.
  right; exists X, []; split; first exact: (ow_ext0 Z y X (or_intror Hvy)).
  split; first by exists [y].
  exact: Hvy.
- right; exists v, (w :: K); split.
  + apply: (ow_ext Z y v w K Hw (or_intror Hvy)).
    apply: (triple_noncol Z y v w _ HvZ).
    move=> H; exact: (no_two_cycle G y v Hdag.1 Hdag.2 H.1 Hvy).
  + split; first by exists (y :: K'); rewrite /= HK.
    exact: Hvy.
Qed.

(* extend along an edge entering v, after a walk that left v: non-collider *)
Lemma wk_in_from_out (Z : nodes) (X v y : node) :
  G_well_formed G = true /\ contains_cycle G = false ->
  Wk Z X v false -> ~ In v Z -> is_edge (y, v) G = true -> Wk Z X y false.
Proof.
move=> Hdag [Hv | [w [K [Hw [[K' HK] Hdir]]]]] HvZ Hyv.
- subst v.
  right; exists X, []; split; first exact: (ow_ext0 Z y X (or_introl Hyv)).
  split; first by exists [y].
  exact: Hyv.
- right; exists v, (w :: K); split.
  + apply: (ow_ext Z y v w K Hw (or_introl Hyv)).
    apply: (triple_noncol Z y v w _ HvZ).
    move=> H; exact: (no_two_cycle G v w Hdag.1 Hdag.2 Hdir H.2).
  + split; first by exists (y :: K'); rewrite /= HK.
    exact: Hyv.
Qed.

(* extend along an edge entering v, after a walk that entered v: collider *)
Lemma wk_in_from_in (Z : nodes) (X v y : node) :
  Wk Z X v true -> is_edge (y, v) G = true ->
  (exists d, In d (find_descendants v G) /\ In d Z) -> Wk Z X y false.
Proof.
move=> [Hv | [w [K [Hw [[K' HK] Hdir]]]]] Hyv Hd.
- subst v.
  right; exists X, []; split; first exact: (ow_ext0 Z y X (or_introl Hyv)).
  split; first by exists [y].
  exact: Hyv.
- right; exists v, (w :: K); split.
  + apply: (ow_ext Z y v w K Hw (or_introl Hyv)).
    exact: (triple_col Z y v w Hyv Hdir Hd).
  + split; first by exists (y :: K'); rewrite /= HK.
    exact: Hyv.
Qed.

Lemma dadj_adj (L : nodes) : dadj L G -> adj L G.
Proof.
elim: L => [|a L IH].
- by move=> _; exact: I.
- case: L IH => [|b L] IH H.
  + exact: I.
  + rewrite dadj_cons in H; rewrite adj_cons; split.
    * by left; exact: H.1.
    * exact: IH H.2.
Qed.

(* a directed path avoiding Z is an open walk *)
Lemma open_dadj (Z : nodes) (L : nodes) :
  G_well_formed G = true /\ contains_cycle G = false ->
  dadj L G -> (forall z, In z L -> ~ In z Z) -> open_path G Z L.
Proof.
move=> Hdag; elim: L => [|a L IH] Hd HZ.
- exact: I.
- case: L IH Hd HZ => [|b L] IH Hd HZ.
  + exact: I.
  + case: L IH Hd HZ => [|c r] IH Hd HZ.
    * exact: I.
    * rewrite open_path_cons3; split.
      -- rewrite dadj_cons in Hd; case: Hd => Hab Hd'.
         rewrite dadj_cons in Hd'; case: Hd' => Hbc Hd''.
         apply: triple_noncol.
         ++ move=> H; exact: (no_two_cycle G b c Hdag.1 Hdag.2 Hbc H.2).
         ++ apply: HZ; right; left; reflexivity.
      -- apply: IH.
         ++ rewrite dadj_cons in Hd; exact: Hd.2.
         ++ move=> z Hz; apply: HZ; right; exact: Hz.
Qed.

(* if X lies below p and no descendant of p is in Z, walk from X up to p *)
Lemma wk_up (Z : nodes) (X p : node) :
  G_well_formed G = true /\ contains_cycle G = false ->
  In X (find_descendants p G) ->
  (forall e, In e (find_descendants p G) -> ~ In e Z) ->
  Wk Z X p false.
Proof.
move=> Hdag HX Hnz.
case: (desc_path G p X Hdag.1 Hdag.2 HX) => [Hp | [l [Hdadj _]]].
- left; exact: esym Hp.
- right.
  have Hz : forall z, In z (p :: app l [X]) -> ~ In z Z.
    move=> z Hzin; apply: Hnz.
    exact: (dadj_desc G p _ Hdag.1 Hdag.2 Hdadj
              (node_is_descendant_of_itself p _) z Hzin).
  have HD : OW Z (p :: app l [X]) :=
    conj (dadj_adj _ Hdadj) (open_dadj Z _ Hdag Hdadj Hz).
  case: l Hdadj Hz HD => [|a l'] Hdadj Hz HD.
  + exists X, []; split; first exact: HD.
    split; first by exists [p].
    by case: Hdadj => H _; exact: H.
  + exists a, (app l' [X]); split; first exact: HD.
    split; first by exists (p :: a :: l').
    by case: Hdadj => H _; exact: H.
Qed.

(* walk down a directed path c -> ... -> Y whose nodes avoid Z *)
Lemma wk_down (Z : nodes) (X : node) :
  G_well_formed G = true /\ contains_cycle G = false ->
  forall (l : nodes) (c Y : node) (d : bool),
    dadj (c :: app l [Y]) G ->
    (forall z, In z (c :: app l [Y]) -> ~ In z Z) ->
    Wk Z X c d -> Wk Z X Y true.
Proof.
move=> Hdag l; elim: l => [|a l IH] c Y d Hd HZ Hw.
- case: Hd => Hcy _.
  exact: (wk_out Z X c Y d Hdag Hw (HZ c (or_introl erefl)) Hcy).
- case: Hd => Hca Hd'.
  have Hw' := wk_out Z X c a d Hdag Hw (HZ c (or_introl erefl)) Hca.
  apply: (IH a Y true Hd' _ Hw').
  move=> z Hz; apply: HZ; right; exact: Hz.
Qed.

(* if Y lies below c and no descendant of c is in Z, reach Y from c *)
Lemma wk_to_desc (Z : nodes) (X c Y : node) (d : bool) :
  G_well_formed G = true /\ contains_cycle G = false ->
  Wk Z X c d -> In Y (find_descendants c G) ->
  (forall e, In e (find_descendants c G) -> ~ In e Z) ->
  exists d', Wk Z X Y d'.
Proof.
move=> Hdag Hw HY Hnz.
case: (desc_path G c Y Hdag.1 Hdag.2 HY) => [Hcy | [l [Hdadj _]]].
- by rewrite Hcy; exists d.
- exists true.
  apply: (wk_down Z X Hdag l c Y d Hdadj _ Hw).
  move=> z Hz; apply: Hnz.
  exact: (dadj_desc G c _ Hdag.1 Hdag.2 Hdadj
            (node_is_descendant_of_itself c _) z Hz).
Qed.

(* ---- bookkeeping between Node G, set_nodes and the moral graph ---- *)

Lemma in_set_nodes (t : Node G) (S : {set Node G}) :
  t \in S -> In (ssval t) (set_nodes S).
Proof.
move=> Ht; apply: mem_In; rewrite /set_nodes.
by apply: map_f; rewrite mem_enum.
Qed.

Lemma set_nodes_in (v : Node G) (S : {set Node G}) :
  In (ssval v) (set_nodes S) -> v \in S.
Proof.
move/In_mem; rewrite /set_nodes => /mapP [z Hz Hzv].
have -> : v = z by apply: val_inj; exact: Hzv.
by rewrite -mem_enum.
Qed.

Lemma nin_Z (v : Node G) (S : {set Node G}) :
  v \notin S -> ~ In (ssval v) (set_nodes S).
Proof.
move=> Hv H; exact: (elimT negP Hv (set_nodes_in v S H)).
Qed.

(* a node of An(X,Y,S) with no descendant in S lies above X or Y: reroute *)
Lemma bad_resolve (X Y c : Node G) (S : {set Node G}) (d : bool) :
  G_well_formed G = true /\ contains_cycle G = false ->
  c \in anc_set (X |: (Y |: S)) ->
  (forall e, In e (find_descendants (ssval c) G) -> ~ In e (set_nodes S)) ->
  Wk (set_nodes S) (ssval X) (ssval c) d ->
  (exists d', Wk (set_nodes S) (ssval X) (ssval Y) d') \/
  Wk (set_nodes S) (ssval X) (ssval c) false.
Proof.
move=> Hdag Hc Hnz Hw.
move: Hc; rewrite /anc_set inE => /existsP [t /andP [Ht Hct]].
have Htd : In (ssval t) (find_descendants (ssval c) G) :=
  proj2 (descendants_ancestors_correct G (ssval t) (ssval c)
     (conj (node_in_graph_ssval t) (node_in_graph_ssval c))) (mem_In Hct).
move: Ht; rewrite !inE => /orP [/eqP Htx | /orP [/eqP Hty | HtS]].
- right; rewrite Htx in Htd.
  exact: (wk_up (set_nodes S) (ssval X) (ssval c) Hdag Htd Hnz).
- left; rewrite Hty in Htd.
  exact: (wk_to_desc (set_nodes S) (ssval X) (ssval c) (ssval Y) d Hdag Hw Htd Hnz).
- exfalso; exact: (Hnz _ Htd (in_set_nodes t S HtS)).
Qed.

Lemma moral_adj_r (A : {set Node G}) (a b : Node G) : moral_adj A a b -> b \in A.
Proof.
rewrite /moral_adj => /andP [/andP [/andP [_ _] Hb] _]; exact: Hb.
Qed.

(* ---- one step along the moral path ---- *)
Lemma lift_step (X Y v y : Node G) (S : {set Node G}) :
  G_well_formed G = true /\ contains_cycle G = false ->
  moral_adj_avoid (anc_set (X |: (Y |: S))) S v y ->
  (exists d, Wk (set_nodes S) (ssval X) (ssval v) d) ->
  (exists d, Wk (set_nodes S) (ssval X) (ssval Y) d) \/
  (exists d, Wk (set_nodes S) (ssval X) (ssval y) d).
Proof.
move=> Hdag Hvy [d Hw].
move: Hvy; rewrite /moral_adj_avoid => /andP [/andP [Hm HvS] HyS].
have HvZ : ~ In (ssval v) (set_nodes S) := nin_Z v S HvS.
move: Hm; rewrite /moral_adj => /andP [/andP [/andP [_ HvA] HyA] Hdisj].
case/orP: Hdisj => [/orP [He1 | He2] | Hex].
- (* an edge v -> y *)
  right; exists true.
  exact: (wk_out _ _ _ _ d Hdag Hw HvZ He1).
- (* an edge y -> v *)
  case: d Hw => Hw.
  + case: (boolp.EM (exists e, In e (find_descendants (ssval v) G)
                              /\ In e (set_nodes S))) => [Hd | Hnd].
    * right; exists false.
      exact: (wk_in_from_in _ _ _ _ Hw He2 Hd).
    * case: (bad_resolve X Y v S true Hdag HvA
               (fun e H1 H2 => Hnd (ex_intro _ e (conj H1 H2))) Hw)
        => [Hg | Hw0].
      -- by left.
      -- right; exists false.
         exact: (wk_in_from_out _ _ _ _ Hdag Hw0 HvZ He2).
  + right; exists false.
    exact: (wk_in_from_out _ _ _ _ Hdag Hw HvZ He2).
- (* a common child c of v and y *)
  case/existsP: Hex => c /andP [HcA /andP [Hvc Hyc]].
  have Hwc : Wk (set_nodes S) (ssval X) (ssval c) true :=
    wk_out _ _ _ _ d Hdag Hw HvZ Hvc.
  case: (boolp.EM (exists e, In e (find_descendants (ssval c) G)
                            /\ In e (set_nodes S))) => [Hd | Hnd].
  + right; exists false.
    exact: (wk_in_from_in _ _ _ _ Hwc Hyc Hd).
  + case: (bad_resolve X Y c S true Hdag HcA
             (fun e H1 H2 => Hnd (ex_intro _ e (conj H1 H2))) Hwc)
      => [Hg | Hw0].
    * by left.
    * right; exists false.
      have HcZ : ~ In (ssval c) (set_nodes S).
        move=> HcZ'; apply: Hnd; exists (ssval c); split.
        -- exact: node_is_descendant_of_itself _ _.
        -- exact: HcZ'.
      exact: (wk_in_from_out _ _ _ _ Hdag Hw0 HcZ Hyc).
Qed.

(* ---- the whole moral path ---- *)
Lemma lift_path (X Y : Node G) (S : {set Node G}) :
  G_well_formed G = true /\ contains_cycle G = false ->
  forall (p : seq (Node G)) (v : Node G),
    path (moral_adj_avoid (anc_set (X |: (Y |: S))) S) v p ->
    v \notin S ->
    (exists d, Wk (set_nodes S) (ssval X) (ssval v) d) ->
    (exists d, Wk (set_nodes S) (ssval X) (ssval Y) d) \/
    (exists d, Wk (set_nodes S) (ssval X) (ssval (last v p)) d).
Proof.
move=> Hdag p; elim: p => [|y p IH] v; cbn [path last].
- by move=> _ _ Hv; right.
- move=> /andP [Hvy Hp] HvS Hv.
  case: (lift_step X Y v y S Hdag Hvy Hv) => [Hg | Hy].
  + by left.
  + have HyS : y \notin S.
      by move: Hvy; rewrite /moral_adj_avoid => /andP [_ HyS]; exact: HyS.
    exact: (IH y Hp HyS Hy).
Qed.

(* ---- a walk can be shortened to a path (loop cutting) ---- *)
(* Lemma walk_to_path (Z : nodes) (u v w : node) (K : nodes) :
  G_well_formed G = true /\ contains_cycle G = false ->
  OW Z (u :: w :: K) -> (exists K', u :: w :: K = app K' [v]) -> u <> v ->
  exists l, NoDup (u :: app l [v]) /\ OW Z (u :: app l [v]).
Proof.
Admitted. *)

(* ---- a walk can be shortened to a path (loop cutting) ---- *)
 
(* ================================================================== *)
(* Helpers for walk_to_path                                            *)
(* Idea: strong induction on the length of the walk.  If a node repeats, *)
(*   L = A ++ b :: (B ++ b :: C), cut the loop and get A ++ b :: C.     *)
(* Only the triple at the junction (last A, b, head C) can break; it is  *)
(* repaired by [wp_junction] using the loop b :: B ++ [b], which must    *)
(* contain a collider below b ([wp_chain], [wp_loop_dz]).                *)
(* ================================================================== *)
 
(* ---- pure list helpers ---- *)
Lemma wp_snoc_decomp (A : nodes) : A = [] \/ exists X a, A = X ++ [a].
Proof.
induction A as [|x A IH].
- left; reflexivity.
- right. destruct IH as [HA | [X [a HA]]].
  + exists [], x. subst A. reflexivity.
  + exists (x :: X), a. subst A. reflexivity.
Qed.
 
Lemma wp_not_nodup_split (L : nodes) :
  ~ NoDup L -> exists A b B C, L = A ++ (b :: (B ++ (b :: C))).
Proof.
induction L as [|x L IH]; intros Hn.
- exfalso; apply Hn; constructor.
- destruct (boolp.EM (In x L)) as [Hin | Hnin].
  + destruct (in_split x L Hin) as [B [C E]].
    exists [], x, B, C. subst L. reflexivity.
  + assert (Hnd : ~ NoDup L) by (intros H; apply Hn; constructor; assumption).
    destruct (IH Hnd) as [A [b [B [C E]]]].
    exists (x :: A), b, B, C. subst L. reflexivity.
Qed.
 
Lemma wp_last_app_cons (X : nodes) (y : node) (Y : nodes) (d : node) :
  List.last (X ++ (y :: Y)) d = List.last (y :: Y) d.
Proof.
induction X as [|x X IH].
- reflexivity.
- destruct X as [|x2 X'].
  + reflexivity.
  + exact IH.
Qed.
 
Lemma wp_cut_last (u : node) (A : nodes) (b : node) (B C : nodes) :
  List.last (A ++ (b :: (B ++ (b :: C)))) u = List.last (A ++ (b :: C)) u.
Proof.
  exact (Logic.eq_trans (wp_last_app_cons A b (B ++ (b :: C)) u)
        (Logic.eq_trans (wp_last_app_cons (b :: B) b C u)
                  (Logic.eq_sym (wp_last_app_cons A b C u)))).
Qed.
 
Lemma wp_cut_hd (u : node) (A : nodes) (b : node) (B C : nodes) :
  List.hd u (A ++ (b :: (B ++ (b :: C)))) = List.hd u (A ++ (b :: C)).
Proof. destruct A; reflexivity. Qed.
 
Lemma wp_len_app (B : nodes) (b : node) (C : nodes) :
  le (S (length C)) (length (B ++ (b :: C))).
Proof.
induction B as [|x B IH].
- simpl. apply le_n.
- simpl. apply le_S. exact IH.
Qed.
 
Lemma wp_len_cut (A : nodes) (b : node) (B C : nodes) :
  le (S (length (A ++ (b :: C)))) (length (A ++ (b :: (B ++ (b :: C))))).
Proof.
induction A as [|a A IH].
- simpl. apply le_n_S. exact (wp_len_app B b C).
- simpl. apply le_n_S. exact IH.
Qed.
 
Lemma wp_decomp_ends (L : nodes) (u v : node) :
  List.hd u L = u -> List.last L u = v -> u <> v -> exists l, L = u :: (l ++ [v]).
Proof.
intros Hh Hl Huv. destruct L as [|a T].
- exfalso. apply Huv. exact Hl.
- change (a = u) in Hh. subst a.
  destruct (wp_snoc_decomp T) as [HT | [l [z HT]]].
  + subst T. exfalso. apply Huv. exact Hl.
  + subst T. exists l.
    have Hz : z = v := Logic.eq_trans (Logic.eq_sym (wp_last_app_cons (u :: l) z [] u)) Hl.
    subst z. reflexivity.
Qed.
 
(* ---- adj / open_path: prefixes, windows, joining ---- *)
Lemma wp_adj_app_left (P Q : nodes) : adj (P ++ Q) G -> adj P G.
Proof.
induction P as [|x P IH]; intros H.
- exact I.
- destruct P as [|y P'].
  + exact I.
  + change (adj (x :: y :: (P' ++ Q)) G) in H.
    rewrite adj_cons in H. rewrite adj_cons.
    split; [exact (proj1 H) | exact (IH (proj2 H))].
Qed.
 
Lemma wp_open_app_left (Z P Q : nodes) : open_path G Z (P ++ Q) -> open_path G Z P.
Proof.
induction P as [|x P IH]; intros H.
- exact I.
- destruct P as [|y P'].
  + exact I.
  + destruct P' as [|z P''].
    * exact I.
    * change (open_path G Z (x :: y :: z :: (P'' ++ Q))) in H.
      rewrite open_path_cons3 in H. rewrite open_path_cons3.
      split; [exact (proj1 H) | exact (IH (proj2 H))].
Qed.
 
Lemma wp_open_eq (Z L1 L2 : nodes) : L1 = L2 -> open_path G Z L1 -> open_path G Z L2.
Proof. intros E H. destruct E. exact H. Qed.
 
Lemma wp_open_win (Z X : nodes) (a b c : node) (Rt : nodes) :
  open_path G Z (X ++ (a :: b :: c :: Rt)) -> triple_ok G Z a b c.
Proof.
induction X as [|x X IH]; intros H.
- change (open_path G Z (a :: b :: c :: Rt)) in H.
  rewrite open_path_cons3 in H. exact (proj1 H).
- exact (IH (open_path_tail G Z x _ H)).
Qed.
 
Lemma wp_open_win_hd (Z X : nodes) (a b a' : node) (B0 Rt : nodes) :
  open_path G Z (X ++ (a :: b :: (B0 ++ (a' :: Rt)))) ->
  triple_ok G Z a b (List.hd a' B0).
Proof.
destruct B0 as [|c B0']; intros H.
- exact (wp_open_win Z X a b a' Rt H).
- exact (wp_open_win Z X a b c (B0' ++ (a' :: Rt)) H).
Qed.
 
Lemma wp_open_prefix2 (Z X : nodes) (a b : node) (Rt : nodes) :
  open_path G Z (X ++ (a :: b :: Rt)) -> open_path G Z (X ++ [a; b]).
Proof.
intros H.
exact (wp_open_app_left Z (X ++ [a; b]) Rt
         (wp_open_eq Z _ _ (app_assoc X [a; b] Rt) H)).
Qed.
 
Lemma wp_open_prefix_b (Z A : nodes) (b : node) (Rt : nodes) :
  open_path G Z (A ++ (b :: Rt)) -> open_path G Z (A ++ [b]).
Proof.
intros H.
exact (wp_open_app_left Z (A ++ [b]) Rt
         (wp_open_eq Z _ _ (app_assoc A [b] Rt) H)).
Qed.
 
Lemma wp_open_join (Z X : nodes) (a b : node) (Y : nodes) :
  open_path G Z (X ++ [a; b]) -> open_path G Z (a :: b :: Y) ->
  open_path G Z (X ++ (a :: b :: Y)).
Proof.
induction X as [|x X IH]; intros H1 H2.
- exact H2.
- destruct X as [|y X'].
  + change (open_path G Z (x :: a :: b :: [])) in H1.
    change (open_path G Z (x :: a :: b :: Y)).
    rewrite open_path_cons3 in H1. rewrite open_path_cons3.
    exact (conj (proj1 H1) H2).
  + have H1' : open_path G Z ((y :: X') ++ [a; b]) := open_path_tail G Z x _ H1.
    have H3 := IH H1' H2.
    destruct X' as [|z X''].
    * change (open_path G Z (x :: y :: a :: b :: [])) in H1.
      change (open_path G Z (x :: y :: a :: b :: Y)).
      rewrite open_path_cons3 in H1. rewrite open_path_cons3.
      exact (conj (proj1 H1) H3).
    * change (open_path G Z (x :: y :: z :: (X'' ++ [a; b]))) in H1.
      change (open_path G Z (x :: y :: z :: (X'' ++ (a :: b :: Y)))).
      rewrite open_path_cons3 in H1. rewrite open_path_cons3.
      exact (conj (proj1 H1) H3).
Qed.
 
Lemma wp_adj_splice (A : nodes) (b : node) (B C : nodes) :
  adj (A ++ (b :: (B ++ (b :: C)))) G -> adj (A ++ (b :: C)) G.
Proof.
induction A as [|a A IH]; intros H.
- exact (adj_app_right (b :: B) (b :: C) G H).
- destruct A as [|a2 A'].
  + change (adj (a :: b :: (B ++ (b :: C))) G) in H.
    change (adj (a :: b :: C) G).
    rewrite adj_cons in H. rewrite adj_cons.
    split; [exact (proj1 H)
           | exact (adj_app_right (b :: B) (b :: C) G (proj2 H))].
  + change (adj (a :: a2 :: (A' ++ (b :: (B ++ (b :: C))))) G) in H.
    change (adj (a :: a2 :: (A' ++ (b :: C))) G).
    rewrite adj_cons in H. rewrite adj_cons.
    split; [exact (proj1 H) | exact (IH (proj2 H))].
Qed.
 
(* ---- the loop b :: B ++ [b] ---- *)
Lemma wp_loop_sub (Z : nodes) (b : node) (B C : nodes) :
  adj (b :: (B ++ (b :: C))) G -> open_path G Z (b :: (B ++ (b :: C))) ->
  adj (b :: (B ++ [b])) G /\ open_path G Z (b :: (B ++ [b])).
Proof.
intros Ha Ho.
have E : (b :: (B ++ [b])) ++ C = b :: (B ++ (b :: C)) :=
  f_equal (cons b) (Logic.eq_sym (app_assoc B [b] C)).
split.
- apply (wp_adj_app_left (b :: (B ++ [b])) C). rewrite E. exact Ha.
- exact (wp_open_app_left Z (b :: (B ++ [b])) C
           (wp_open_eq Z _ _ (Logic.eq_sym E) Ho)).
Qed.
 
Lemma wp_edge_dir (x y : node) :
  (is_edge (x, y) G = true \/ is_edge (y, x) G = true) ->
  is_edge (y, x) G = false -> is_edge (x, y) G = true.
Proof.
intros [H | H] Hf.
- exact H.
- rewrite Hf in H. discriminate H.
Qed.
 
(* an open walk starting with p -> q either has a collider below p with a
   descendant in Z, or is a directed chain *)
Lemma wp_chain (Z : nodes) :
  G_well_formed G = true /\ contains_cycle G = false ->
  forall (M : nodes) (p q : node),
    open_path G Z (p :: q :: M) -> adj (p :: q :: M) G ->
    is_edge (p, q) G = true ->
    (exists d, In d (find_descendants p G) /\ In d Z) \/ dadj (p :: q :: M) G.
Proof.
intros Hdag M.
induction M as [|r M IH]; intros p q Ho Ha Hpq.
- right. rewrite dadj_cons. split; [exact Hpq | exact I].
- rewrite open_path_cons3 in Ho. destruct Ho as [Ht Ho'].
  have Ha1 := Ha. rewrite adj_cons in Ha1. destruct Ha1 as [_ Ha2].
  have Ha3 := Ha2. rewrite adj_cons in Ha3. destruct Ha3 as [Hqr _].
  destruct (is_edge (r, q) G) eqn:Erq.
  + left. destruct Ht as [Ht1 _].
    destruct (Ht1 (conj Hpq Erq)) as [d [Hd HdZ]].
    exists d. split; [| exact HdZ].
    exact (desc_trans G d q p Hdag.1 Hdag.2
             (desc_edge G p q Hdag.1 Hdag.2 Hpq) Hd).
  + assert (is_edge (q, r) G = true \/ is_edge (r, q) G = true).
      rewrite Erq.
      exact Hqr.
    have Hqr' := wp_edge_dir q r H Erq.
    destruct (IH q r Ho' Ha2 Hqr') as [[d [Hd HdZ]] | Hdq].
    * left. exists d. split; [| exact HdZ].
      exact (desc_trans G d q p Hdag.1 Hdag.2
               (desc_edge G p q Hdag.1 Hdag.2 Hpq) Hd).
    * right. rewrite dadj_cons. split; [exact Hpq | exact Hdq].
Qed.
 
(* a loop b -> c ... a' <- b ... cannot be directed throughout *)
Lemma wp_loop_dz (Z : nodes) :
  G_well_formed G = true /\ contains_cycle G = false ->
  forall (b a' : node) (B0 : nodes),
    adj (b :: ((B0 ++ [a']) ++ [b])) G ->
    open_path G Z (b :: ((B0 ++ [a']) ++ [b])) ->
    is_edge (List.hd a' B0, b) G = false -> is_edge (a', b) G = false ->
    exists d, In d (find_descendants b G) /\ In d Z.
Proof.
intros Hdag b a' B0 Ha Ho H1 H2.
have E : b :: ((B0 ++ [a']) ++ [b]) = b :: (B0 ++ [a'; b]) :=
  f_equal (cons b) (Logic.eq_sym (app_assoc B0 [a'] [b])).
rewrite E in Ha. rewrite E in Ho.
destruct B0 as [|c B0'].
- assert (Hba : is_edge (b, a') G = true).
  { have Ha1 := Ha.
    change (adj (b :: a' :: b :: []) G) in Ha1.
    rewrite adj_cons in Ha1. destruct Ha1 as [Hx _].
    exact (wp_edge_dir b a' Hx H2). }
  destruct (wp_chain Z Hdag [b] b a' Ho Ha Hba) as [Hd | Hdadj].
  + exact Hd.
  + exfalso.
    change (dadj (b :: a' :: b :: []) G) in Hdadj.
    rewrite dadj_cons in Hdadj. destruct Hdadj as [_ Hd2].
    rewrite dadj_cons in Hd2. destruct Hd2 as [Hd3 _].
    rewrite H2 in Hd3. discriminate Hd3.
- change (is_edge (c, b) G = false) in H1.
  assert (Hbc : is_edge (b, c) G = true).
  { have Ha1 := Ha.
    change (adj (b :: c :: (B0' ++ [a'; b])) G) in Ha1.
    rewrite adj_cons in Ha1. destruct Ha1 as [Hx _].
    exact (wp_edge_dir b c Hx H1). }
  destruct (wp_chain Z Hdag (B0' ++ [a'; b]) b c Ho Ha Hbc) as [Hd | Hdadj].
  + exact Hd.
  + exfalso.
    have Hl : dadj [a'; b] G :=
      dadj_app_right (b :: c :: B0') [a'; b] G Hdadj.
    rewrite dadj_cons in Hl. destruct Hl as [Hd3 _].
    rewrite H2 in Hd3. discriminate Hd3.
Qed.
 
(* the junction triple of the shortened walk *)
Lemma wp_junction (Z : nodes) (a b c a' c1 : node) :
  triple_ok G Z a b c -> triple_ok G Z a' b c1 ->
  (is_edge (c, b) G = false -> is_edge (a', b) G = false ->
     exists d, In d (find_descendants b G) /\ In d Z) ->
  triple_ok G Z a b c1.
Proof.
intros [T1a T1b] [T2a T2b] Hl. split.
- intros [Hab Hc1b].
  destruct (is_edge (c, b) G) eqn:E1.
  + apply T1a. split. exact Hab. reflexivity.
  + destruct (is_edge (a', b) G) eqn:E2.
    * apply T2a. split. reflexivity. exact Hc1b.
    * apply Hl; reflexivity.
- intros Hn.
  destruct (is_edge (a, b) G) eqn:Eab.
  + destruct (is_edge (c1, b) G) eqn:Ec1.
    * exfalso. apply Hn. split; reflexivity.
    * apply T2b. intros [_ H]. discriminate H.
  + apply T1b. intros [H _]. discriminate H.
Qed.
 
(* cutting a loop keeps the walk open *)
Lemma wp_open_splice (Z : nodes) :
  G_well_formed G = true /\ contains_cycle G = false ->
  forall (A : nodes) (b : node) (B C : nodes),
    adj (A ++ (b :: (B ++ (b :: C)))) G ->
    open_path G Z (A ++ (b :: (B ++ (b :: C)))) ->
    open_path G Z (A ++ (b :: C)).
Proof.
intros Hdag A b B C Hadj Hopen.
have Hsuf : open_path G Z (b :: C) :=
  open_path_app_right G Z (b :: B) (b :: C)
    (open_path_app_right G Z A (b :: (B ++ (b :: C))) Hopen).
assert (HBne : B <> []).
{ intros HB. subst B.
  have Ha1 : adj (b :: b :: C) G :=
    adj_app_right A (b :: ([] ++ (b :: C))) G Hadj.
  rewrite adj_cons in Ha1.
  destruct Ha1 as [[H | H] _];
    exact (no_two_cycle G b b Hdag.1 Hdag.2 H H). }
destruct (wp_snoc_decomp A) as [HA | [X [a HA]]].
- subst A. exact Hsuf.
- subst A.
  destruct C as [|c1 C'].
  + exact (wp_open_prefix_b Z (X ++ [a]) b (B ++ [b]) Hopen).
  + destruct (wp_snoc_decomp B) as [HB | [B0 [a' HB]]].
    * exfalso. exact (HBne HB).
    * subst B.
      have HaS : adj (b :: ((B0 ++ [a']) ++ (b :: c1 :: C'))) G :=
        adj_app_right (X ++ [a]) _ G Hadj.
      have HoS : open_path G Z (b :: ((B0 ++ [a']) ++ (b :: c1 :: C'))) :=
        open_path_app_right G Z (X ++ [a]) _ Hopen.
      have HW := wp_loop_sub Z b (B0 ++ [a']) (c1 :: C') HaS HoS.
      have HNa : open_path G Z
          (X ++ (a :: b :: ((B0 ++ [a']) ++ (b :: c1 :: C')))) :=
        wp_open_eq Z _ _
          (Logic.eq_sym (app_assoc X [a]
                    (b :: ((B0 ++ [a']) ++ (b :: c1 :: C'))))) Hopen.
      have HN : open_path G Z
          (X ++ (a :: b :: (B0 ++ (a' :: b :: c1 :: C')))) :=
        wp_open_eq Z _ _
          (f_equal (fun r => X ++ (a :: b :: r))
                   (Logic.eq_sym (app_assoc B0 [a'] (b :: c1 :: C')))) HNa.
      have HN2 : open_path G Z
          ((X ++ (a :: b :: B0)) ++ (a' :: b :: c1 :: C')) :=
        wp_open_eq Z _ _
          (app_assoc X (a :: b :: B0) (a' :: b :: c1 :: C')) HN.
      have T1 := wp_open_win_hd Z X a b a' B0 (b :: c1 :: C') HN.
      have T2 := wp_open_win Z (X ++ (a :: b :: B0)) a' b c1 C' HN2.
      have Hjn := wp_junction Z a b (List.hd a' B0) a' c1 T1 T2
                    (fun E1 E2 => wp_loop_dz Z Hdag b a' B0 HW.1 HW.2 E1 E2).
      have Hpre := wp_open_prefix2 Z X a b (B0 ++ (a' :: b :: c1 :: C')) HN.
      assert (Hpost : open_path G Z (a :: b :: c1 :: C'))
        by (rewrite open_path_cons3; exact (conj Hjn Hsuf)).
      have Hg := wp_open_join Z X a b (c1 :: C') Hpre Hpost.
      exact (wp_open_eq Z _ _ (app_assoc X [a] (b :: c1 :: C')) Hg).
Qed.
 
(* strong induction on the length: remove loops until the walk is NoDup *)
Lemma wp_shorten (Z : nodes) (u v : node) :
  G_well_formed G = true /\ contains_cycle G = false ->
  u <> v ->
  forall (n : nat) (L : nodes),
    le (length L) n -> adj L G -> open_path G Z L ->
    List.hd u L = u -> List.last L u = v ->
    exists l, NoDup (u :: (l ++ [v])) /\ adj (u :: (l ++ [v])) G /\
              open_path G Z (u :: (l ++ [v])).
Proof.
intros Hdag Huv n.
induction n as [|n IH]; intros L Hlen Hadj Hopen Hh Hl.
- destruct L as [|x L'].
  + exfalso. apply Huv. exact Hl.
  + exfalso. simpl in Hlen. inversion Hlen.
- destruct (boolp.EM (NoDup L)) as [Hnd | Hnnd].
  + destruct (wp_decomp_ends L u v Hh Hl Huv) as [l HL].
    exists l. subst L. exact (conj Hnd (conj Hadj Hopen)).
  + destruct (wp_not_nodup_split L Hnnd) as [A [b [B [C HL]]]].
    subst L.
    have Hlen' : le (length (A ++ (b :: C))) n :=
      le_S_n _ _ (Nat.le_trans _ _ _ (wp_len_cut A b B C) Hlen).
    exact (IH (A ++ (b :: C)) Hlen'
             (wp_adj_splice A b B C Hadj)
             (wp_open_splice Z Hdag A b B C Hadj Hopen)
             (Logic.eq_trans (Logic.eq_sym (wp_cut_hd u A b B C)) Hh)
             (Logic.eq_trans (Logic.eq_sym (wp_cut_last u A b B C)) Hl)).
Qed.
 
Lemma walk_to_path (Z : nodes) (u v w : node) (K : nodes) :
  G_well_formed G = true /\ contains_cycle G = false ->
  OW Z (u :: w :: K) -> (exists K', u :: w :: K = app K' [v]) -> u <> v ->
  exists l, NoDup (u :: app l [v]) /\ OW Z (u :: app l [v]).
Proof.
intros Hdag [Hadj Hopen] [K' HK] Huv.
have Hl : List.last (u :: w :: K) u = v :=
  eq_trans (f_equal (fun l => List.last l u) HK) (wp_last_app_cons K' v [] u).
destruct (wp_shorten Z u v Hdag Huv (length (u :: w :: K)) (u :: w :: K)
            (le_n _) Hadj Hopen Logic.eq_refl Hl) as [l [Hnd [Hadj' Hopen']]].
exists l. split; [exact Hnd | split; [exact Hadj' | exact Hopen']].

Qed.

(* final step: an open walk Y ~> X contradicts d-separation *)
Lemma end_case (X Y : Node G) (S : {set Node G}) (d : bool) :
  G_well_formed G = true /\ contains_cycle G = false ->
  X != Y ->
  d_separated_bool (ssval X) (ssval Y) G (set_nodes S) = true ->
  Wk (set_nodes S) (ssval X) (ssval Y) d -> False.
Proof.
move=> Hdag Hne Hd [HYX | [w [K [Hw [Hlast _]]]]].
- have E : Y = X := val_inj HYX.
  by rewrite -E eqxx in Hne.
- have Hne' : ssval Y <> ssval X.
    move=> E; have E' : Y = X := val_inj E.
    by rewrite E' eqxx in Hne.
  case: (walk_to_path (set_nodes S) (ssval Y) (ssval X) w K Hdag Hw Hlast Hne')
    => l [Hnd [Hadj Hopen]].
  have Hconn : d_connected_2 (ssval Y, ssval X, l) G (set_nodes S) :=
    open_d_connected G (set_nodes S) _ _ l Hdag.1 Hdag.2 Hadj Hopen.
  have Hsep' : d_separated_bool (ssval Y) (ssval X) G (set_nodes S) = false.
    apply: (proj2 (d_separated_vs_connected (ssval Y) (ssval X) G
                    (set_nodes S) Hdag)).
    exists l; split; first exact: (nodup_acyclic2 _ _ _ Hnd).
    split; first exact: (adj_path _ _ _ _ Hadj).
    exact: Hconn.
  have Hs := d_separated_symmetry (ssval X) (ssval Y) G (set_nodes S) Hdag Hd.
  by rewrite Hsep' in Hs.
Qed.

(* d-separation implies moral separation *)
Lemma dsep_implies_moral_sep (X Y : Node G) (S : {set Node G}) :
  G_well_formed G = true /\ contains_cycle G = false ->
  X != Y -> X \notin S -> Y \notin S ->
  d_separated_bool (ssval X) (ssval Y) G (set_nodes S) = true ->
  moral_sep (anc_set (X |: (Y |: S))) S X Y.
Proof.
move=> Hdag Hne HXS HYS Hd.
rewrite /moral_sep; apply/negP => Hconn.
case/connectP: Hconn => p Hp Hlast.
have HX0 : exists d, Wk (set_nodes S) (ssval X) (ssval X) d.
  by exists true; left.
case: (lift_path X Y S Hdag p X Hp HXS HX0) => [[d Hg] | [d Hl]].
- exact: (end_case X Y S d Hdag Hne Hd Hg).
- rewrite -Hlast in Hl.
  exact: (end_case X Y S d Hdag Hne Hd Hl).
Qed.

(* ------------------------------------------------------------------ *)
(* Main lemma                                                          *)
(* ------------------------------------------------------------------ *)

(* d-separation implies conditional independence (global Markov property):
   if X and Y are d-separated by Z in a well-formed acyclic G, then the solved
   values of X and Y are independent given the solved values of Z. *)
Lemma dsep_implies_cond_indep (X Y : Node G) (Z : {set Node G}) :
  G_well_formed G = true /\ contains_cycle G = false ->
  X != Y ->
  d_separated_bool (ssval X) (ssval Y) G (set_nodes Z) = true ->
  Pc |= nodeRV X _|_ nodeRV Y | setRV Z.
Proof.
  move=> Hdag Hne Hd.
  case: (boolP (X \in Z)) => [HX | HX]; first exact: cinde_X_in_Z.
  case: (boolP (Y \in Z)) => [HY | HY]; first exact: cinde_Y_in_Z.
  have Hm := dsep_implies_moral_sep X Y Z Hdag Hne HX HY Hd.
  exact: (cinde_of_moral_sep X Y Z Hdag Hne HX HY Hm).
Qed.

(* Print Assumptions dsep_implies_cond_indep. *)

End DSepImpliesCondIndep.
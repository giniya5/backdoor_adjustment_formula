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
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Arith.EqNat. Import Nat.
From Stdlib Require Import Lia.
From Stdlib Require Import FunctionalExtensionality.
From mathcomp Require Import all_ssreflect ssralg ssrnum finalg reals matrix.
From infotheo Require Import ssr_ext ssralg_ext fdist proba.
Import Order.POrderTheory Order.TotalTheory GRing.Theory Num.Theory.

Import ListNotations.

Section NodeRVs.

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

Definition Pc : R.-fdist (context dom) := fdist_context Pn.

(* Hypothesis encK : forall n : Node G, cancel (enc n) (dec n). *)

(* U_n : the node's unobserved variable (e.g. UTRV, UHRV, ...) *)
Definition unobsRV (n : Node G) : {RV Pc -> dom n} := fun w => w n.

(* the node's solved value (e.g. T, H, C, E, ...) *)
Definition nodeRV (n : Node G) : {RV Pc -> dom n} :=
  fun w => solve enc dec tF w n.

(* the node under do(n0 := t) (e.g. Hinterv t, Cinterv t, ...) *)
Definition solve_do (n0 : Node G) (t : dom n0) (w : context dom) (n : Node G)
    : dom n :=
  dec n (Main.eval (do (ssval n0) G)
           (do_graphfun (ssval n0) (enc n0 t) (elab enc dec tF))
           (ssval n) (to_assign enc w)).

Definition doRV (n0 : Node G) (t : dom n0) (n : Node G) : {RV Pc -> dom n} :=
  fun w => solve_do n0 t w n.

(* an intervention: a list of nodes, each paired with a value in its own domain *)
Definition intervention := seq {n : Node G & dom n}.

(* cut the incoming edges of every intervened node *)
Definition do_graph (l : intervention) : graph :=
  foldr (fun p g => do (ssval (tag p)) g) G l.

(* replace the mechanism of every intervened node by its constant *)
Definition do_fun (l : intervention) : @graphfun nat :=
  foldr (fun p g => do_graphfun (ssval (tag p)) (enc (tag p) (tagged p)) g)
        (elab enc dec tF) l.

(* node n under do(l) *)
Definition solve_do_list (l : intervention) (w : context dom) (n : Node G)
    : dom n :=
  dec n (Main.eval (do_graph l) (do_fun l) (ssval n) (to_assign enc w)).

(* the single-node version is the one-element case; this should hold by
   [reflexivity], since [foldr] on a singleton unfolds definitionally *)
Lemma solve_do_list1 (n0 : Node G) (t : dom n0) w n :
  solve_do_list [:: Tagged dom t] w n = solve_do n0 t w n.
Proof. by []. Qed.

(* convenience: intervene on a set S of nodes, with the values given by t *)
Definition solve_do_set (S : {set Node G}) (t : forall n : Node G, dom n) :=
  solve_do_list [seq Tagged dom (t n) | n <- enum S].

Definition doRV_list (l : intervention) (n : Node G) : {RV Pc -> dom n} :=
  fun w => solve_do_list l w n.

(* the values of the declared parents of n, bundled as one RV.
   An entry is indexed by a parent p, with the [is_parent n p] ticket
   carried in the subtype, and lives in p's own domain. *)
Definition paRV (n : Node G) :
  {RV Pc -> {dffun forall p : {p : Node G | is_parent n p}, dom (sval p)}} :=
  fun w => [ffun p => nodeRV (sval p) w].

(* the whole solved world, as one RV *)
Definition worldRV : {RV Pc -> world dom} :=
  fun w => world_of enc dec tF w.

(* read the parent values of n off a full assignment v *)
Definition pa_of (v : world dom) (n : Node G) :
  {dffun forall p : {p : Node G | is_parent n p}, dom (sval p)} :=
  [ffun p => v (sval p)].

End NodeRVs.
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
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Arith.EqNat. Import Nat.
From Stdlib Require Import Lia.
From mathcomp Require Import all_ssreflect ssralg ssrnum finalg reals matrix.
From infotheo Require Import ssr_ext ssralg_ext fdist proba.
Import Order.POrderTheory Order.TotalTheory GRing.Theory Num.Theory.

Import ListNotations.

Section MarkovFactorization.

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

(* Definition Pc : R.-fdist (context dom) := fdist_context Pn. *)

Local Notation Pc       := (@Pc R G dom Pn).
Local Notation unobsRV  := (@unobsRV R G dom Pn).
Local Notation nodeRV   := (@nodeRV R G dom enc dec Pn tF).
Local Notation paRV     := (@paRV R G dom enc dec Pn tF).
Local Notation worldRV  := (@worldRV R G dom enc dec Pn tF).
Local Notation pa_of    := (@pa_of G dom).
Local Notation solve_do_list := (@solve_do_list G dom enc dec tF).

Hypothesis encK : forall n : Node G, cancel (enc n) (dec n).

(*(* Markov factorization: on a well-formed acyclic graph, the joint law of
   the solved nodes is the product over nodes of
   P(node = its value | its parents = their values). *)
Lemma markov_factorization (v : world dom) :
  G_well_formed G = true /\ contains_cycle G = false ->
  `Pr[ worldRV = v ] =
  (\prod_(n : Node G) `Pr[ (nodeRV n) = v n | (paRV n) = (pa_of v n) ])%R.
Proof. 
Admitted.*)

(* ------------------------------------------------------------------ *)
(* ------------------------------------------------------------------ *)
(* ------------------------------------------------------------------ *)
(* PROOF OF MARKOV FACTORIZATION                                      *)
(* ------------------------------------------------------------------ *)
(* ------------------------------------------------------------------ *)
(* ------------------------------------------------------------------ *)

(* ------------------------------------------------------------------ *)
(* helper definitions used by the statements                           *)
(* ------------------------------------------------------------------ *)

(* the parent view of node n obtained by reading a full assignment v *)
Definition pa_view (v : world dom) (n : Node G) : parent_view dom n :=
  fun p _ => v p.

(* noise values for which node n produces v n when its parents read v *)
Definition A_set (v : world dom) (n : Node G) : {set dom n} :=
  [set u | tF n u (pa_view v n) == v n].

(* a default value in every node's domain (nonempty: Pn m is an fdist) *)
Definition j0 (m : Node G) : dom m := sval (fdist_supp_mem (Pn m)).

(* the noise with node n's own slot reset to a default *)
Definition unobs_rest (n : Node G) : {RV Pc -> context dom} :=
  fun w => [ffun m => if m == n then j0 m else w m].

(* ---- marginal: Pr[U_n = v] = Pn n v ---- *)
Check unobsRV.
Lemma pfwd1_unobs (n : Node G) (v : dom n) : `Pr[ (unobsRV n) = v ] = Pn n v.
Proof.
  rewrite -dist_of_RVE.
  exact: (congr1 (fun d : R.-fdist (dom n) => d v) (fdist_context_marginal Pn n)).
Qed.

(* ---- mutual independence: the joint law of ALL the U_n is the product ---- *)
Definition unobs_all : {RV Pc -> context dom} := fun w => w.

Lemma unobs_all_prod (w : context dom) :
  `Pr[ unobs_all = w ] = (\prod_(n : Node G) `Pr[ (unobsRV n) = w n ])%R.
Proof.
  rewrite pfwd1E /Pr.
  have -> : finset (unobs_all @^-1 w) = [set w] by apply/setP => v; rewrite !inE.
  rewrite big_set1 /Pc fdist_contextE.
  by apply: eq_bigr => n _; rewrite pfwd1_unobs.
Qed.

(* ------------------------------------------------------------------ *)
(* L1: product sets have product probability                           *)
(* ------------------------------------------------------------------ *)
Lemma Pr_prod_set (S : forall n : Node G, {set dom n}) :
  Pr Pc [set w : context dom | [forall n, w n \in S n]]
  = (\prod_(n : Node G) Pr (Pn n) (S n))%R.
Proof.
  pose j0 (n : Node G) : dom n := sval (fdist_supp_mem (Pn n)).
  (* a product of 0/1 indicators is the indicator of "all true" *)
  have prod_ind (w : context dom) :
      \prod_(m : Node G) (if w m \in S m then (1 : R) else 0)
      = (if [forall m, w m \in S m] then (1 : R) else 0).
    case: ifPn => [/forallP H | H].
    - by apply: big1 => m _; rewrite (H m).
    - move: H; rewrite negb_forall => /existsP [m0 Hm0].
      by rewrite (bigD1 m0) //= (negbTE Hm0) /= mul0r.
  (* step 1: put the indicator of the event inside the product *)
  transitivity (\sum_(w : context dom) \prod_(m : Node G)
      ((if w m \in S m then (1 : R) else 0) * Pn m (w m))).
    rewrite /Pr /Pc big_mkcond /=; apply: eq_bigr => w _.
    rewrite inE /= big_split /= prod_ind -fdist_contextE.
    by case: ifP => _; rewrite ?mul1r ?mul0r.
  (* step 2: sums over functions distribute over the product *)
  rewrite -(bigA_distr_big_dffun j0 (fun m (j : dom m) =>
    (if j \in S m then (1 : R) else 0) * Pn m j)) /=.
  (* step 3: each factor is the mass of S m *)
  apply: eq_bigr => m _.
  rewrite /Pr.
  transitivity (\sum_(j : dom m) (if j \in S m then Pn m j else 0))%R.
    by apply: eq_bigr => j _; case: (j \in S m); rewrite /= ?mul1r ?mul0r.
  by rewrite -big_mkcond.
Qed.

(* ------------------------------------------------------------------ *)
(* L2: structural equation                                             *)
(* the solved value of n is n's mechanism applied to its own noise and *)
(* the solved values of its parents                                    *)
(* ------------------------------------------------------------------ *)
(* the i-th parent value read positionally equals the value assigned to that parent *)
Lemma get_parent_assignments_nth (A : assignments nat) (L : nodes)
    (l : list nat) (m x : nat) :
  get_parent_assignments A L = Some l -> m \in L ->
  get_assigned_value A m = Some x ->
  List.nth_default 0 l (index m L) = x.
Proof.
  elim: L l => [|h t IH] l.
  - by move=> _ Hm; rewrite in_nil in Hm.
  - move=> /=; case Hh: (get_assigned_value A h) => [xh|] //.
    case Ht: (get_parent_assignments A t) => [l'|] // [<-].
    rewrite inE => Hin.
    case Hmh: (m == h).
    + move/eqP: Hmh => Hmh; rewrite Hmh Hh => -[<-].
      by rewrite /= eqxx.
    + have Hmt : m \in t by move: Hin; rewrite Hmh.
      move=> Hm.
      have := IH l' Ht Hmt Hm.
      by rewrite /= eq_sym Hmh.
Qed.

(* L2: the structural equation *)
Lemma solve_eq (w : context dom) (n : Node G) :
  G_well_formed G = true /\ contains_cycle G = false ->
  solve enc dec tF w n
  = tF n (w n) (fun p (_ : is_parent n p) => solve enc dec tF w p).
Proof using encK.
  move=> [Hwf Hcyc].
  (* dsep-core: value of n = n's function applied to (noise, parent values) *)
  have [P [HP [pa [Hpa [unobs [HU Hfv]]]]]] :=
    find_value_evaluates_to_g G (elab enc dec tF) (to_assign enc w) (ssval n)
      (conj (conj Hwf Hcyc)
            (conj (to_assign_complete enc w) (node_in_graph_ssval n))).
  (* the noise it reads is the code of n's noise *)
  rewrite (to_assign_get enc w n) in HU.
  case: HU => Hun; subst unobs.
  (* so Main.eval n is that application *)
  have Hval := find_value_to_assign enc dec tF w n Hwf Hcyc.
  rewrite Hfv in Hval; case: Hval => Heq.
  (* unwinding elab at n: enc . tF n . dec, with encK on the noise *)
  have Helab : elab enc dec tF (ssval n) (enc n (w n), pa)
    = enc n (tF n (w n)
        (fun p (_ : is_parent n p) =>
          dec p (List.nth_default 0 pa
                    (index (ssval p) (find_parents (ssval n) G))))).
    by rewrite /elab o_node_self /= encK.
  rewrite /solve -Heq Helab encK.
  (* the two parent views agree at every declared parent p *)
  congr (tF n (w n) _).
  apply: boolp.functional_extensionality_dep => p; apply: boolp.funext => hp.
  congr (dec p _).
  have Hm : List.In (ssval p) (find_parents (ssval n) G) := mem_In hp.
  have Hxp := find_value_to_assign enc dec tF w p Hwf Hcyc.
  have Hget := find_values_get_assigned _ _ _ _ _ _ _ _ _ (conj HP (conj Hm Hxp)).
  exact: get_parent_assignments_nth (esym Hpa) hp Hget.
Qed.

(* ------------------------------------------------------------------ *)
(* L3: the parent relation is well-founded on an acyclic graph         *)
(* ------------------------------------------------------------------ *)
(* edge_in_graph only looks at the edge list *)
Lemma edge_in_graph_snd (H : graph) (e : edge) :
  edge_in_graph e H = member_edge e (snd H).
Proof. by case: H. Qed.

(* a declared parent gives a (well-formed) edge parent -> child *)
Lemma is_parent_edge (n p : Node G) :
  G_well_formed G = true -> is_parent n p ->
  is_edge (ssval p, ssval n) G = true.
Proof.
  move=> Hwf Hp.
  have Hin : List.In (ssval p) (find_parents (ssval n) G) := mem_In Hp.
  have Hedge := (edge_from_parent_to_child (ssval n) (ssval p) G).1 Hin.
  rewrite edge_in_graph_snd in Hedge.
  exact: in_is_edge _ _ _ Hwf ((member_edge_In_equiv _ _).1 Hedge).
Qed.

(* a child is a descendant of each of its parents *)
Lemma parent_is_descendant (n p : Node G) :
  G_well_formed G = true -> contains_cycle G = false -> is_parent n p ->
  List.In (ssval n) (find_descendants (ssval p) G).
Proof.
  move=> Hwf Hcyc Hp.
  apply (proj2 (find_descendants_correct G (ssval p) (ssval n) Hwf Hcyc)).
  right; exists (ssval p, ssval n, []); split.
  - by rewrite /is_directed_path_in_graph /= (is_parent_edge n p Hwf Hp).
  - by rewrite /path_start_and_end /= !Nat.eqb_refl.
Qed.

(* ancestors of a parent are ancestors of the child *)
Lemma ancestors_mono (n p m : Node G) :
  G_well_formed G = true -> contains_cycle G = false -> is_parent n p ->
  List.In (ssval m) (find_ancestors (ssval p) G) ->
  List.In (ssval m) (find_ancestors (ssval n) G).
Proof.
  move=> Hwf Hcyc Hp Hm.
  apply (proj1 (descendants_ancestors_correct G (ssval n) (ssval m)
          (conj (node_in_graph_ssval n) (node_in_graph_ssval m)))).
  apply: (descendants_transitive G (ssval n) (ssval p) (ssval m) Hwf Hcyc).
  split.
  - exact: (proj2 (descendants_ancestors_correct G (ssval p) (ssval m)
            (conj (node_in_graph_ssval p) (node_in_graph_ssval m))) Hm).
  - exact: parent_is_descendant.
Qed.

(* in a DAG, a child is never an ancestor of its own parent *)
Lemma child_not_ancestor_of_parent (n p : Node G) :
  G_well_formed G = true /\ contains_cycle G = false ->
  is_parent n p -> ssval n \notin find_ancestors (ssval p) G.
Proof.
  move=> [Hwf Hcyc] Hp; apply/negP => Hn.
  have Hd := (proj2 (descendants_ancestors_correct G (ssval p) (ssval n)
                (conj (node_in_graph_ssval p) (node_in_graph_ssval n)))) (mem_In Hn).
  have He := is_parent_edge n p Hwf Hp.
  case: (proj1 (find_descendants_correct G (ssval n) (ssval p) Hwf Hcyc) Hd)
    => [Hnp | [[[a b] l] [Hdir Hse]]].
  - (* n = p would be a self-loop *)
    rewrite Hnp in He.
    by rewrite (acyclic_no_self_loop G (ssval p) Hwf Hcyc) in He.
  - (* a path n ~> p plus the edge p -> n is a cycle *)
    move: Hse; rewrite /path_start_and_end /=.
    move=> /andP[/Nat.eqb_spec Ha /Nat.eqb_spec Hb]; subst a b.
    have Hdir2 := directed_path_extend_last G (ssval n) (ssval p) l (ssval n) Hdir He.
    have Hac := contains_cycle_false_correct G _ Hwf Hcyc Hdir2.
    by case: Hac => Hne _; apply: Hne.
Qed.

Lemma parent_wf :
  G_well_formed G = true /\ contains_cycle G = false ->
  well_founded (fun p n : Node G => is_parent n p = true).
Proof.
  move=> [Hwf Hcyc].
  pose anc (n : Node G) : {set Node G} :=
    [set m : Node G | ssval m \in find_ancestors (ssval n) G].
  apply: (Wf_nat.well_founded_lt_compat _ (fun n : Node G => #|anc n|)).
  move=> p n Hp'.
  have Hp : is_parent n p := Hp'.
  apply/ssrnat.ltP; apply: proper_card.
  rewrite properE; apply/andP; split.
  - apply/subsetP => m; rewrite !inE => Hm.
    apply: In_mem.
    exact: (ancestors_mono n p m Hwf Hcyc Hp (mem_In Hm)).
  - apply/negP => /subsetP Hsub.
    have Hself : ssval n \in find_ancestors (ssval n) G.
      apply: In_mem.
      exact: (proj1 (descendants_ancestors_correct G (ssval n) (ssval n)
                (conj (node_in_graph_ssval n) (node_in_graph_ssval n)))
                (node_is_descendant_of_itself (ssval n) G)).
    have H1 := Hsub n.
    rewrite !inE in H1.
    have H2 := H1 Hself.
    by rewrite (negbTE (child_not_ancestor_of_parent n p (conj Hwf Hcyc) Hp)) in H2.
Qed.

(* ------------------------------------------------------------------ *)
(* L4: a context solves to v iff every node's own equation holds at v  *)
(* ------------------------------------------------------------------ *)
Lemma world_of_char (w : context dom) (v : world dom) :
  G_well_formed G = true /\ contains_cycle G = false ->
  world_of enc dec tF w = v <->
  forall n : Node G, tF n (w n) (pa_view v n) = v n.
Proof.
  move=> Hdag; split.
  - (* (=>) every node's solved value is v's value, so n's equation holds *)
    move=> Hw n.
    have Hsol : forall m : Node G, solve enc dec tF w m = v m.
      move=> m; have H := congr1 (fun f : world dom => f m) Hw.
      by rewrite /= /world_of ffunE in H; exact: H.
    have Hpv : (fun p (_ : is_parent n p) => solve enc dec tF w p) = pa_view v n.
      apply: boolp.functional_extensionality_dep => p.
      by apply: boolp.funext => hp; rewrite /pa_view; exact: Hsol.
    rewrite -Hpv -(solve_eq w n Hdag).
    exact: Hsol.
  - (* (<=) induction along the parent relation *)
    move=> H; apply/ffunP => n; rewrite /world_of ffunE.
    elim/(well_founded_ind (parent_wf Hdag)): n => n IH.
    have Hpv : (fun p (_ : is_parent n p) => solve enc dec tF w p) = pa_view v n.
      apply: boolp.functional_extensionality_dep => p.
      by apply: boolp.funext => hp; rewrite /pa_view; exact: IH p hp.
    by rewrite (solve_eq w n Hdag) Hpv; exact: H n.
Qed.

(* ------------------------------------------------------------------ *)
(* L5: locality                                                        *)
(* n's solved value depends only on the noise of n and its ancestors   *)
(* ------------------------------------------------------------------ *)
(* every node is among its own ancestors *)
Lemma self_in_ancestors (n : Node G) :
  ssval n \in find_ancestors (ssval n) G.
Proof.
  apply: In_mem.
  exact: (proj1 (descendants_ancestors_correct G (ssval n) (ssval n)
            (conj (node_in_graph_ssval n) (node_in_graph_ssval n)))
            (node_is_descendant_of_itself (ssval n) G)).
Qed.

Lemma solve_local (w w' : context dom) (n : Node G) :
  G_well_formed G = true /\ contains_cycle G = false ->
  (forall m : Node G, ssval m \in find_ancestors (ssval n) G -> w m = w' m) ->
  solve enc dec tF w n = solve enc dec tF w' n.
Proof.
  move=> Hdag; have [Hwf Hcyc] := Hdag.
  move: n; elim/(well_founded_ind (parent_wf Hdag)) => n IH Hag.
  rewrite (solve_eq w n Hdag) (solve_eq w' n Hdag).
  have Hn : w n = w' n by apply: Hag; exact: self_in_ancestors.
  rewrite Hn.
  congr (tF n (w' n) _).
  apply: boolp.functional_extensionality_dep => p; apply: boolp.funext => hp.
  apply: IH; first exact: hp.
  move=> m Hm; apply: Hag; apply: In_mem.
  exact: (ancestors_mono n p m Hwf Hcyc hp (mem_In Hm)).
Qed.

(* ------------------------------------------------------------------ *)
(* L6: a node's noise is independent of all the other noises           *)
(* ------------------------------------------------------------------ *)
Lemma inde_unobs_rest (n : Node G) :
  Pc |= unobsRV n _|_ unobs_rest n.
Proof.
  move=> x y.
  (* S1: the event {unobs_rest n = y};  S2: additionally {w n = x} *)
  pose S1 (m : Node G) : {set dom m} :=
    if m == n then (if y n == j0 n then setT else set0) else [set y m].
  pose S2 (m : Node G) : {set dom m} :=
    if m == n
    then (if y n == j0 n then [set j | Tagged dom j == Tagged dom x] else set0)
    else [set y m].

  have memS1 (w : context dom) :
      (unobs_rest n w == y) = [forall m, w m \in S1 m].
    apply/eqP/forallP => [Hw m | H].
    - have Hm := congr1 (fun f : context dom => f m) Hw.
      rewrite /= /unobs_rest ffunE in Hm.
      move: Hm; case Hmn: (m == n).
      + move/eqP: Hmn => -> /= Hm.
        by rewrite /S1 eqxx -Hm eqxx /= inE.
      + move=> /= Hm; rewrite /S1 Hmn inE.
        by apply/eqP.
    - apply/ffunP => m; rewrite ffunE.
      case Hmn: (m == n).
      + move/eqP: Hmn => ->; rewrite /=.
        move: (H n); rewrite /S1 eqxx.
        case Hc: (y n == j0 n) => /=; last by rewrite in_set0.
        by move=> _; move/eqP: Hc => ->.
      + rewrite /=; move: (H m); rewrite /S1 Hmn inE.
        by move/eqP.

  have memS2 (w : context dom) :
      ((unobsRV n w == x) && (unobs_rest n w == y)) = [forall m, w m \in S2 m].
    rewrite memS1; apply/andP/forallP => [[/eqP Hx /forallP H1] m | H].
    - case Hmn: (m == n).
      + move/eqP: Hmn => ->.
        move: (H1 n); rewrite /S1 /S2 !eqxx.
        case Hc: (y n == j0 n) => /=; last by rewrite in_set0.
        by move=> _; rewrite inE eq_Tagged; apply/eqP.
      + by move: (H1 m); rewrite /S1 /S2 Hmn.
    - split.
      + move: (H n); rewrite /S2 eqxx.
        case Hc: (y n == j0 n) => /=; last by rewrite in_set0.
        by move=> Hn; rewrite inE eq_Tagged in Hn.
      + apply/forallP => m; case Hmn: (m == n).
        * move/eqP: Hmn => ->.
          move: (H n); rewrite /S1 /S2 !eqxx.
          case Hc: (y n == j0 n) => /=; last by rewrite in_set0.
          by move=> _; rewrite inE.
        * by move: (H m); rewrite /S1 /S2 Hmn.

  (* rewrite both sides as probabilities of product sets *)
  rewrite pfwd1E (_ : finset _ = [set w : context dom | [forall m, w m \in S2 m]]);
    last by apply/setP => w; rewrite !inE /= xpair_eqE; exact: memS2.
  have E2 : finset ([% unobsRV n, unobs_rest n] @^-1 (x, y))
          = [set w : context dom | [forall m, w m \in S2 m]].
    by apply/setP => w; rewrite !inE /= xpair_eqE; exact: memS2.
  have E1 : finset (unobs_rest n @^-1 y)
          = [set w : context dom | [forall m, w m \in S1 m]].
    by apply/setP => w; rewrite !inE /=; exact: memS1.
  have P2 : `Pr[ [% unobsRV n, unobs_rest n] = (x, y) ]
          = Pr Pc [set w : context dom | [forall m, w m \in S2 m]].
    by rewrite pfwd1E /Pr; apply: eq_bigl => w;
      rewrite !inE /= xpair_eqE; exact: memS2.
  have P1 : `Pr[ (unobs_rest n) = y ]
          = Pr Pc [set w : context dom | [forall m, w m \in S1 m]].
    by rewrite pfwd1E /Pr; apply: eq_bigl => w;
      rewrite !inE /=; exact: memS1.
  transitivity (Pr Pc [set w : context dom | [forall m, w m \in S2 m]]).
    reflexivity.
    (* first by rewrite pfwd1E /Pr; apply: eq_bigl => w;
            rewrite !inE /= xpair_eqE; exact: memS2. *)

  (* rest event: Pr[U_rest = y] = Pr of the S1 product set *)
  have -> : `Pr[ (unobs_rest n) = y ]
          = Pr Pc [set w : context dom | [forall m, w m \in S1 m]].
    by rewrite pfwd1E /Pr; apply: eq_bigl => w; rewrite !inE /=; exact: memS1.

  rewrite (pfwd1_unobs n x) (Pr_prod_set S2) (Pr_prod_set S1).
  rewrite [X in X = _](bigD1 n) //= [X in _ = _ * X](bigD1 n) //=.
  have -> : (\prod_(i | i != n) Pr (Pn i) (S2 i))%R
          = (\prod_(i | i != n) Pr (Pn i) (S1 i))%R.
    by apply: eq_bigr => i Hi; rewrite /S1 /S2 (negbTE Hi).
  have S1n : S1 n = if y n == j0 n then setT else set0 by rewrite /S1 eqxx.
  have S2n : S2 n = if y n == j0 n then [set j | Tagged dom j == Tagged dom x]
                    else set0 by rewrite /S2 eqxx.
  have Tx : [set j : dom n | Tagged dom j == Tagged dom x] = [set x].
    by apply/setP => j; rewrite !inE eq_Tagged.
  rewrite S1n S2n Tx.
  case: (y n == j0 n) => /=; rewrite ?Pr_set1 ?Pr_setT ?Pr_set0.
  - by rewrite mul1r.
  - by rewrite mul0r mulr0.
Qed.

(* ------------------------------------------------------------------ *)
(* helper for L7 (from L5 + L6 + inde_RV_comp):                        *)
(* a node's noise is independent of the values of its parents          *)
(* ------------------------------------------------------------------ *)
(* Lemma inde_unobs_paRV (n : Node G) :
  G_well_formed G = true /\ contains_cycle G = false ->
  Pc |= unobsRV n _|_ paRV n. *)
  (* helper graph fact: a parent's ancestors never include its child *)
(* Lemma child_not_ancestor_of_parent (n p : Node G) :
  G_well_formed G = true /\ contains_cycle G = false ->
  is_parent n p -> ssval n \notin find_ancestors (ssval p) G.
Proof. Admitted. *)

(* paRV n ignores node n's own noise *)
Lemma paRV_unobs_rest (n : Node G) :
  G_well_formed G = true /\ contains_cycle G = false ->
  forall w : context dom, paRV n w = paRV n (unobs_rest n w).
Proof.
  move=> Hdag w; apply/ffunP => p; rewrite /paRV !ffunE /nodeRV.
  apply: (solve_local w (unobs_rest n w) (sval p) Hdag) => m Hm.
  rewrite /unobs_rest ffunE.
  case Hmn: (m == n); last by [].
  move/eqP: Hmn => mn; rewrite mn in Hm.
  by case/negP: (child_not_ancestor_of_parent n (sval p) Hdag (valP p)).
Qed.

Lemma inde_unobs_paRV (n : Node G) :
  G_well_formed G = true /\ contains_cycle G = false ->
  Pc |= unobsRV n _|_ paRV n.
Proof.
  move=> Hdag.
  have Hc : Pc |= (id `o unobsRV n)
                _|_ ((fun w : context dom => paRV n w) `o unobs_rest n).
    by apply: inde_RV_comp; exact: inde_unobs_rest.
  have Hpa : paRV n = (fun w : context dom => paRV n w) `o unobs_rest n.
    by rewrite boolp.funeqE => w; exact: paRV_unobs_rest.
  by rewrite Hpa; exact: Hc.
Qed.

(* ------------------------------------------------------------------ *)
(* helper for L8 (from L4 + L1):                                       *)
(* the probability of a full world is the product of the noise masses  *)
(* ------------------------------------------------------------------ *)
Lemma pfwd1_worldRV (v : world dom) :
  G_well_formed G = true /\ contains_cycle G = false ->
  `Pr[ worldRV = v ] = (\prod_(n : Node G) Pr (Pn n) (A_set v n))%R.
Proof.
  move=> Hdag.
  rewrite -(Pr_prod_set (A_set v)) pfwd1E.
  congr (Pr Pc _); apply/setP => w; rewrite !inE /=.
  apply/eqP/forallP => [Hw n | H].
  - rewrite /A_set inE; apply/eqP.
    exact: ((world_of_char w v Hdag).1 Hw n).
  - apply/((world_of_char w v Hdag).2) => n.
    by move: (H n); rewrite /A_set inE => /eqP.
Qed.

(* ------------------------------------------------------------------ *)
(* helper for L8: a full world forces each parent tuple                *)
(* (no graph hypothesis needed: it is just set inclusion)              *)
(* ------------------------------------------------------------------ *)
Lemma pfwd1_worldRV_le_pa (v : world dom) (n : Node G) :
  (`Pr[ worldRV = v ] <= `Pr[ (paRV n) = (pa_of v n) ])%R.
Proof.
  rewrite !pfwd1E; apply: subset_Pr; apply/subsetP => w.
  rewrite !inE /= => /eqP Hw; apply/eqP.
  apply/ffunP => p.
  rewrite /paRV /pa_of /nodeRV !ffunE.
  have Hp := congr1 (fun f : world dom => f (sval p)) Hw.
  by rewrite /= /worldRV /world_of ffunE in Hp.
Qed.

(* ------------------------------------------------------------------ *)
(* L7: one conditional factor equals the noise mass of A_set           *)
(* ------------------------------------------------------------------ *)
(* the distribution of one noise coordinate, in event form *)
Lemma pr_in_unobs (n : Node G) (E : {set dom n}) :
  `Pr[ (unobsRV n) \in E ] = Pr (Pn n) E.
Proof.
  rewrite pr_inE'.
  have -> : `p_(unobsRV n) = Pn n := fdist_context_marginal Pn n.
  by [].
Qed.

(* on the event {parents read pa_of v}, node n obeys its own equation at v *)
Lemma nodeRV_given_pa (v : world dom) (n : Node G) (w : context dom) :
  G_well_formed G = true /\ contains_cycle G = false ->
  paRV n w = pa_of v n ->
  nodeRV n w = tF n (w n) (pa_view v n).
Proof.
  move=> Hdag Hpa.
  rewrite /nodeRV (solve_eq w n Hdag).
  congr (tF n (w n) _).
  apply: boolp.functional_extensionality_dep => p.
  apply: boolp.functional_extensionality_dep => hp.
  have H := congr1 (fun f : {dffun forall q : {q : Node G | is_parent n q},
                                    dom (sval q)} => f (exist _ p hp)) Hpa.
  rewrite /paRV /pa_of !ffunE in H.
  by rewrite /pa_view; exact: H.
Qed.

Lemma cpr_node_given_parents (v : world dom) (n : Node G) :
  G_well_formed G = true /\ contains_cycle G = false ->
  (`Pr[ (paRV n) = (pa_of v n) ] != 0)%R ->
  `Pr[ (nodeRV n) = v n | (paRV n) = (pa_of v n) ] = Pr (Pn n) (A_set v n).
Proof.
  move=> Hdag Hne.
  (* independence of the noise and the parent values, in event form *)
  move: (inde_unobs_paRV n Hdag) => /inde_RVP Hind.
  have H := Hind (A_set v n) [set pa_of v n].
  rewrite pr_in_unobs pr_in1 in H.
  rewrite cpr_eqE.
  transitivity
    ((Pr (Pn n) (A_set v n) * `Pr[ (paRV n) = (pa_of v n) ])
    / `Pr[ (paRV n) = (pa_of v n) ])%R.
  - congr (_ / _).
    apply: (etrans _ H).
    rewrite pfwd1E pr_inE; congr (Pr Pc _); apply/setP => w.
    rewrite /A_set !inE /= xpair_eqE.
    case Hp: (paRV n w == pa_of v n); last by rewrite !andbF.
    rewrite !andbT.
    by congr (_ == _); exact: nodeRV_given_pa v n w Hdag (eqP Hp).
  - by rewrite -mulrA mulfV ?mulr1.
Qed.

(* ------------------------------------------------------------------ *)
(* L8: Markov factorization                                            *)
(* ------------------------------------------------------------------ *)
Lemma markov_factorization (v : world dom) :
  G_well_formed G = true /\ contains_cycle G = false ->
  `Pr[ worldRV = v ] =
  (\prod_(n : Node G) `Pr[ (nodeRV n) = v n | (paRV n) = (pa_of v n) ])%R.
Proof.
  (* Outline, using only the lemmas above: *)
   move=> Hdag.
   case: (boolP [forall n, `Pr[ (paRV n) = (pa_of v n) ] != 0]).

   (* case 1: every conditioning event has positive probability *)
   - move=> /forallP Hpos.
     rewrite (pfwd1_worldRV v Hdag).
     apply: eq_bigr => n _.
     (* Check cpr_node_given_parents. *)
     by rewrite (cpr_node_given_parents v _ Hdag (Hpos n)).

   (* case 2: some n0 has Pr[ paRV n0 = pa_of v n0 ] = 0 *)
   - rewrite negb_forall => /existsP [n0 /negPn /eqP H0].
     (* LHS = 0: Pr[worldRV = v] <= Pr[paRV n0 = ...] = 0, and Pr >= 0 *)
     have H : `Pr[ worldRV = v ] = 0.
      apply/eqP; rewrite eq_le (pfwd1_ge0 _ _) andbT.
      by rewrite -H0 (pfwd1_worldRV_le_pa v n0).
     (* RHS = 0: the n0 factor is a quotient by 0 (cpr_eqE, invr0, mulr0) *)
     rewrite (bigD1 n0) //=.
     by rewrite cpr_eqE H0 invr0 mulr0 mul0r.
Qed.

End MarkovFactorization.
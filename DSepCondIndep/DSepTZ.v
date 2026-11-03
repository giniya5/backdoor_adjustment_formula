From CausalDiagrams Require Import IntermediateNodes.
From CausalDiagrams Require Import DSeparation.
From DAGs Require Import Basics.
From DAGs Require Import CycleDetection.
From DAGs Require Import Descendants.
From DAGs Require Import PathFinding.
From Utils Require Import Lists.
From Utils Require Import Logic.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Arith.EqNat. Import Nat.
From Stdlib Require Import Lia.

Import ListNotations.

(* ------------------------------------------------------------------ *)
(* Set versions (drop these if already defined elsewhere)              *)
(* ------------------------------------------------------------------ *)

Definition find_descendants_set (N: nodes) (G: graph) : nodes :=
  flat_map (fun x => find_descendants x G) N.

Definition find_parents_set (N: nodes) (G: graph) : nodes :=
  flat_map (fun x => find_parents x G) N.

Lemma parents_set_intro : forall G T t p,
  In t T -> In p (find_parents t G) -> In p (find_parents_set T G).
Proof.
  intros G T t p Ht Hp. unfold find_parents_set. apply in_flat_map.
  exists t. split; assumption.
Qed.

Lemma parents_set_elim : forall G T p,
  In p (find_parents_set T G) -> exists t, In t T /\ In p (find_parents t G).
Proof.
  intros G T p H. unfold find_parents_set in H. apply in_flat_map in H. exact H.
Qed.

Lemma desc_set_intro : forall G T t v,
  In t T -> In v (find_descendants t G) -> In v (find_descendants_set T G).
Proof.
  intros G T t v Ht Hv. unfold find_descendants_set. apply in_flat_map.
  exists t. split; assumption.
Qed.

(* ------------------------------------------------------------------ *)
(* Adjacency along a node list (consecutive nodes joined by an edge)   *)
(* ------------------------------------------------------------------ *)

Fixpoint adj (L: nodes) (G: graph) : Prop :=
  match L with
  | a :: ((b :: _) as t) => (is_edge (a, b) G = true \/ is_edge (b, a) G = true) /\ adj t G
  | _ => True
  end.

Lemma adj_cons : forall a b r G,
  adj (a :: b :: r) G = ((is_edge (a, b) G = true \/ is_edge (b, a) G = true) /\ adj (b :: r) G).
Proof. reflexivity. Qed.

Lemma mediators_path : forall u v l G,
  find_mediators_in_path (u, v, l) G = find_mediators_in_nodes (u :: (l ++ [v])) G.
Proof. reflexivity. Qed.

Lemma confounders_path : forall u v l G,
  find_confounders_in_path (u, v, l) G = find_confounders_in_nodes (u :: (l ++ [v])) G.
Proof. reflexivity. Qed.

Lemma snoc_nonempty : forall (l: nodes) (z: node), exists h2 r, l ++ [z] = h2 :: r.
Proof.
  intros l z. destruct l as [|a l'].
  - exists z, []. reflexivity.
  - exists a, (l' ++ [z]). reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Bridge lemmas: facts about Basics.v definitions (is_edge, paths).   *)
(* ------------------------------------------------------------------ *)
 
(* is_edge (a,b) holds iff a is a parent of b (in well-formed graphs) *)
Lemma is_edge_parent : forall G a b,
  G_well_formed G = true ->
  (is_edge (a, b) G = true <-> In a (find_parents b G)).
Proof.
  intros G a b Hwf. split; intro H.
  - apply (proj2 (edge_from_parent_to_child b a G)).
    rewrite (edge_in_graph_equiv G a b Hwf) in H. exact H.
  - apply (proj1 (edge_from_parent_to_child b a G)) in H.
    apply edge_in_graph_then_is_edge; assumption.
Qed.
 
(* an edge gives a descendant: one-step directed path + find_descendants_correct *)
Lemma desc_edge : forall G a b,
  G_well_formed G = true -> contains_cycle G = false ->
  is_edge (a, b) G = true -> In b (find_descendants a G).
Proof.
  intros G a b Hwf Hcyc Hedge.
  apply (proj2 (find_descendants_correct G a b Hwf Hcyc)).
  right. exists (a, b, []). split.
  - unfold is_directed_path_in_graph. cbn [app is_dir_path_in_graph_helper].
    rewrite Hedge; reflexivity.
  - unfold path_start_and_end. simpl. rewrite Nat.eqb_refl. simpl. apply Nat.eqb_refl.
Qed.
 
(* a path in the graph is adjacent node-to-node along u :: l ++ [v] *)
Lemma path_adj_helper : forall L G,
  is_path_in_graph_helper L G = true -> adj L G.
Proof.
  intros L [V E]. induction L as [|a L IH]; intro H.
  - exact I.
  - destruct L as [|b L'].
    + exact I.
    + cbn [is_path_in_graph_helper] in H.
      apply andb_true_iff in H. destruct H as [Hab Hrest].
      rewrite adj_cons. split.
      * apply orb_true_iff in Hab. exact Hab.
      * apply IH. exact Hrest.
Qed.
 
Lemma path_adj : forall u v l G,
  is_path_in_graph (u, v, l) G = true -> adj (u :: l ++ [v]) G.
Proof.
  intros u v l G H. apply path_adj_helper. exact H.
Qed.
 
(* in an acyclic graph, a parent of t is not a descendant of t *)
Lemma parent_not_descendant : forall G t p,
  G_well_formed G = true -> contains_cycle G = false ->
  In p (find_parents t G) -> ~ In p (find_descendants t G).
Proof.
  intros G t p Hwf Hcyc Hpar Hdesc.
  assert (Hedge : is_edge (p, t) G = true)
    by (apply (proj2 (is_edge_parent G p t Hwf)); exact Hpar).
  assert (Hdir2 : is_directed_path_in_graph (p, t, []) G = true).
  { unfold is_directed_path_in_graph. cbn [app is_dir_path_in_graph_helper].
    rewrite Hedge; reflexivity. }
  apply (proj1 (find_descendants_correct G t p Hwf Hcyc)) in Hdesc.
  destruct Hdesc as [Heq | [U [Hdir Hse]]].
  - (* p = t: a self loop *)
    subst p.
    assert (Hac : acyclic_path_2 (t, t, []))
      by (eapply contains_cycle_false_correct; eauto).
    destruct Hac as [Hne _]. apply Hne. reflexivity.
  - (* directed path t ~> p followed by the edge p -> t is a cycle *)
    destruct U as [[u v] l].
    apply path_start_end_equal in Hse. destruct Hse as [Hu Hv].
    rewrite Hu in Hdir. rewrite Hv in Hdir.
    assert (Hcat : is_directed_path_in_graph (t, t, l ++ p :: []) G = true)
      by (apply (concat_directed_paths t p t l [] G); split; assumption).
    assert (Hac : acyclic_path_2 (t, t, l ++ p :: []))
      by (eapply contains_cycle_false_correct; eauto).
    simpl in Hac. destruct Hac as [Hne _]. apply Hne. reflexivity.
Qed.
 
(* membership in both lists implies overlap *)
Lemma overlap_intro : forall (A B: nodes) x,
  In x A -> In x B -> overlap A B = true.
Proof.
  intros A B x HA HB.
  apply (proj2 (overlap_has_member_in_common A B)).
  exists x. split; assumption.
Qed.
(* 

(* ------------------------------------------------------------------ *)
(* BRIDGE lemmas: facts about Basics.v definitions (is_edge, paths).   *)
(* Statements are what the proof needs; proofs are to be filled in.    *)
(* ------------------------------------------------------------------ *)

(* is_edge (a,b) holds iff a is a parent of b (in well-formed graphs) *)
Lemma is_edge_parent : forall G a b,
  G_well_formed G = true ->
  (is_edge (a, b) G = true <-> In a (find_parents b G)).
Proof.
  (* use edge_from_parent_to_child, edge_corresponds_to_nodes_in_well_formed,
     is_edge_true_implies_In_edge *)
Admitted.

(* an edge gives a descendant: one-step directed path + find_descendants_correct *)
Lemma desc_edge : forall G a b,
  G_well_formed G = true -> contains_cycle G = false ->
  is_edge (a, b) G = true -> In b (find_descendants a G).
Proof.
  (* apply find_descendants_correct; right; exists (a, b, []);
     is_directed_path_in_graph (a,b,[]) G unfolds to is_edge (a,b) G && true *)
Admitted.

(* a path in the graph is adjacent node-to-node along u :: l ++ [v] *)
Lemma path_adj : forall u v l G,
  is_path_in_graph (u, v, l) G = true -> adj (u :: l ++ [v]) G.
Proof.
  (* induction on is_path_in_graph_helper; each step is (is_edge || is_edge) && rest *)
Admitted.

(* in an acyclic graph, a parent of t is not a descendant of t *)
Lemma parent_not_descendant : forall G t p,
  G_well_formed G = true -> contains_cycle G = false ->
  In p (find_parents t G) -> ~ In p (find_descendants t G).
Proof.
  (* a directed path t ~> p plus edge p -> t is a cycle; see contains_cycle_false_correct *)
Admitted.

(* membership in both lists implies overlap *)
Lemma overlap_intro : forall (A B: nodes) x,
  In x A -> In x B -> overlap A B = true.
Proof.
  (* converse of overlap_has_member_in_common; see Utils/Lists.v *)
Admitted. *)

(* ------------------------------------------------------------------ *)
(* Descendant helpers                                                   *)
(* ------------------------------------------------------------------ *)

Lemma desc_trans : forall G x y z,
  G_well_formed G = true -> contains_cycle G = false ->
  In y (find_descendants z G) -> In x (find_descendants y G) ->
  In x (find_descendants z G).
Proof.
  intros G x y z Hwf Hcyc Hy Hx.
  eapply descendants_transitive; eauto.
Qed.

Lemma desc_step : forall G t p a,
  G_well_formed G = true -> contains_cycle G = false ->
  In p (find_descendants t G) -> is_edge (p, a) G = true ->
  In a (find_descendants t G).
Proof.
  intros G t p a Hwf Hcyc Hp Hpa.
  eapply desc_trans; eauto. apply desc_edge; assumption.
Qed.

(* ------------------------------------------------------------------ *)
(* Collider / mediator / confounder bookkeeping on node lists          *)
(* ------------------------------------------------------------------ *)

Lemma collider_here : forall G p a c r,
  is_edge (p, a) G = true -> is_edge (c, a) G = true ->
  In a (find_colliders_in_nodes (p :: a :: c :: r) G).
Proof.
  intros G p a c r H1 H2.
  change (find_colliders_in_nodes (p :: a :: c :: r) G) with
    (if is_collider_bool p c a G
     then a :: find_colliders_in_nodes (a :: c :: r) G
     else find_colliders_in_nodes (a :: c :: r) G).
  unfold is_collider_bool. rewrite H1, H2. simpl. left. reflexivity.
Qed.

Lemma colliders_cons : forall G p a b r x,
  In x (find_colliders_in_nodes (a :: b :: r) G) ->
  In x (find_colliders_in_nodes (p :: a :: b :: r) G).
Proof.
  intros G p a b r x H.
  change (find_colliders_in_nodes (p :: a :: b :: r) G) with
    (if is_collider_bool p b a G
     then a :: find_colliders_in_nodes (a :: b :: r) G
     else find_colliders_in_nodes (a :: b :: r) G).
  destruct (is_collider_bool p b a G); [right|]; exact H.
Qed.

(* if the path leaves t through a parent h, then h is a mediator or confounder *)
Lemma parent_start_blocked : forall G t h h2 r,
  is_edge (h, t) G = true ->
  (is_edge (h, h2) G = true \/ is_edge (h2, h) G = true) ->
  In h (find_mediators_in_nodes (t :: h :: h2 :: r) G) \/
  In h (find_confounders_in_nodes (t :: h :: h2 :: r) G).
Proof.
  intros G t h h2 r Hht [Hhh2 | Hh2h].
  - right.
    change (find_confounders_in_nodes (t :: h :: h2 :: r) G) with
      (if is_confounder_bool t h2 h G
       then h :: find_confounders_in_nodes (h :: h2 :: r) G
       else find_confounders_in_nodes (h :: h2 :: r) G).
    unfold is_confounder_bool. rewrite Hht, Hhh2. simpl. left. reflexivity.
  - left.
    change (find_mediators_in_nodes (t :: h :: h2 :: r) G) with
      (if (is_mediator_bool t h2 h G || is_mediator_bool h2 t h G)
       then h :: find_mediators_in_nodes (h :: h2 :: r) G
       else find_mediators_in_nodes (h :: h2 :: r) G).
    unfold is_mediator_bool. rewrite Hh2h, Hht.
    destruct (is_edge (t, h) G && is_edge (h, h2) G); simpl; left; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Going down from t: either we reach z along a directed path, or we    *)
(* hit a collider that is a descendant of t                             *)
(* ------------------------------------------------------------------ *)

Lemma down_chain : forall G t z,
  G_well_formed G = true -> contains_cycle G = false ->
  forall M0 p a,
    adj (p :: a :: M0 ++ [z]) G ->
    is_edge (p, a) G = true ->
    In p (find_descendants t G) ->
    In z (find_descendants t G) \/
    exists x, In x (find_colliders_in_nodes (p :: a :: M0 ++ [z]) G)
              /\ In x (find_descendants t G).
Proof.
  intros G t z Hwf Hcyc M0. induction M0 as [|b M0' IH]; intros p a Hadj Hpa Hp.
  - cbn [adj app] in Hadj. destruct Hadj as [_ [Haz_or _]].
    assert (Ha : In a (find_descendants t G)) by (eapply desc_step; eauto).
    destruct (is_edge (a, z) G) eqn:Haz.
    + left. eapply desc_step; eauto.
    + right.
      assert (Hza : is_edge (z, a) G = true).
      { destruct Haz_or as [H | H]. inversion H. exact H. }
      exists a. split.
      * exact (collider_here G p a z [] Hpa Hza).
      * exact Ha.
  - cbn [adj app] in Hadj. destruct Hadj as [_ [Hab_adj Hrest]].
    assert (Ha : In a (find_descendants t G)) by (eapply desc_step; eauto).
    assert (Hrest' : adj (a :: b :: M0' ++ [z]) G)
      by (cbn [adj app]; split; assumption).
    destruct (is_edge (a, b) G) eqn:Hab.
    + destruct (IH a b Hrest' Hab Ha) as [Hz | [x [Hx Hxd]]].
      * left. exact Hz.
      * right. exists x. split.
        { apply colliders_cons. exact Hx. }
        { exact Hxd. }
    + assert (Hba : is_edge (b, a) G = true).
      { destruct Hab_adj as [H | H]. inversion H. exact H. }
      right. exists a. split.
      * exact (collider_here G p a b (M0' ++ [z]) Hpa Hba).
      * exact Ha.
Qed.

(* ------------------------------------------------------------------ *)
(* A descendant of T never has a conditioned descendant                 *)
(* ------------------------------------------------------------------ *)

Lemma conditioned_desc_impossible : forall G T t x d,
  G_well_formed G = true -> contains_cycle G = false ->
  (forall t t', In t T -> In t' T -> t <> t' ->
     ~ In t (find_descendants t' G) /\ ~ In t' (find_descendants t G)) ->
  In t T ->
  In x (find_descendants t G) ->
  In d (find_descendants x G) ->
  In d (find_parents_set T G) -> False.
Proof.
  intros G T t x d Hwf Hcyc Hanti Ht Hx Hd Hdp.
  destruct (parents_set_elim G T d Hdp) as [t' [Ht' Hdt']].
  assert (Hedge : is_edge (d, t') G = true)
    by (apply (proj2 (is_edge_parent G d t' Hwf)); exact Hdt').
  assert (Ht'd : In t' (find_descendants d G)) by (apply desc_edge; assumption).
  assert (Hdt : In d (find_descendants t G)) by (eapply desc_trans; eauto).
  assert (Ht't : In t' (find_descendants t G)) by (eapply desc_trans; eauto).
  destruct (Nat.eq_dec t' t) as [Heq | Hne].
  - rewrite Heq in Hdt'.
    exact (parent_not_descendant G t d Hwf Hcyc Hdt' Hdt).
  - destruct (Hanti t t' Ht Ht' (fun e => Hne (eq_sym e))) as [_ H2].
    exact (H2 Ht't).
Qed.

(* ------------------------------------------------------------------ *)
(* Main lemma                                                           *)
(* ------------------------------------------------------------------ *)

Lemma DSep_T_Z_given_paT :
  forall (G: graph) (T Z: nodes),
    G_well_formed G = true /\ contains_cycle G = false ->
    (* T is an antichain: no directed path between distinct members *)
    (forall t t', In t T -> In t' T -> t <> t' ->
       ~ In t (find_descendants t' G) /\ ~ In t' (find_descendants t G)) ->
    (* Z avoids T, parents(T), and all descendants of T *)
    (forall z, In z Z ->
       ~ In z T /\
       ~ In z (find_descendants_set T G) /\
       ~ In z (find_parents_set T G)) ->
    forall t z, In t T -> In z Z ->
      d_separated_bool t z G (find_parents_set T G) = true.
Proof.
  intros G T Z Hgood Hanti HZ t z Ht Hz.
  assert (Hg := Hgood). destruct Hg as [Hwf Hcyc].
  destruct (HZ z Hz) as [_ [HzD HzP]].
  destruct (d_separated_bool t z G (find_parents_set T G)) eqn:Hd; [reflexivity|].
  exfalso.
  apply d_separated_vs_connected in Hd; [| exact Hgood].
  destruct Hd as [l [_ [Hpath Hconn]]].
  destruct Hconn as [Hmed [Hcon Hcol]].
  pose proof (path_adj t z l G Hpath) as Hadj.
  destruct l as [|h l'].
  - (* single edge between t and z *)
    cbn [app adj] in Hadj. destruct Hadj as [[Htz | Hzt] _].
    + apply HzD. eapply desc_set_intro; [exact Ht|].
      eapply desc_step; [exact Hwf | exact Hcyc | apply node_is_descendant_of_itself | exact Htz].
    + apply HzP. eapply parents_set_intro; [exact Ht|].
      exact (proj1 (is_edge_parent G z t Hwf) Hzt).
  - destruct (is_edge (t, h) G) eqn:Hth.
    + (* path leaves t downward *)
      destruct (down_chain G t z Hwf Hcyc l' t h Hadj Hth
                  (node_is_descendant_of_itself t G)) as [Hz' | [x [Hx Hxd]]].
      * apply HzD. eapply desc_set_intro; eauto.
      * unfold all_colliders_have_descendant_conditioned_on in Hcol.
        rewrite forallb_forall in Hcol.
        specialize (Hcol x Hx).
        assert (Hov : overlap (find_descendants x G) (find_parents_set T G) = true)
          by exact Hcol.
        destruct (proj1 (overlap_has_member_in_common _ _) Hov) as [d [Hdx Hdz]].
        (* destruct (overlap_has_member_in_common _ _ Hov) as [d [Hdx Hdz]]. *)
        exact (conditioned_desc_impossible G T t x d Hwf Hcyc Hanti Ht Hxd Hdx Hdz).
    + (* path leaves t through a parent h *)
      destruct (snoc_nonempty l' z) as [h2 [r Hr]].
      assert (Hlist : t :: (h :: l') ++ [z] = t :: h :: h2 :: r)
        by (cbn [app]; rewrite Hr; reflexivity).
      rewrite Hlist in Hadj.
      rewrite mediators_path in Hmed. rewrite Hlist in Hmed.
      rewrite confounders_path in Hcon. rewrite Hlist in Hcon.
      rewrite adj_cons in Hadj. destruct Hadj as [[Hth' | Hht] Hadj2].
      { rewrite Hth in Hth'. discriminate. }
      rewrite adj_cons in Hadj2. destruct Hadj2 as [Hhh2 _].
      assert (Hhz : In h (find_parents_set T G)).
      { eapply parents_set_intro; [exact Ht|].
        exact (proj1 (is_edge_parent G h t Hwf) Hht). }
      destruct (parent_start_blocked G t h h2 r Hht Hhh2) as [Hm | Hc].
      * pose proof (overlap_intro _ _ h Hhz Hm) as Hov.
        rewrite Hmed in Hov. discriminate.
      * pose proof (overlap_intro _ _ h Hhz Hc) as Hov.
        rewrite Hcon in Hov. discriminate.
Qed.

Print Assumptions DSep_T_Z_given_paT.
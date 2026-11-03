From CausalDiagrams Require Import IntermediateNodes.
From CausalDiagrams Require Import DSeparation.
From CondIndep Require Import DSepTZ.
From DAGs Require Import Basics.
From DAGs Require Import CycleDetection.
From DAGs Require Import Descendants.
From DAGs Require Import PathFinding.
From Utils Require Import Lists.
From Utils Require Import Logic.
From Stdlib Require Import Arith.EqNat. Import Nat.

Import ListNotations.

(* ------------------------------------------------------------------ *)
(* 1. The backdoor graph: remove every edge whose source is in T       *)
(* ------------------------------------------------------------------ *)

Definition remove_outgoing_edges (T: nodes) (G: graph) : graph :=
  match G with
  | (V, E) => (V, filter (fun e => negb (member (fst e) T)) E)
  end.

Lemma backdoor_is_edge : forall T G a b,
  is_edge (a, b) (remove_outgoing_edges T G) = true <->
  (is_edge (a, b) G = true /\ ~ In a T).
Proof.
  intros T [V E] a b. unfold remove_outgoing_edges, is_edge.
  split.
  - intros H. apply andb_true_iff in H. destruct H as [H Hme].
    apply andb_true_iff in H. destruct H as [Ha Hb].
    apply member_edge_In_equiv in Hme. apply filter_true in Hme.
    destruct Hme as [HmeE Hf]. simpl in Hf. apply negb_true_iff in Hf.
    split.
    + apply andb_true_iff. split.
      * apply andb_true_iff. split; assumption.
      * apply member_edge_In_equiv. exact HmeE.
    + intro HaT. apply member_In_equiv in HaT. rewrite HaT in Hf. discriminate.
  - intros [H HaT]. apply andb_true_iff in H. destruct H as [H Hme].
    apply andb_true_iff in H. destruct H as [Ha Hb].
    apply andb_true_iff. split.
    + apply andb_true_iff. split; assumption.
    + apply member_edge_In_equiv. apply filter_true. split.
      * apply member_edge_In_equiv. exact Hme.
      * simpl. apply negb_true_iff.
        destruct (member a T) eqn:HmT.
        { exfalso. apply HaT. apply member_In_equiv. exact HmT. }
        { reflexivity. }
Qed.

Lemma backdoor_well_formed : forall T G,
  G_well_formed G = true -> G_well_formed (remove_outgoing_edges T G) = true.
Proof.
  intros T [V E] H. unfold remove_outgoing_edges.
  unfold G_well_formed in H. unfold G_well_formed. simpl.
  apply split_and_true in H. destruct H as [He Hec].
  apply split_and_true in He. destruct He as [He Hv].
  apply split_and_true. split.
  - apply split_and_true. split.
    + apply forallb_true_iff_mem. intros [u v] Hmem.
      apply filter_true in Hmem. destruct Hmem as [Hmem _].
      assert (HVmem: forall x: nat * nat, In x E ->
                (let (u, v) := x in member u V && member v V) = true)
        by (apply forallb_true_iff_mem; exact He).
      exact (HVmem (u, v) Hmem).
    + exact Hv.
  - apply forallb_true_iff_mem. intros x Hmem.
    apply filter_true in Hmem. destruct Hmem as [HmemE Hf].
    assert (Hc : count_edge x E =
                 count_edge x (filter (fun e : nat * node => negb (member (fst e) T)) E))
      by (apply count_edge_filter; exact Hf).
    rewrite <- Hc.
    assert (HVc: forall x: edge, In x E -> (count_edge x E =? 1) = true)
      by (apply forallb_true_iff_mem; exact Hec).
    exact (HVc x HmemE).
Qed.

Lemma dir_helper_backdoor : forall T G L,
  is_dir_path_in_graph_helper L (remove_outgoing_edges T G) = true ->
  is_dir_path_in_graph_helper L G = true.
Proof.
  intros T G. induction L as [|a L IH]; intro H.
  - reflexivity.
  - destruct L as [|b L'].
    + reflexivity.
    + cbn [is_dir_path_in_graph_helper] in H |- *.
      apply andb_true_iff in H. destruct H as [Hab Hr].
      apply andb_true_iff. split.
      * exact (proj1 (proj1 (backdoor_is_edge T G a b) Hab)).
      * apply IH. exact Hr.
Qed.

(* every directed path of the backdoor graph is a directed path of G, hence acyclic *)
Lemma backdoor_acyclic : forall T G,
  G_well_formed G = true -> contains_cycle G = false ->
  contains_cycle (remove_outgoing_edges T G) = false.
Proof.
  intros T G Hwf Hcyc.
  apply contains_cycle_false_complete.
  - apply backdoor_well_formed. exact Hwf.
  - intros p Hp.
    apply (contains_cycle_false_correct G p Hwf Hcyc).
    destruct p as [[u v] l]. unfold is_directed_path_in_graph in *.
    apply dir_helper_backdoor with (T := T). exact Hp.
Qed.

Lemma no_two_cycle : forall G a b,
  G_well_formed G = true -> contains_cycle G = false ->
  is_edge (a, b) G = true -> is_edge (b, a) G = true -> False.
Proof.
  intros G a b Hwf Hcyc H1 H2.
  assert (Hdir : is_directed_path_in_graph (a, a, [b]) G = true).
  { unfold is_directed_path_in_graph. cbn [app is_dir_path_in_graph_helper].
    rewrite H1, H2; reflexivity. }
  assert (Hac : acyclic_path_2 (a, a, [b]))
    by (eapply contains_cycle_false_correct; eauto).
  destruct Hac as [Hne _]. apply Hne. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* 2. open_path: a node-list version of d_connected_2                   *)
(*    each interior node b with neighbours a, c is either a collider    *)
(*    with a descendant in Z, or a non-collider outside Z               *)
(* ------------------------------------------------------------------ *)

Definition triple_ok (G: graph) (Z: nodes) (a b c: node) : Prop :=
  (is_edge (a, b) G = true /\ is_edge (c, b) G = true ->
     exists d, In d (find_descendants b G) /\ In d Z) /\
  (~ (is_edge (a, b) G = true /\ is_edge (c, b) G = true) -> ~ In b Z).

Fixpoint open_path (G: graph) (Z: nodes) (L: nodes) : Prop :=
  match L with
  | a :: ((b :: (c :: _)) as t) => triple_ok G Z a b c /\ open_path G Z t
  | _ => True
  end.

Lemma open_path_cons3 : forall G Z a b c r,
  open_path G Z (a :: b :: c :: r) = (triple_ok G Z a b c /\ open_path G Z (b :: c :: r)).
Proof. reflexivity. Qed.

Lemma mediators_unfold : forall G a b c r,
  find_mediators_in_nodes (a :: b :: c :: r) G =
  if (is_mediator_bool a c b G || is_mediator_bool c a b G)
  then b :: find_mediators_in_nodes (b :: c :: r) G
  else find_mediators_in_nodes (b :: c :: r) G.
Proof. reflexivity. Qed.

Lemma confounders_unfold : forall G a b c r,
  find_confounders_in_nodes (a :: b :: c :: r) G =
  if is_confounder_bool a c b G
  then b :: find_confounders_in_nodes (b :: c :: r) G
  else find_confounders_in_nodes (b :: c :: r) G.
Proof. reflexivity. Qed.

Lemma colliders_unfold : forall G a b c r,
  find_colliders_in_nodes (a :: b :: c :: r) G =
  if is_collider_bool a c b G
  then b :: find_colliders_in_nodes (b :: c :: r) G
  else find_colliders_in_nodes (b :: c :: r) G.
Proof. reflexivity. Qed.

Lemma colliders_path : forall u v l G,
  find_colliders_in_path (u, v, l) G = find_colliders_in_nodes (u :: (l ++ [v])) G.
Proof. reflexivity. Qed.

Lemma overlap_mem : forall (A B: nodes) x,
  In x A -> In x B -> overlap A B = true.
Proof.
  intros A B x HA HB.
  apply (proj2 (overlap_has_member_in_common A B)).
  exists x. split; assumption.
Qed.

Lemma overlap_nil : forall Z, overlap Z [] = false.
Proof.
  intros Z. destruct (overlap Z []) eqn:H; [|reflexivity].
  apply (proj1 (overlap_has_member_in_common Z [])) in H.
  destruct H as [m [_ Hm]]. contradiction.
Qed.

Lemma overlap_if : forall Z (cond: bool) x M,
  overlap Z (if cond then x :: M else M) = false ->
  overlap Z M = false /\ (cond = true -> ~ In x Z).
Proof.
  intros Z cond x M H. destruct cond; simpl in H.
  - split.
    + destruct (overlap Z M) eqn:HM; [|reflexivity].
      apply (proj1 (overlap_has_member_in_common Z M)) in HM.
      destruct HM as [m [HmZ HmM]].
      pose proof (overlap_mem Z (x :: M) m HmZ (or_intror HmM)) as H'.
      rewrite H in H'. discriminate.
    + intros _ HxZ.
      pose proof (overlap_mem Z (x :: M) x HxZ (in_eq _ _)) as H'.
      rewrite H in H'. discriminate.
  - split; [exact H | intros E; discriminate].
Qed.

Lemma overlap_if_rev : forall Z (cond: bool) x M,
  overlap Z M = false -> (cond = true -> ~ In x Z) ->
  overlap Z (if cond then x :: M else M) = false.
Proof.
  intros Z cond x M HM Hc. destruct cond; simpl.
  - destruct (overlap Z (x :: M)) eqn:H; [|reflexivity].
    apply (proj1 (overlap_has_member_in_common Z (x :: M))) in H.
    destruct H as [m [HmZ [Hm | Hm]]].
    + subst m. exfalso. assert (Htt : true = true) by reflexivity. exact (Hc Htt HmZ).
    + pose proof (overlap_mem Z M m HmZ Hm) as H'. rewrite HM in H'. discriminate.
  - exact HM.
Qed.

Lemma colliders_ok_if : forall G Z (cond: bool) x C,
  all_colliders_have_descendant_conditioned_on (if cond then x :: C else C) G Z = true ->
  all_colliders_have_descendant_conditioned_on C G Z = true /\
  (cond = true -> some_descendant_in_Z_bool (find_descendants x G) Z = true).
Proof.
  intros G Z cond x C H. unfold all_colliders_have_descendant_conditioned_on in *.
  destruct cond; simpl in H.
  - apply andb_true_iff in H. destruct H as [H1 H2]. split; [exact H2 | intros _; exact H1].
  - split; [exact H | intros E; discriminate].
Qed.

Lemma colliders_ok_if_rev : forall G Z (cond: bool) x C,
  all_colliders_have_descendant_conditioned_on C G Z = true ->
  (cond = true -> some_descendant_in_Z_bool (find_descendants x G) Z = true) ->
  all_colliders_have_descendant_conditioned_on (if cond then x :: C else C) G Z = true.
Proof.
  intros G Z cond x C H1 H2. unfold all_colliders_have_descendant_conditioned_on in *.
  destruct cond; simpl.
  - apply andb_true_iff. split; [apply H2; reflexivity | exact H1].
  - exact H1.
Qed.

Lemma is_collider_true : forall G a c b,
  is_collider_bool a c b G = true -> is_edge (a, b) G = true /\ is_edge (c, b) G = true.
Proof.
  intros G a c b H. unfold is_collider_bool in H. apply andb_true_iff in H. exact H.
Qed.

Lemma noncollider_mc : forall G a b c,
  (is_edge (a, b) G = true \/ is_edge (b, a) G = true) ->
  (is_edge (b, c) G = true \/ is_edge (c, b) G = true) ->
  ~ (is_edge (a, b) G = true /\ is_edge (c, b) G = true) ->
  (is_mediator_bool a c b G || is_mediator_bool c a b G) = true \/
  is_confounder_bool a c b G = true.
Proof.
  intros G a b c Hab Hbc Hnc.
  destruct (is_edge (a, b) G) eqn:E1.
  - destruct (is_edge (c, b) G) eqn:E2.
    + exfalso. apply Hnc. split; reflexivity.
    + assert (E3 : is_edge (b, c) G = true)
        by (destruct Hbc as [H|H]; [exact H | congruence]).
      left. unfold is_mediator_bool. rewrite E1, E3; reflexivity.
  - assert (E0 : is_edge (b, a) G = true)
      by (destruct Hab as [H|H]; [congruence | exact H]).
    destruct (is_edge (b, c) G) eqn:E3.
    + right. unfold is_confounder_bool. rewrite E0, E3; reflexivity.
    + assert (E4 : is_edge (c, b) G = true)
        by (destruct Hbc as [H|H]; [congruence | exact H]).
      left. unfold is_mediator_bool. rewrite E1, E3, E4, E0; reflexivity.
Qed.

Lemma mediator_noncollider : forall G a b c,
  G_well_formed G = true -> contains_cycle G = false ->
  (is_mediator_bool a c b G || is_mediator_bool c a b G) = true ->
  ~ (is_edge (a, b) G = true /\ is_edge (c, b) G = true).
Proof.
  intros G a b c Hwf Hcyc H [E1 E2].
  apply orb_true_iff in H. destruct H as [H | H];
  unfold is_mediator_bool in H; apply andb_true_iff in H; destruct H as [H1 H2].
  - exact (no_two_cycle G b c Hwf Hcyc H2 E2).
  - exact (no_two_cycle G a b Hwf Hcyc E1 H2).
Qed.

Lemma confounder_noncollider : forall G a b c,
  G_well_formed G = true -> contains_cycle G = false ->
  is_confounder_bool a c b G = true ->
  ~ (is_edge (a, b) G = true /\ is_edge (c, b) G = true).
Proof.
  intros G a b c Hwf Hcyc H [E1 E2].
  unfold is_confounder_bool in H. apply andb_true_iff in H. destruct H as [H1 H2].
  exact (no_two_cycle G a b Hwf Hcyc E1 H1).
Qed.

(* ---- bridge A: d_connected_2 (list form) gives open_path ---- *)
Lemma open_path_from_lists : forall G Z L,
  adj L G ->
  overlap Z (find_mediators_in_nodes L G) = false ->
  overlap Z (find_confounders_in_nodes L G) = false ->
  all_colliders_have_descendant_conditioned_on (find_colliders_in_nodes L G) G Z = true ->
  open_path G Z L.
Proof.
  intros G Z L. induction L as [|a L IH]; intros Hadj Hm Hc Hcol.
  - exact I.
  - destruct L as [|b L']; [exact I|].
    destruct L' as [|c r]; [exact I|].
    rewrite open_path_cons3.
    pose proof Hadj as Hadj0.
    rewrite adj_cons in Hadj0. destruct Hadj0 as [Hab Hadj1].
    pose proof Hadj1 as Hadj2.
    rewrite adj_cons in Hadj2. destruct Hadj2 as [Hbc _].
    rewrite mediators_unfold in Hm.
    rewrite confounders_unfold in Hc.
    rewrite colliders_unfold in Hcol.
    apply overlap_if in Hm. destruct Hm as [Hm1 Hm2].
    apply overlap_if in Hc. destruct Hc as [Hc1 Hc2].
    apply colliders_ok_if in Hcol. destruct Hcol as [Hcol1 Hcol2].
    split.
    + unfold triple_ok. split.
      * intros [E1 E2].
        assert (Hcl : is_collider_bool a c b G = true)
          by (unfold is_collider_bool; rewrite E1, E2; reflexivity).
        pose proof (Hcol2 Hcl) as Hs.
        assert (Hs' : overlap (find_descendants b G) Z = true) by exact Hs.
        apply (proj1 (overlap_has_member_in_common _ _)) in Hs'.
        destruct Hs' as [d [Hd1 Hd2]]. exists d. split; assumption.
      * intros Hnc HbZ.
        destruct (noncollider_mc G a b c Hab Hbc Hnc) as [Hmed | Hconf].
        -- exact (Hm2 Hmed HbZ).
        -- exact (Hc2 Hconf HbZ).
    + apply IH; assumption.
Qed.

Lemma lists_short : forall G Z (L: nodes),
  (L = [] \/ (exists a, L = [a]) \/ (exists a b, L = [a; b])) ->
  overlap Z (find_mediators_in_nodes L G) = false /\
  overlap Z (find_confounders_in_nodes L G) = false /\
  all_colliders_have_descendant_conditioned_on (find_colliders_in_nodes L G) G Z = true.
Proof.
  intros G Z L [H | [[a H] | [a [b H]]]]; subst L;
  cbn [find_mediators_in_nodes find_confounders_in_nodes find_colliders_in_nodes];
  repeat split; try apply overlap_nil; reflexivity.
Qed.

(* ---- bridge B: open_path gives the list conditions of d_connected_2 ---- *)
Lemma lists_from_open_path : forall G Z L,
  G_well_formed G = true -> contains_cycle G = false ->
  adj L G -> open_path G Z L ->
  overlap Z (find_mediators_in_nodes L G) = false /\
  overlap Z (find_confounders_in_nodes L G) = false /\
  all_colliders_have_descendant_conditioned_on (find_colliders_in_nodes L G) G Z = true.
Proof.
  intros G Z L Hwf Hcyc. induction L as [|a L IH]; intros Hadj Hopen.
  - apply lists_short. left. reflexivity.
  - destruct L as [|b L'].
    + apply lists_short. right. left. exists a. reflexivity.
    + destruct L' as [|c r].
      * apply lists_short. right. right. exists a, b. reflexivity.
      * pose proof Hadj as Hadj0.
        rewrite adj_cons in Hadj0. destruct Hadj0 as [Hab Hadj1].
        rewrite open_path_cons3 in Hopen. destruct Hopen as [[Htr1 Htr2] Hopen1].
        destruct (IH Hadj1 Hopen1) as [IHm [IHc IHcol]].
        rewrite mediators_unfold, confounders_unfold, colliders_unfold.
        repeat split.
        -- apply overlap_if_rev; [exact IHm|].
           intros Hcond HbZ.
           exact (Htr2 (mediator_noncollider G a b c Hwf Hcyc Hcond) HbZ).
        -- apply overlap_if_rev; [exact IHc|].
           intros Hcond HbZ.
           exact (Htr2 (confounder_noncollider G a b c Hwf Hcyc Hcond) HbZ).
        -- apply colliders_ok_if_rev; [exact IHcol|].
           intros Hcond.
           apply is_collider_true in Hcond.
           destruct (Htr1 Hcond) as [d [Hd1 Hd2]].
           assert (Hov : overlap (find_descendants b G) Z = true)
             by exact (overlap_mem _ _ d Hd1 Hd2).
           exact Hov.
Qed.

Lemma d_connected_open : forall G Z u v l,
  adj (u :: l ++ [v]) G -> d_connected_2 (u, v, l) G Z ->
  open_path G Z (u :: l ++ [v]).
Proof.
  intros G Z u v l Hadj Hconn. unfold d_connected_2 in Hconn.
  destruct Hconn as [H1 [H2 H3]].
  rewrite mediators_path in H1. rewrite confounders_path in H2.
  rewrite colliders_path in H3.
  apply open_path_from_lists; assumption.
Qed.

Lemma open_d_connected : forall G Z u v l,
  G_well_formed G = true -> contains_cycle G = false ->
  adj (u :: l ++ [v]) G -> open_path G Z (u :: l ++ [v]) ->
  d_connected_2 (u, v, l) G Z.
Proof.
  intros G Z u v l Hwf Hcyc Hadj Hopen.
  destruct (lists_from_open_path G Z _ Hwf Hcyc Hadj Hopen) as [H1 [H2 H3]].
  unfold d_connected_2. rewrite mediators_path, confounders_path, colliders_path.
  repeat split; assumption.
Qed.

(* converse of path_adj *)
Lemma adj_helper_path : forall L G, adj L G -> is_path_in_graph_helper L G = true.
Proof.
  intros L [V E]. induction L as [|a L IH]; intro H.
  - reflexivity.
  - destruct L as [|b L'].
    + reflexivity.
    + rewrite adj_cons in H. destruct H as [Hab Hrest].
      cbn [is_path_in_graph_helper].
      apply andb_true_iff. split.
      * apply orb_true_iff. exact Hab.
      * apply IH. exact Hrest.
Qed.

Lemma adj_path : forall u v l G,
  adj (u :: l ++ [v]) G -> is_path_in_graph (u, v, l) G = true.
Proof.
  intros u v l G H. apply adj_helper_path. exact H.
Qed.

(* ------------------------------------------------------------------ *)
(* 3. Utilities                                                         *)
(* ------------------------------------------------------------------ *)

Lemma nodup_disj : forall (L1 L2: nodes),
  NoDup (L1 ++ L2) -> forall x, In x L1 -> In x L2 -> False.
Proof.
  induction L1 as [|a L1 IH]; intros L2 Hnd x H1 H2.
  - contradiction.
  - cbn [app] in Hnd. apply NoDup_cons_iff in Hnd. destruct Hnd as [Hnotin Hnd'].
    destruct H1 as [Hx | Hx].
    + subst x. apply Hnotin. apply in_or_app. right. exact H2.
    + exact (IH L2 Hnd' x Hx H2).
Qed.

Lemma nodup_app_intro : forall (A C: nodes),
  NoDup A -> NoDup C -> (forall x, In x A -> In x C -> False) -> NoDup (A ++ C).
Proof.
  induction A as [|a A IH]; intros C HA HC Hd.
  - exact HC.
  - cbn [app]. apply NoDup_cons_iff in HA. destruct HA as [Hnotin HA'].
    apply NoDup_cons_iff. split.
    + intro Hin. apply in_app_or in Hin. destruct Hin as [H|H].
      * exact (Hnotin H).
      * exact (Hd a (in_eq _ _) H).
    + apply IH; [exact HA' | exact HC |]. intros x H1 H2. exact (Hd x (or_intror H1) H2).
Qed.

Lemma nodup_suffix : forall (X Y: nodes), NoDup (X ++ Y) -> NoDup Y.
Proof.
  induction X as [|a X IH]; intros Y H.
  - exact H.
  - cbn [app] in H. apply NoDup_cons_iff in H. destruct H as [_ Hnd]. exact (IH Y Hnd).
Qed.

Lemma nodup_prefix : forall (X Y: nodes), NoDup (X ++ Y) -> NoDup X.
Proof.
  induction X as [|a X IH]; intros Y H.
  - constructor.
  - cbn [app] in H. apply NoDup_cons_iff in H. destruct H as [Hn Hnd].
    apply NoDup_cons_iff. split.
    + intro Hin. apply Hn. apply in_or_app. left. exact Hin.
    + exact (IH Y Hnd).
Qed.

Lemma in_rev_fwd : forall (l: nodes) (x: node), In x l -> In x (rev l).
Proof.
  induction l as [|a l IH]; intros x H.
  - contradiction.
  - simpl. apply in_or_app. destruct H as [H | H].
    + right. left. exact H.
    + left. exact (IH x H).
Qed.

Lemma rev_cons_app : forall (y: node) (Y K: nodes), rev (y :: Y) ++ K = rev Y ++ y :: K.
Proof.
  intros y Y K. simpl. symmetry. exact (app_assoc (rev Y) [y] K).
Qed.

Lemma dec_inter : forall (D B: nodes),
  (exists y, In y D /\ In y B) \/ (forall y, In y D -> ~ In y B).
Proof.
  induction D as [|a D IH]; intros B.
  - right. intros y H. contradiction.
  - destruct (IH B) as [[y [H1 H2]] | H].
    + left. exists y. split; [right; exact H1 | exact H2].
    + destruct (in_dec Nat.eq_dec a B) as [Ha | Ha].
      * left. exists a. split; [left; reflexivity | exact Ha].
      * right. intros y Hy. destruct Hy as [Hy | Hy].
        -- subst y. exact Ha.
        -- exact (H y Hy).
Qed.

(* split D at its last member that lies in B *)
Lemma last_in_decomp : forall (D B: nodes),
  (exists y, In y D /\ In y B) ->
  exists D1 x D2, D = D1 ++ x :: D2 /\ In x B /\ (forall y, In y D2 -> ~ In y B).
Proof.
  induction D as [|a D IH]; intros B [y [Hy HyB]].
  - contradiction.
  - destruct (dec_inter D B) as [Hin | Hnone].
    + destruct (IH B Hin) as [D1 [x [D2 [HD [HxB HD2]]]]].
      exists (a :: D1), x, D2. split.
      * rewrite HD; reflexivity.
      * split; assumption.
    + destruct Hy as [Hy | Hy].
      * subst y. exists [], a, D. split; [reflexivity | split; [exact HyB | exact Hnone]].
      * exfalso. exact (Hnone y Hy HyB).
Qed.

Lemma suffix_last : forall (U S B0: nodes) (h: node),
  U ++ S = B0 ++ [h] -> S <> [] -> exists S', S = S' ++ [h].
Proof.
  intros U S B0 h H Hne.
  destruct (exists_last Hne) as [S' [a HS]]. subst S.
  rewrite app_assoc in H.
  destruct (app_inj_tail _ _ _ _ H) as [_ Ha]. subst a.
  exists S'. reflexivity.
Qed.

Lemma lift_head : forall (P: node -> Prop) (w: node) (Bt' : nodes) (w0: node) (Bt0: nodes),
  P w -> w :: Bt' = w0 :: Bt0 -> P w0.
Proof.
  intros P w Bt' w0 Bt0 H E. injection E as Hw _. rewrite <- Hw. exact H.
Qed.

Lemma acyclic2_nodup : forall u v l, acyclic_path_2 (u, v, l) -> NoDup (u :: l ++ [v]).
Proof.
  intros u v l H. apply acyclic_path_spec in H. simpl in H.
  destruct H as [Hne [Hu [Hv Hnd]]].
  apply NoDup_cons_iff. split.
  - intro Hin. apply in_app_or in Hin. destruct Hin as [H1 | H1].
    + exact (Hu H1).
    + destruct H1 as [H1 | H1]; [apply Hne; symmetry; exact H1 | contradiction].
  - apply nodup_app_intro.
    + exact Hnd.
    + apply NoDup_cons_iff. split; [intro H0; contradiction | constructor].
    + intros x H1 H2. destruct H2 as [H2 | H2]; [subst x; exact (Hv H1) | contradiction].
Qed.

Lemma nodup_acyclic2 : forall u v l, NoDup (u :: l ++ [v]) -> acyclic_path_2 (u, v, l).
Proof.
  intros u v l H. apply NoDup_cons_iff in H. destruct H as [Hn Hnd].
  apply (proj2 (acyclic_path_spec (u, v, l))). simpl.
  repeat split.
  - intro E. apply Hn. apply in_or_app. right. left. symmetry. exact E.
  - intro H'. apply Hn. apply in_or_app. left. exact H'.
  - intro H'. exact (nodup_disj l [v] Hnd v H' (in_eq _ _)).
  - exact (nodup_prefix l [v] Hnd).
Qed.

(* ---- adj / open_path: tails and cons-at-the-front ---- *)
Lemma adj_tail : forall a L G, adj (a :: L) G -> adj L G.
Proof.
  intros a L G H. destruct L as [|b L'].
  - exact I.
  - rewrite adj_cons in H. exact (proj2 H).
Qed.

Lemma adj_app_right : forall X L G, adj (X ++ L) G -> adj L G.
Proof.
  induction X as [|a X IH]; intros L G H.
  - exact H.
  - cbn [app] in H. apply IH. exact (adj_tail _ _ _ H).
Qed.

Lemma open_path_tail : forall G Z a L, open_path G Z (a :: L) -> open_path G Z L.
Proof.
  intros G Z a L H. destruct L as [|b [|c r]].
  - exact I.
  - exact I.
  - rewrite open_path_cons3 in H. exact (proj2 H).
Qed.

Lemma open_path_app_right : forall G Z X L, open_path G Z (X ++ L) -> open_path G Z L.
Proof.
  intros G Z X. induction X as [|a X IH]; intros L H.
  - exact H.
  - cbn [app] in H. apply IH. exact (open_path_tail _ _ _ _ H).
Qed.

Lemma adj_cons_front : forall G y e Bt,
  adj (e :: Bt) G ->
  (is_edge (y, e) G = true \/ is_edge (e, y) G = true) ->
  adj (y :: e :: Bt) G.
Proof. intros G y e Bt H1 H2. rewrite adj_cons. split; assumption. Qed.

Lemma open_cons_front : forall G Z y e Bt,
  open_path G Z (e :: Bt) ->
  (forall w Bt', Bt = w :: Bt' -> triple_ok G Z y e w) ->
  open_path G Z (y :: e :: Bt).
Proof.
  intros G Z y e Bt H1 H2. destruct Bt as [|w Bt'].
  - exact I.
  - rewrite open_path_cons3. split.
    + assert (Hw : w :: Bt' = w :: Bt') by reflexivity. exact (H2 w Bt' Hw).
    + exact H1.
Qed.

(* an edge e -> y makes e a non-collider on y - e - w *)
Lemma triple_down : forall G Z y e w,
  G_well_formed G = true -> contains_cycle G = false ->
  is_edge (e, y) G = true -> ~ In e Z -> triple_ok G Z y e w.
Proof.
  intros G Z y e w Hwf Hcyc Hey HeZ. split.
  - intros [E1 _]. exfalso. exact (no_two_cycle G y e Hwf Hcyc E1 Hey).
  - intros _. exact HeZ.
Qed.

(* a conditioned middle node must be a collider, so its left edge points into it *)
Lemma collider_forced : forall G Zc a b c,
  triple_ok G Zc a b c -> In b Zc -> is_edge (a, b) G = true.
Proof.
  intros G Zc a b c [_ H2] Hb.
  destruct (is_edge (a, b) G) eqn:E1; [reflexivity|].
  exfalso. refine (H2 _ Hb). intros [Hc _]. congruence.
Qed.

(* ------------------------------------------------------------------ *)
(* 4. Descendants in G versus the backdoor graph                        *)
(* ------------------------------------------------------------------ *)

Definition good_pair (G: graph) (T: nodes) : Prop :=
  G_well_formed G = true /\ contains_cycle G = false /\
  G_well_formed (remove_outgoing_edges T G) = true /\
  contains_cycle (remove_outgoing_edges T G) = false.

Fixpoint dadj (L: nodes) (G: graph) : Prop :=
  match L with
  | a :: ((b :: _) as t) => is_edge (a, b) G = true /\ dadj t G
  | _ => True
  end.

Lemma dadj_cons : forall a b r G,
  dadj (a :: b :: r) G = (is_edge (a, b) G = true /\ dadj (b :: r) G).
Proof. reflexivity. Qed.

Lemma dadj_helper : forall L G, is_dir_path_in_graph_helper L G = true -> dadj L G.
Proof.
  induction L as [|a L IH]; intros G H.
  - exact I.
  - destruct L as [|b L'].
    + exact I.
    + cbn [is_dir_path_in_graph_helper] in H.
      apply andb_true_iff in H. destruct H as [Hab Hr].
      rewrite dadj_cons. split.
      * exact Hab.
      * apply IH. exact Hr.
Qed.

Lemma dadj_tail : forall a L G, dadj (a :: L) G -> dadj L G.
Proof.
  intros a L G H. destruct L as [|b L'].
  - exact I.
  - rewrite dadj_cons in H. exact (proj2 H).
Qed.

Lemma dadj_app_right : forall X L G, dadj (X ++ L) G -> dadj L G.
Proof.
  induction X as [|a X IH]; intros L G H.
  - exact H.
  - cbn [app] in H. apply IH. exact (dadj_tail _ _ _ H).
Qed.

(* every node on a directed path from a descendant of t is a descendant of t *)
Lemma dadj_desc : forall G t L,
  G_well_formed G = true -> contains_cycle G = false ->
  dadj L G ->
  (match L with x :: _ => In x (find_descendants t G) | [] => True end) ->
  forall y, In y L -> In y (find_descendants t G).
Proof.
  intros G t L Hwf Hcyc. induction L as [|a L IH]; intros Hd Hhd y Hy.
  - contradiction.
  - destruct Hy as [Hy | Hy].
    + subst y. exact Hhd.
    + destruct L as [|b L'].
      * contradiction.
      * rewrite dadj_cons in Hd. destruct Hd as [Hab Hd'].
        exact (IH Hd' (desc_step G t a b Hwf Hcyc Hhd Hab) y Hy).
Qed.

Lemma desc_path : forall G c d,
  G_well_formed G = true -> contains_cycle G = false ->
  In d (find_descendants c G) ->
  d = c \/ exists l, dadj (c :: l ++ [d]) G /\ acyclic_path_2 (c, d, l).
Proof.
  intros G c d Hwf Hcyc H.
  apply (proj1 (find_descendants_correct G c d Hwf Hcyc)) in H.
  destruct H as [Heq | [U [Hdir Hse]]].
  - left. symmetry. exact Heq.
  - right. destruct U as [[u v] l].
    apply path_start_end_equal in Hse. destruct Hse as [Hu Hv].
    rewrite Hu in Hdir. rewrite Hv in Hdir.
    exists l. split.
    + apply dadj_helper. exact Hdir.
    + assert (Hac : acyclic_path_2 (c, d, l))
        by (eapply contains_cycle_false_correct; eauto).
      exact Hac.
Qed.

(* a directed path in G either survives in the backdoor graph or runs into T *)
Lemma desc_conv_aux : forall G T,
  good_pair G T ->
  forall l c d, dadj (c :: l ++ [d]) G ->
    In d (find_descendants c (remove_outgoing_edges T G)) \/
    exists t, In t T /\ In t (find_descendants c (remove_outgoing_edges T G)).
Proof.
  intros G T Hgood. assert (Hg := Hgood). destruct Hg as [Hwf [Hcyc [Hwf' Hcyc']]].
  induction l as [|b l IH]; intros c d Hd.
  - cbn [app] in Hd. rewrite dadj_cons in Hd. destruct Hd as [Hcd _].
    destruct (in_dec Nat.eq_dec c T) as [HcT | HcT].
    + right. exists c. split; [exact HcT | apply node_is_descendant_of_itself].
    + left. exact (desc_edge _ c d Hwf' Hcyc'
                     (proj2 (backdoor_is_edge T G c d) (conj Hcd HcT))).
  - cbn [app] in Hd. rewrite dadj_cons in Hd. destruct Hd as [Hcb Hd'].
    destruct (in_dec Nat.eq_dec c T) as [HcT | HcT].
    + right. exists c. split; [exact HcT | apply node_is_descendant_of_itself].
    + assert (Hbc : In b (find_descendants c (remove_outgoing_edges T G)))
        by exact (desc_edge _ c b Hwf' Hcyc'
                    (proj2 (backdoor_is_edge T G c b) (conj Hcb HcT))).
      destruct (IH b d Hd') as [H | [t [Ht H]]].
      * left. exact (desc_trans _ d b c Hwf' Hcyc' Hbc H).
      * right. exists t. split; [exact Ht | exact (desc_trans _ t b c Hwf' Hcyc' Hbc H)].
Qed.

Lemma desc_conv : forall G T c d,
  good_pair G T -> In d (find_descendants c G) ->
  In d (find_descendants c (remove_outgoing_edges T G)) \/
  exists t, In t T /\ In t (find_descendants c (remove_outgoing_edges T G)).
Proof.
  intros G T c d Hgood Hd. assert (Hg := Hgood). destruct Hg as [Hwf [Hcyc _]].
  destruct (desc_path G c d Hwf Hcyc Hd) as [Heq | [l [Hl _]]].
  - left. subst d. apply node_is_descendant_of_itself.
  - exact (desc_conv_aux G T Hgood l c d Hl).
Qed.

(* ------------------------------------------------------------------ *)
(* 5. Finishing a path: "bad collider" rerouting, then the sweep        *)
(* Paths are stored REVERSED (head = current endpoint), so every        *)
(* extension is a cons at the front.                                    *)
(* ------------------------------------------------------------------ *)

Definition BdOut (G: graph) (T Z: nodes) (h: node) (K: nodes) : Prop :=
  exists tau, In tau T /\ NoDup K /\
    adj K (remove_outgoing_edges T G) /\
    open_path (remove_outgoing_edges T G) Z K /\
    (exists K', K = tau :: K') /\ (exists K'', K = K'' ++ [h]).

(* walk down a directed path, consing each node on the front *)
Lemma cons_down : forall G T Z,
  good_pair G T ->
  forall (Y: nodes) (x: node) (K': nodes),
    dadj (x :: Y) (remove_outgoing_edges T G) ->
    (forall z, In z (x :: Y) -> ~ In z Z) ->
    NoDup (x :: K') ->
    (forall z, In z Y -> ~ In z (x :: K')) ->
    NoDup Y ->
    adj (x :: K') (remove_outgoing_edges T G) ->
    open_path (remove_outgoing_edges T G) Z (x :: K') ->
    NoDup (rev Y ++ x :: K') /\
    adj (rev Y ++ x :: K') (remove_outgoing_edges T G) /\
    open_path (remove_outgoing_edges T G) Z (rev Y ++ x :: K').
Proof.
  intros G T Z Hgood. assert (Hg := Hgood). destruct Hg as [Hwf [Hcyc [Hwf' Hcyc']]].
  induction Y as [|y Y IH]; intros x K' Hd HZ Hnd Hdisj HndY Hadj Hopen.
  - exact (conj Hnd (conj Hadj Hopen)).
  - rewrite rev_cons_app.
    rewrite dadj_cons in Hd. destruct Hd as [Hxy Hd'].
    apply NoDup_cons_iff in HndY. destruct HndY as [HyY HndY'].
    assert (Hyk : ~ In y (x :: K')) by (apply Hdisj; left; reflexivity).
    assert (HxZ : ~ In x Z) by (apply HZ; left; reflexivity).
    apply (IH y (x :: K')).
    + exact Hd'.
    + intros z Hz. apply HZ. right. exact Hz.
    + apply NoDup_cons_iff. split; [exact Hyk | exact Hnd].
    + intros z Hz Hzin. destruct Hzin as [Hzy | Hzin].
      * subst z. exact (HyY Hz).
      * exact (Hdisj z (or_intror Hz) Hzin).
    + exact HndY'.
    + apply adj_cons_front; [exact Hadj | right; exact Hxy].
    + apply open_cons_front; [exact Hopen |].
      intros w K'' E. exact (triple_down _ Z y x w Hwf' Hcyc' Hxy HxZ).
Qed.

(* A "bad" collider e (no descendant in Z in the backdoor graph) has a descendant
   tau in T. Splice a directed path from e to tau onto the part of B up to the last
   node they share. *)
Lemma reroute :
  forall G T Z h B e,
    good_pair G T ->
    NoDup B -> (forall x, In x B -> ~ In x T) ->
    adj B (remove_outgoing_edges T G) ->
    open_path (remove_outgoing_edges T G) Z B ->
    (exists B0, B = B0 ++ [h]) ->
    In e B ->
    (forall d, In d (find_descendants e (remove_outgoing_edges T G)) -> ~ In d Z) ->
    (exists t, In t T /\ In t (find_descendants e (remove_outgoing_edges T G))) ->
    exists K, BdOut G T Z h K.
Proof.
  intros G T Z h B e Hgood HndB HBT HadjB HopenB [B0 HB0] HeB Hbad [tau [Htau Htaud]].
  assert (Hg := Hgood). destruct Hg as [Hwf [Hcyc [Hwf' Hcyc']]].
  assert (HeT : ~ In e T) by (apply HBT; exact HeB).
  assert (Hne : tau <> e) by (intro E; apply HeT; rewrite <- E; exact Htau).
  destruct (desc_path _ e tau Hwf' Hcyc' Htaud) as [Heq | [l [Hdadj Hac]]].
  { exfalso. apply Hne. exact Heq. }
  assert (HndD : NoDup (e :: l ++ [tau])) by exact (acyclic2_nodup e tau l Hac).
  assert (HallD : forall z, In z (e :: l ++ [tau]) ->
                    In z (find_descendants e (remove_outgoing_edges T G)))
    by exact (dadj_desc _ e _ Hwf' Hcyc' Hdadj (node_is_descendant_of_itself e _)).
  destruct (last_in_decomp (e :: l) B (ex_intro _ e (conj (in_eq _ _) HeB)))
    as [D1 [x [D2 [HD [HxB HD2]]]]].
  assert (HD' : e :: l ++ [tau] = D1 ++ x :: (D2 ++ [tau])).
  { change (e :: l ++ [tau]) with ((e :: l) ++ [tau]).
    rewrite HD; rewrite <- app_assoc; reflexivity. }
  assert (Hdadj2 : dadj (x :: D2 ++ [tau]) (remove_outgoing_edges T G)).
  { rewrite HD' in Hdadj. exact (dadj_app_right _ _ _ Hdadj). }
  assert (HndY : NoDup (x :: D2 ++ [tau])).
  { rewrite HD' in HndD. exact (nodup_suffix _ _ HndD). }
  destruct (in_split x B HxB) as [U [V HBsplit]].
  assert (HndV : NoDup (x :: V)) by (rewrite HBsplit in HndB; exact (nodup_suffix _ _ HndB)).
  assert (HadjV : adj (x :: V) (remove_outgoing_edges T G))
    by (rewrite HBsplit in HadjB; exact (adj_app_right _ _ _ HadjB)).
  assert (HopenV : open_path (remove_outgoing_edges T G) Z (x :: V))
    by (rewrite HBsplit in HopenB; exact (open_path_app_right _ _ _ _ HopenB)).
  assert (HndY' : NoDup (D2 ++ [tau])).
  { apply NoDup_cons_iff in HndY. exact (proj2 HndY). }
  assert (Hnz : forall z, In z (x :: D2 ++ [tau]) -> ~ In z Z).
  { intros z Hz. apply Hbad. apply HallD. rewrite HD'. apply in_or_app. right. exact Hz. }
  assert (Hdisj : forall z, In z (D2 ++ [tau]) -> ~ In z (x :: V)).
  { intros z Hz Hzin. apply in_app_or in Hz. destruct Hz as [Hz | Hz].
    - apply (HD2 z Hz). rewrite HBsplit. apply in_or_app. right. exact Hzin.
    - destruct Hz as [Hz | Hz]; [| contradiction]. subst z.
      assert (HtB : In tau B).
      { rewrite HBsplit. apply in_or_app. right. exact Hzin. }
      exact (HBT tau HtB Htau). }
  destruct (cons_down G T Z Hgood (D2 ++ [tau]) x V Hdadj2 Hnz HndV Hdisj HndY' HadjV HopenV)
    as [Hnd3 [Hadj3 Hopen3]].
  assert (Hlast : exists K'', rev (D2 ++ [tau]) ++ x :: V = K'' ++ [h]).
  { destruct (suffix_last U (x :: V) B0 h) as [S' HS'].
    - rewrite <- HBsplit. exact HB0.
    - intro H. discriminate H.
    - exists (rev (D2 ++ [tau]) ++ S'). rewrite HS'. exact (app_assoc _ _ _). }
  exists (rev (D2 ++ [tau]) ++ x :: V). unfold BdOut. exists tau.
  split; [exact Htau |].
  split; [exact Hnd3 |].
  split; [exact Hadj3 |].
  split; [exact Hopen3 |].
  split.
  - exists (rev D2 ++ x :: V). rewrite rev_app_distr; reflexivity.
  - exact Hlast.
Qed.

(* The sweep: walk along pi from h, keeping a prefix B (stored reversed) that is an
   open path in the backdoor graph avoiding T. *)
Lemma sweep :
  forall G T Z h p,
    good_pair G T ->
    ~ In h T -> ~ In h Z -> ~ In p T -> ~ In p Z ->
    (exists t0, In t0 T /\ is_edge (p, t0) G = true) ->
    forall (pi: nodes),
      (exists pi0, pi = pi0 ++ [p]) ->
      NoDup pi -> adj pi G -> open_path G (T ++ Z) pi ->
      forall (R B: nodes),
        pi = rev B ++ R ->
        NoDup B -> (forall x, In x B -> ~ In x T) ->
        adj B (remove_outgoing_edges T G) ->
        open_path (remove_outgoing_edges T G) Z B ->
        (exists B0, B = B0 ++ [h]) ->
        exists K, BdOut G T Z h K.
Proof.
  intros G T Z h p Hgood HhT HhZ HpT HpZ [t0 [Ht0 Hpt0]] pi Hlast Hnd Hadj Hopen R.
  assert (Hg := Hgood). destruct Hg as [Hwf [Hcyc [Hwf' Hcyc']]].
  induction R as [|y R' IH]; intros B Hpi HndB HBT HadjB HopenB HB0'.
  - (* pi exhausted: the endpoint is p; append t0 *)
    destruct HB0' as [B0 HB0].
    destruct B as [|e Bt].
    + exfalso. destruct B0; discriminate HB0.
    + rewrite app_nil_r in Hpi.
      destruct Hlast as [pi0 Hpi0].
      assert (Hep : e = p).
      { rewrite Hpi0 in Hpi. simpl in Hpi.
        symmetry. exact (proj2 (app_inj_tail _ _ _ _ Hpi)). }
      subst e.
      assert (Hedge' : is_edge (p, t0) (remove_outgoing_edges T G) = true)
        by (apply (proj2 (backdoor_is_edge T G p t0)); split; assumption).
      exists (t0 :: p :: Bt). unfold BdOut. exists t0.
      split; [exact Ht0 |].
      split.
      { apply NoDup_cons_iff. split.
        - intro H. exact (HBT t0 H Ht0).
        - exact HndB. }
      split; [exact (adj_cons_front _ t0 p Bt HadjB (or_intror Hedge')) |].
      split.
      { exact (open_cons_front _ Z t0 p Bt HopenB
                 (fun w Bt' _ => triple_down _ Z t0 p w Hwf' Hcyc' Hedge' HpZ)). }
      split; [exists (p :: Bt); reflexivity |].
      exists (t0 :: B0). simpl. f_equal. exact HB0.
  - (* next node of pi is y *)
    destruct HB0' as [B0 HB0].
    destruct B as [|e Bt].
    + exfalso. destruct B0; discriminate HB0.
    + pose proof Hpi as Hpi_orig.
      assert (HeB : In e (e :: Bt)) by (left; reflexivity).
      assert (HeT : ~ In e T) by (apply HBT; exact HeB).
      rewrite rev_cons_app in Hpi.
      assert (Hey : is_edge (e, y) G = true \/ is_edge (y, e) G = true).
      { assert (Ha : adj (e :: y :: R') G)
          by (rewrite Hpi in Hadj; exact (adj_app_right _ _ _ Hadj)).
        rewrite adj_cons in Ha. exact (proj1 Ha). }
      assert (HyB : ~ In y (e :: Bt)).
      { intro Hy.
        assert (Hnd' : NoDup (rev (e :: Bt) ++ y :: R'))
          by (rewrite <- Hpi_orig; exact Hnd).
        assert (Hy' : In y (rev (e :: Bt))) by exact (in_rev_fwd _ _ Hy).
        exact (nodup_disj _ _ Hnd' y Hy' (in_eq _ _)). }
      destruct (in_dec Nat.eq_dec y T) as [HyT | HyT].
      * (* y in T: the path ends here *)
        assert (Hey_edge : is_edge (e, y) G = true).
        { destruct R' as [|y2 R''].
          - exfalso. destruct Hlast as [pi0 Hpi0].
            rewrite Hpi0 in Hpi_orig.
            assert (Hyp : p = y) by exact (proj2 (app_inj_tail _ _ _ _ Hpi_orig)).
            apply HpT. rewrite Hyp. exact HyT.
          - assert (Ho : open_path G (T ++ Z) (e :: y :: y2 :: R'')).
            { rewrite Hpi in Hopen. exact (open_path_app_right _ _ _ _ Hopen). }
            rewrite open_path_cons3 in Ho. destruct Ho as [Htr _].
            exact (collider_forced G (T ++ Z) e y y2 Htr (in_or_app _ _ _ (or_introl HyT))). }
        assert (Hey' : is_edge (e, y) (remove_outgoing_edges T G) = true)
          by (apply (proj2 (backdoor_is_edge T G e y)); split; assumption).
        assert (Hye : is_edge (y, e) G = false).
        { destruct (is_edge (y, e) G) eqn:E; [|reflexivity].
          exfalso. exact (no_two_cycle G y e Hwf Hcyc E Hey_edge). }
        assert (HeZ : ~ In e Z).
        { destruct Bt as [|w Bt'].
          - destruct (app_inj_tail [] B0 e h HB0) as [_ Heh]. rewrite Heh. exact HhZ.
          - assert (Ho : open_path G (T ++ Z) (w :: e :: y :: R')).
            { rewrite rev_cons_app in Hpi. rewrite Hpi in Hopen.
              exact (open_path_app_right _ _ _ _ Hopen). }
            rewrite open_path_cons3 in Ho. destruct Ho as [[_ H2] _].
            intro HeZ0.
            refine (H2 _ (in_or_app T Z e (or_intror HeZ0))).
            intros [_ Hc]. congruence. }
        exists (y :: e :: Bt). unfold BdOut. exists y.
        split; [exact HyT |].
        split; [apply NoDup_cons_iff; split; [exact HyB | exact HndB] |].
        split; [exact (adj_cons_front _ y e Bt HadjB (or_intror Hey')) |].
        split.
        { exact (open_cons_front _ Z y e Bt HopenB
                   (fun w Bt' _ => triple_down _ Z y e w Hwf' Hcyc' Hey' HeZ)). }
        split; [exists (e :: Bt); reflexivity |].
        exists (y :: B0). simpl. f_equal. exact HB0.
      * (* y not in T *)
        assert (Hey'' : is_edge (y, e) (remove_outgoing_edges T G) = true \/
                        is_edge (e, y) (remove_outgoing_edges T G) = true).
        { destruct Hey as [H | H].
          - right. apply (proj2 (backdoor_is_edge T G e y)). split; assumption.
          - left. apply (proj2 (backdoor_is_edge T G y e)). split; assumption. }
        assert (Hcase :
          (forall w Bt', Bt = w :: Bt' ->
             triple_ok (remove_outgoing_edges T G) Z y e w) \/
          (exists t, In t T /\ In t (find_descendants e (remove_outgoing_edges T G)) /\
             (forall d, In d (find_descendants e (remove_outgoing_edges T G)) -> ~ In d Z))).
        { destruct Bt as [|w Bt'].
          - left. intros w Bt' H. discriminate H.
          - assert (Htr : triple_ok G (T ++ Z) w e y).
            { assert (Ho : open_path G (T ++ Z) (w :: e :: y :: R')).
              { rewrite rev_cons_app in Hpi. rewrite Hpi in Hopen.
                exact (open_path_app_right _ _ _ _ Hopen). }
              rewrite open_path_cons3 in Ho. exact (proj1 Ho). }
            destruct Htr as [Htr1 Htr2].
            assert (HwT : ~ In w T) by (apply HBT; right; left; reflexivity).
            assert (Hnc_ext : ~ (is_edge (w, e) G = true /\ is_edge (y, e) G = true) ->
                              triple_ok (remove_outgoing_edges T G) Z y e w).
            { intro Hnc. split.
              - intros [E1 E2]. exfalso. apply Hnc. split.
                + exact (proj1 (proj1 (backdoor_is_edge T G w e) E2)).
                + exact (proj1 (proj1 (backdoor_is_edge T G y e) E1)).
              - intros _ HeZ. exact (Htr2 Hnc (in_or_app _ _ _ (or_intror HeZ))). }
            destruct (is_edge (w, e) G) eqn:Ew.
            + destruct (is_edge (y, e) G) eqn:Ey.
              * (* collider on pi *)
                assert (Htr1': true = true /\ true = true).
                  split; reflexivity.
                apply Htr1 in Htr1'.
                destruct (Htr1') as [d [Hd1 Hd2]].
                destruct (dec_inter (find_descendants e (remove_outgoing_edges T G)) Z)
                  as [[d' [Hd'1 Hd'2]] | Hnone].
                -- left. intros w0 Bt0 E.
                   refine (lift_head (fun v => triple_ok (remove_outgoing_edges T G) Z y e v)
                             w Bt' w0 Bt0 _ E).
                   split.
                   ++ intros _. exists d'. split; assumption.
                   ++ intros Hn. exfalso. apply Hn. split.
                      ** apply (proj2 (backdoor_is_edge T G y e)). split; [exact Ey | exact HyT].
                      ** apply (proj2 (backdoor_is_edge T G w e)). split; [exact Ew | exact HwT].
                -- right.
                   destruct (desc_conv G T e d Hgood Hd1) as [Hdd | [t [Ht Hdt]]].
                   ++ apply in_app_or in Hd2. destruct Hd2 as [HdT | HdZ].
                      ** exists d. split; [exact HdT | split; [exact Hdd | exact Hnone]].
                      ** exfalso. exact (Hnone d Hdd HdZ).
                   ++ exists t. split; [exact Ht | split; [exact Hdt | exact Hnone]].
              * left. intros w0 Bt0 E.
                refine (lift_head (fun v => triple_ok (remove_outgoing_edges T G) Z y e v)
                          w Bt' w0 Bt0 _ E).
                apply Hnc_ext. intros [_ Hc]. congruence.
            + left. intros w0 Bt0 E.
              refine (lift_head (fun v => triple_ok (remove_outgoing_edges T G) Z y e v)
                        w Bt' w0 Bt0 _ E).
              apply Hnc_ext. intros [Hc _]. congruence. }
        destruct Hcase as [Hext | [t [Ht [Htd Hbad]]]].
        -- (* extend the prefix by y and continue *)
           assert (HndB' : NoDup (y :: e :: Bt))
             by (apply NoDup_cons_iff; split; [exact HyB | exact HndB]).
           assert (HBT' : forall x, In x (y :: e :: Bt) -> ~ In x T).
           { intros x [Hx | Hx].
             - subst x. exact HyT.
             - exact (HBT x Hx). }
           apply (IH (y :: e :: Bt)).
           ++ rewrite rev_cons_app. exact Hpi_orig.
           ++ exact HndB'.
           ++ exact HBT'.
           ++ exact (adj_cons_front _ y e Bt HadjB Hey'').
           ++ exact (open_cons_front _ Z y e Bt HopenB (fun w Bt' H => Hext w Bt' H)).
           ++ exists (y :: B0). simpl. f_equal. exact HB0.
        -- (* e is a bad collider: reroute through a descendant in T *)
           exact (reroute G T Z h (e :: Bt) e Hgood HndB HBT HadjB HopenB
                    (ex_intro _ B0 HB0) HeB Hbad (ex_intro _ t (conj Ht Htd))).
Qed.

Lemma out_to_path : forall G T Z h K,
  ~ In h T -> BdOut G T Z h K ->
  exists m tau, In tau T /\ K = tau :: m ++ [h] /\ NoDup K /\
    adj K (remove_outgoing_edges T G) /\
    open_path (remove_outgoing_edges T G) Z K.
Proof.
  intros G T Z h K HhT HOut. unfold BdOut in HOut.
  destruct HOut as [tau [Htau [Hnd [Hadj [Hopen [[K' HK'] [K'' HK'']]]]]]].
  destruct K' as [|a K'1].
  - exfalso. rewrite HK' in HK''.
    destruct (app_inj_tail [] K'' tau h HK'') as [_ Hth].
    apply HhT. rewrite <- Hth. exact Htau.
  - assert (Hne : a :: K'1 <> []) by (intro H; discriminate H).
    destruct (exists_last Hne) as [m [b Hm]].
    rewrite Hm in HK'. rewrite HK' in HK''.
    assert (E : (tau :: m) ++ [b] = K'' ++ [h]) by exact HK''.
    destruct (app_inj_tail _ _ _ _ E) as [_ Hbh]. subst b.
    exists m, tau.
    split; [exact Htau |].
    split; [exact HK' |].
    exact (conj Hnd (conj Hadj Hopen)).
Qed.

(* ------------------------------------------------------------------ *)
(* 6. The core lemma                                                    *)
(* ------------------------------------------------------------------ *)

Lemma backdoor_reroute :
  forall (G: graph) (T Z: nodes) (h p: node) (l: nodes),
    G_well_formed G = true -> contains_cycle G = false ->
    ~ In h T -> ~ In h Z -> ~ In p T -> ~ In p Z ->
    In p (find_parents_set T G) ->
    acyclic_path_2 (h, p, l) ->
    adj (h :: l ++ [p]) G ->
    open_path G (T ++ Z) (h :: l ++ [p]) ->
    exists (m: nodes) (tau: node),
      In tau T /\
      acyclic_path_2 (tau, h, m) /\
      adj (tau :: m ++ [h]) (remove_outgoing_edges T G) /\
      open_path (remove_outgoing_edges T G) Z (tau :: m ++ [h]).
Proof.
  intros G T Z h p l Hwf Hcyc HhT HhZ HpT HpZ Hpin Hac Hadj Hopen.
  assert (Hgood : good_pair G T)
    by exact (conj Hwf (conj Hcyc (conj (backdoor_well_formed T G Hwf)
                                        (backdoor_acyclic T G Hwf Hcyc)))).
  destruct (parents_set_elim G T p Hpin) as [t0 [Ht0 Hpar]].
  assert (Hpt0 : is_edge (p, t0) G = true)
    by (apply (proj2 (is_edge_parent G p t0 Hwf)); exact Hpar).
  assert (HndB : NoDup [h]) by (apply NoDup_cons_iff; split; [intro H; contradiction | constructor]).
  assert (HBT : forall x, In x [h] -> ~ In x T).
  { intros x [Hx | []]. subst x. exact HhT. }
  assert (Ht0' : exists t, In t T /\ is_edge (p, t) G = true)
    by (exists t0; split; [exact Ht0 | exact Hpt0]).
  assert (Hlast : exists pi0, h :: l ++ [p] = pi0 ++ [p])
    by (exists (h :: l); reflexivity).
  assert (Hsplit : h :: l ++ [p] = rev [h] ++ (l ++ [p])) by reflexivity.
  assert (HB0 : exists B0, [h] = B0 ++ [h]) by (exists []; reflexivity).
  assert (HadjB : adj [h] (remove_outgoing_edges T G)) by exact I.
  assert (HopenB : open_path (remove_outgoing_edges T G) Z [h]) by exact I.
  destruct (sweep G T Z h p Hgood HhT HhZ HpT HpZ Ht0'
              (h :: l ++ [p]) Hlast (acyclic2_nodup h p l Hac) Hadj Hopen
              (l ++ [p]) [h] Hsplit HndB HBT HadjB HopenB HB0)
    as [K HK].
  destruct (out_to_path G T Z h K HhT HK) as [m [tau [Htau [HKeq [Hnd [Hadj' Hopen']]]]]].
  subst K. exists m, tau.
  split; [exact Htau |].
  split; [exact (nodup_acyclic2 tau h m Hnd) |].
  exact (conj Hadj' Hopen').
Qed.

(* ------------------------------------------------------------------ *)
(* 7. Main theorem                                                      *)
(* ------------------------------------------------------------------ *)

Theorem DSep_H_PaT :
  forall (G: graph) (T H Z: nodes),
    G_well_formed G = true /\ contains_cycle G = false ->
    (* T and H are d-separated given Z in the backdoor graph *)
    (forall t h, In t T -> In h H ->
        d_separated_bool t h (remove_outgoing_edges T G) Z = true) ->
    (* the conditioning set T ++ Z must not contain the endpoints *)
    (forall p, In p (find_parents_set T G) -> ~ In p T /\ ~ In p Z) ->
    (forall h, In h H -> ~ In h T /\ ~ In h Z) ->
    forall h p, In h H -> In p (find_parents_set T G) ->
      d_separated_bool h p G (T ++ Z) = true.
Proof.
  intros G T H Z Hgood Hsep Hpa Hh h p Hhin Hpin.
  assert (Hg := Hgood). destruct Hg as [Hwf Hcyc].
  assert (Hwf' := backdoor_well_formed T G Hwf).
  assert (Hcyc' := backdoor_acyclic T G Hwf Hcyc).
  destruct (Hh h Hhin) as [HhT HhZ].
  destruct (Hpa p Hpin) as [HpT HpZ].
  destruct (d_separated_bool h p G (T ++ Z)) eqn:Hd; [reflexivity|].
  exfalso.
  apply d_separated_vs_connected in Hd; [| exact Hgood].
  destruct Hd as [l [Hac [Hpath Hconn]]].
  pose proof (path_adj h p l G Hpath) as Hadj.
  pose proof (d_connected_open G (T ++ Z) h p l Hadj Hconn) as Hopen.
  destruct (backdoor_reroute G T Z h p l Hwf Hcyc HhT HhZ HpT HpZ Hpin Hac Hadj Hopen)
    as [m [tau [Htau [Hac' [Hadj' Hopen']]]]].
  pose proof (open_d_connected (remove_outgoing_edges T G) Z tau h m Hwf' Hcyc' Hadj' Hopen')
    as Hconn'.
  pose proof (adj_path tau h m (remove_outgoing_edges T G) Hadj') as Hpath'.
  exact (d_connected_path_not_d_separated tau h m (remove_outgoing_edges T G) Z
           (conj Hwf' Hcyc') Hconn' (conj Hpath' Hac') (Hsep tau h Htau Hhin)).
Qed.

Print Assumptions DSep_H_PaT.
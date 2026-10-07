From mathcomp Require Import ssreflect ssrfun ssrbool eqtype fintype bigop.
From Stdlib Require Import Reals.
From infotheo.probability Require Import proba fdist. (* fsdist jfdist_cond. *)
Require Import List.
Import ListNotations.
From mathcomp Require Import reals.
From mathcomp Require Import all_ssreflect all_algebra fingroup lra ssralg.
From mathcomp Require Import unstable mathcomp_extra reals exp.
From infotheo Require Import ssr_ext ssralg_ext bigop_ext realType_ext realType_ln.
(* Require Import ssr_ext ssralg_ext bigop_ext realType_ext realType_ln. *)
Require Import Classical.
Require Import Field.
Require Import Lia.

From project Require Import GeneralFormulas.

Local Open Scope ring_scope.
Local Open Scope reals_ext_scope.
Local Open Scope fdist_scope.
Local Open Scope proba_scope.

Section ParentalAdjustmentFormula.

Context {R : realType}.
Variables (U : finType).
    (* Set of all unobserved terms -- tuple *)
Variables (outcomesH : finType).
    (* Outcomes of node H *)
Variables (outcomesT : finType).
    (* Outcomes of node T *)
Variables (outcomesPaT : finType).
    (* Outcomes of nodes parents(T) -- tuple *)
Variables (outcomesZ : finType).
    (* Outcomes of nodes Z, those used for backdoor 
        criterion -- tuple *)
Variables (outcomesE : finType).
    (* Outcomes of node E, which is all nodes in the graph 
      except for T, H, paT -- tuple *)
Variable P : R.-fdist (U).

Variable H : {RV P -> outcomesH}.
    (* Variable being measured *)
Variable T : {RV P -> outcomesT}.
    (* Variable being intervened/conditioned on *)
Variable paT : {RV P -> outcomesPaT}.
    (* Set of parents of variable T *)
Variable Z : {RV P -> outcomesZ}.
    (* Set Z that satisfies the backdoor criterion with T->H.
      Note that Z overlaps with E and paT. *)
Variable E : {RV P -> outcomesE}.
    (* Set E, which is all variables in the graph except for 
      T, H and paT. *)
(* Realtionships in the graph:
    paT_i -> T, T -> H, H ... Z_i ... -> T *)

(* All of the node functions under intervention. Take a value
  of type outcomesT, the interventional value of T=t, and
  output a RV. (Tinterv is defined but did not end up getting 
  used, and would be 1 if T=t, 0 if T!=t. So could be 
  explicitly defined instead of just being a variable.)*)
Variable Hinterv : outcomesT -> {RV P -> outcomesH}.
Variable Tinterv : outcomesT -> {RV P -> outcomesT}.
Variable paTinterv : outcomesT -> {RV P -> outcomesPaT}.
Variable Zinterv : outcomesT -> {RV P -> outcomesZ}.
Variable Einterv : outcomesT -> {RV P -> outcomesE}.

(*  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
                SECTION : Parental Adjustment Formula ->
                    Backdoor Adjustment Formula
    %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%  *)

Lemma pair_to_single_non_zero_specialized: 
  (forall (i0 : outcomesPaT) (i1 : outcomesZ) (i2 : outcomesT), 
      `Pr[ [% paT, [% T, Z]] = (i0, (i2, i1)) ] != 0) ->
  (exists z, z \in outcomesZ) ->
  (forall (i0 : outcomesPaT) (i1 : outcomesT),
      `Pr[ [% T, paT] = (i1, i0) ] != 0).
Proof.
  (* move=> H0 i0 i1.
  have Hz : inhabited outcomesZ by exact: (inhabits_fin _).
  destruct Hz as [z].
  have H0 := H i0 z i1.
  (* H0 : Pr[ [% paT, [% T, Z]] = (i0, (i1, z)) ] != 0 *)
  apply: (pair_to_single_non_zero_right paT [% T, Z] i0 (i1, z)) in H0.
  (* H0 : Pr[ [% T, Z] = (i1, z) ] != 0 *)
  exact: (pair_to_single_non_zero_left T Z i1 z H0). *)

  intros.
  specialize (H0 i0).
  (* Check pfwd1_neq0. *)
  (* destruct (classic (exists z, z \in outcomesZ)). *)
  destruct H1 as [z].
  specialize (H0 z i1).
  rewrite pfwd1_pairA in H0.
  rewrite pfwd1_pairC.
  unfold swap.
  simpl.
  pose proof (pair_to_single_non_zero_left [% paT, T] Z (i0, i1) z H0).
  assumption.

  (* apply pair_to_single_non_zero_left in H0. *)
  (* Check pfwd1_pairA. *)
  (* apply pair_to_single_non_zero_right in H0.
  apply pair_to_single_non_zero_right with (X := Z)  *)
  (* specialize (H0 i0 i1).
  Check pfwd1_domin_RV2. *)
Qed.

Lemma cond_to_pair_non_zero: forall {A B : finType} 
  {X : {RV P -> A}} {Y : {RV P -> B}} x y,
  `Pr[ X = x | Y = y ] != 0 ->
  `Pr[ [% X, Y] = (x, y) ] != 0.
Proof.
  intros.
  case: (boolP (`Pr[ Y = y ] == 0)).
  intros.
    move /eqP in p.
    rewrite cpr_eq0_denom in H0; try assumption.
    apply false_cant_be in H0.
    discriminate H0.
  
  intros.
  rewrite cpr_eqE in H0.
  apply div_not_zero with (a := `Pr[ [% X, Y] = (x, y) ]) (b := `Pr[ Y = y ]).
  assumption.
  assumption.
Qed.

Lemma oddly_specific: forall t u z h,
  `Pr[ T=t | paT=u ] != 0 ->
  `Pr[ [% paT, [% T, Z]] = (u, (t, z)) ] = 0 ->
  `Pr[ H = h | [% T, Z] = (t, z) ] * `Pr[ Z = z | [% paT, T] = (u, t) ] * `Pr[ paT = u ] = 0.
Proof.
  intros.
  assert (`Pr[ [% paT, [% T, Z]] = (u, (t, z)) ] = 
      `Pr[ Z = z | [% paT, T] = (u, t) ] * `Pr[ T=t | paT=u] * `Pr[ paT=u]).
    rewrite !cpr_eqE.
    rewrite [in RHS] pfwd1_pairC.
    rewrite -> pfwd1_pairC with (TX := paT) (TY := T).
    unfold swap. simpl.
    rewrite <- pfwd1_pairA.
    rewrite GRing.mulrA.
    rewrite GRing.divfK.
    rewrite GRing.divfK.
    reflexivity.
    apply cond_to_pair_non_zero in H0.
    rewrite pfwd1_pairC. unfold swap. simpl.
    assumption.
    apply cond_to_pair_non_zero in H0.
    apply pair_to_single_non_zero_right in H0.
    assumption.
  rewrite H1 in H2.
  apply esym in H2.
  (* apply Rmult_integral in H2. *)
  (* Check GRing.mulf_eq0. *)
  move /eqP in H2.
  rewrite !GRing.mulf_eq0 in H2.
  move /orP in H2.
  inversion H2.
  move /orP in H3.
  inversion H3.
  
  move /eqP in H4.
  rewrite H4.
  rewrite GRing.mulr0.
  rewrite GRing.mul0r.
  reflexivity.

  move /eqP in H4.
  rewrite H4 in H0.
  apply false_cant_be in H0.
  simpl in H0.
  discriminate H0.

  move /eqP in H3.
  rewrite H3.
  rewrite GRing.mulr0.
  reflexivity.
Qed.

Lemma use_indep_statements: forall h t, 
  Z _|_ T | paT ->
  H _|_ paT | [% T, Z] ->
  (* (exists z, z \in outcomesZ) -> *)
  (* (forall i0 i1, `Pr[ [% T, paT] = (i1, i0) ] != 0) -> *)
  (* (forall i0 i1 i2, `Pr[ [% paT, [% T, Z]] = (i0, (i2, i1)) ] != 0) -> *)
  (forall u t, `Pr[ T=t | paT=u ] != 0) ->
  \sum_(i in outcomesZ) \sum_(u in outcomesPaT)
      `Pr[ H = h | [% T, Z] = (t, i) ] * `Pr[ Z = i | paT = u ] * `Pr[ paT = u ] = 
  \sum_(i in outcomesZ) \sum_(u in outcomesPaT)
      `Pr[ H = h | [% T, Z, paT] = (t, i, u) ] * `Pr[ Z = i | [% paT, T] = (u, t) ] 
      * `Pr[ paT = u ].
Proof.
  intros.
  apply eq_bigr.
  intros.
  apply eq_bigr.
  intros.
  (* apply mult_both_sides_r. *)
  specialize (H2 i0 t).
  pose proof (cond_to_pair_non_zero _ _ H2).
  pose proof (indep_to_equality _ _ _ i t i0 H0 H5).
  rewrite H6.
  case: (boolP (`Pr[ [% paT, [% T, Z]] = (i0, (t, i)) ] == 0)).
    intros.
    move /eqP in p.
    pose proof (oddly_specific _ _ _ h H2 p).
    rewrite H7.
    rewrite cpr_eq0_denom.
    rewrite mult_zero_left.
    rewrite mult_zero_left.
    reflexivity.
    rewrite pfwd1_pairC.
    assumption.
  
  intros.
  (* pose proof (pair_to_single_non_zero_specialized H3 H2).
  specialize (H6 i0 t).
  pose proof (indep_to_equality _ _ _ i t i0 H0 H6).
  specialize (H3 i0 i t). *)
  pose proof (indep_to_equality _ _ _ h i0 (t, i) H1 i1).
  (* apply indep_to_equality with (x := i) (y := t) (w := i0) in H0.
  apply indep_to_equality with (x := h) (y := i0) (w := (t, i)) in H1. *)
  (* rewrite H7. *)
  rewrite H7.
  reflexivity.
Qed.

(* Absolutely not proven, and idk if it is proveable. Trying to remove the condition
    where we need the equation to be non-zero at all values. *)
(* Lemma use_indep_statements_get_rid_of_zero: forall h t, 
  Z _|_ T | paT ->
  H _|_ paT | [% T, Z] ->
  \sum_(i in outcomesZ) \sum_(u in outcomesPaT)
      `Pr[ H = h | [% T, Z] = (t, i) ] * `Pr[ Z = i | paT = u ] * `Pr[ paT = u ] = 
  \sum_(i in outcomesZ) \sum_(u in outcomesPaT)
      `Pr[ H = h | [% T, Z, paT] = (t, i, u) ] * `Pr[ Z = i | [% paT, T] = (u, t) ] 
      * `Pr[ paT = u ].
Proof.
  intros.
  apply eq_bigr.
  intros.
  apply eq_bigr.
  intros.
  apply mult_both_sides_r.

  have [Hzero | Hnonzero] := boolP (`Pr[ [% paT, [% T, Z]] = (i0, (t, i)) ] == 0).
      move/eqP: Hzero => Hzero.
      assert (`Pr[ H = h | [% T, Z, paT] = (t, i, i0) ] = 0 ).
        admit.
      rewrite H4.
      rewrite mult_zero_left.
      have [Hzero' | Hnonzero' ] := boolP (`Pr[ paT = i0 ] == 0).
        move/eqP: Hzero' => Hzero'.
        rewrite cpr_eq0_denom; try assumption.
        rewrite mult_zero_right.
        reflexivity.

        assert (`Pr[ [% T, Z] = (t, i) ] = 0).
          unfold cinde_RV in H0.
          specialize (H0 i t i0).

          admit.
        rewrite -> cpr_eq0_denom with (Y := [%T, Z]); try assumption.
        rewrite mult_zero_left.
        reflexivity.
  admit.
Admitted. *)

(* Lemma saying that it the parental adjustment formula, some
    independence statements, and a non-zero statement is true,
    THEN the backdoor adjustment formula holds. 
    Notes: the non-zero condition feels like it could maybe be 
      removed/isn't a great assumption to be making? Could it
      be an artifact of the way we write Hinterv vs H|T? *)
Lemma parental_to_cond: forall t,
  (forall h, `Pr[(Hinterv t) = h] = \sum_(u : outcomesPaT) 
      `Pr[ H = h | [% T, paT] = (t, u)] * `Pr[paT=u]) ->
  T _|_ Z | paT ->
  H _|_ paT | [% T, Z] ->
  (forall u t, `Pr[ T = t | paT = u] != 0) ->
  (forall h, `Pr[(Hinterv t) = h] = \sum_(z : outcomesZ) 
      `Pr[ H = h | [% T, Z] = (t, z)] * `Pr[Z=z]).
Proof. 
  move => t fact ind1 ind2 nonzero h.
  assert (forall z, `Pr[ H = h | [% T, Z] = (t, z) ] * `Pr[ Z = z ] = 
      `Pr[ H = h | [% T, Z] = (t, z) ] * \sum_(u in outcomesPaT) 
      `Pr[ Z = z | paT = u] * `Pr[ paT = u ]).
    intros.
    apply mult_both_sides_l.
    apply marginalize.
  rewrite -> eq_bigr with (F2 := fun z => `Pr[ H = h | [% T, Z] = (t, z) ] *
      (\sum_(u in outcomesPaT) `Pr[ Z = z | paT = u ] * `Pr[ paT = u ])); cycle 1.
    intros.
    specialize (H0 i).
    apply H0.
  assert (\sum_(i in outcomesZ) `Pr[ H = h | [% T, Z] = (t, i) ] * 
      (\sum_(u in outcomesPaT) `Pr[ Z = i | paT = u ] * `Pr[ paT = u ]) =
      \sum_(i in outcomesZ) (\sum_(u in outcomesPaT) 
      `Pr[ H = h | [% T, Z] = (t, i) ] * `Pr[ Z = i | paT = u ] * `Pr[ paT = u ])).
    apply eq_bigr.
    intros.
    rewrite big_distrr.
    simpl.
    apply eq_bigr.
    intros.
    rewrite GRing.mulrA.
    reflexivity.
  rewrite H1.
  rewrite use_indep_statements; cycle 1.
    apply cinde_RV_sym.
    assumption.
    assumption.
    assumption.
  rewrite exchange_big.
  simpl.
  under eq_bigr => i _.
    rewrite -big_distrl.
    simpl.
    under eq_bigr => i0 _.
      rewrite rearrange_cond.
      rewrite rearrange_brackets.
      simpl.
      over.
    simpl.
    rewrite -marginalize_cond.
    over.
  simpl.
  rewrite fact.
  apply eq_bigr => i _.
  apply mult_both_sides_r.
  apply rearrange_cond.
Qed.

(* T _|_ Z | paT
  Z not descendants of T
  parents T = paT 
  --------
  Z no descendant of T -> Z and T d-sep of Z and T have backdoor path through paT
  paT is a mediator of confounder on backdoor path bw Z and T
  backdoor path bw Z and T blocked by paT 
  Z and T d-sep *)

(* H _|_ paT | [% T, Z] 
  Z not descendants of T
  parents T = paT 
  H descendant of T
  --------

  *)

(*  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
                SECTION : Parental Adjustment Formula
    %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%  *)

(* Lemma proving the parental adjustment formula is true, 
    given some starting equation. The starting equation comes
    from Markov factorizations, but we aren't working with 
    Markov factorizations to avoid having to work with paT and
    E as sets. *)
Lemma parental: forall t,
  (forall h pa e,
    `Pr[ [% (Hinterv t), (paTinterv t), (Einterv t)] = (h, pa, e) ] 
        = `Pr[ [% H, T, paT, E] = (h, t, pa, e) ] / `Pr[ T = t | paT = pa ]) ->
  (* (forall i0 i1 i2, `Pr[ [% paT, T, Z] = (i0, i2, i1) ] != 0) -> *)
  (forall i0 i1, `Pr[ [% paT, T] = (i0, i1) ] != 0) ->
  (* (exists z, z \in outcomesZ) -> *)
  (forall h, `Pr[(Hinterv t) = h] = \sum_(u: outcomesPaT) 
      `Pr[ H=h | [% T, paT] = (t, u)] * `Pr[paT=u]).
Proof.
  intros.
  rewrite (total_prob' (Hinterv t) (paTinterv t) h).
  apply eq_bigr => u _.
  rewrite (total_prob' [% Hinterv t, paTinterv t] (Einterv t) (h, u)).
  under eq_bigr => u0 _.
    specialize (H0 h u u0).
    rewrite H0.
    over.
  rewrite -[LHS]big_enum.
  simpl.

  assert (\sum_(i <- enum outcomesE) `Pr[ [% H, T, paT, E] = (h, t, u, i) ] / `Pr[ T = t | paT = u ] =
          (\sum_(i <- enum outcomesE) `Pr[ [% H, T, paT, E] = (h, t, u, i) ]) / `Pr[ T = t | paT = u ]).
    rewrite big_distrl.
    simpl.
    reflexivity.
  rewrite H2.

  rewrite big_enum.
  simpl.

  rewrite cpr_eqE.
  rewrite cpr_eqE.
  rewrite div_div.
  rewrite pfwd1_pairA.
  apply mult_both_sides_r.
  apply div_both_sides.
  rewrite -total_prob'.
  reflexivity.

  specialize (H1 u t).
  rewrite pfwd1_pairC. unfold swap. simpl.
  assumption.
  specialize (H1 u t).
  apply pair_to_single_non_zero_left with (Y := T) (y := t).
  exact H1.
Qed.


(*  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
                  SECTION : Putting it together
    %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%  *)

(* Given Markov factorization equation,
        independence statements,
        non-zero statment,
    THEN the backdoor adjustment formula is true. *)
Lemma graphfactor_indp_backdoor_adj: forall t,
  (forall h pa e,
  `Pr[ [% (Hinterv t), (paTinterv t), (Einterv t)] = (h, pa, e) ] 
      = `Pr[ [% H, T, paT, E] = (h, t, pa, e) ] / `Pr[ T = t | paT = pa ]) ->
  T _|_ Z | paT ->
  H _|_ paT | [% T, Z] ->
  (forall u t, `Pr[ T = t | paT = u] != 0) ->
  (forall h, `Pr[(Hinterv t) = h] = \sum_(z: outcomesZ) 
      `Pr[ H = h | [% T, Z] = (t, z)] * `Pr[Z=z]).
Proof.
  intros.
  apply parental_to_cond; try assumption.
  apply parental; try assumption.
  intros.
  rewrite pfwd1_pairC.
  unfold swap. simpl.
  apply cond_to_pair_non_zero.
  specialize (H3 i0 i1).
  assumption.
Qed.

Print Assumptions graphfactor_indp_backdoor_adj.

(* Note: move for all h in *)
(* (paTinterv t) = paT *)
(* (Zinterv t) = Z *)
(* paT = [% paT1, paT2, paT3, ..., paTn ] *)

End ParentalAdjustmentFormula.










(*  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
                  SECTION : Testing Examples
    %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%  *)


Section FourVarConfounderExample.
(* Graph :  C <- E -> H
            T <- C -> H
               T -> H *)

(* Graph:           E
                   / |
                  C  |
                 / \ v
                T--->H*)

(* T=t, H=h, paT = C, E = CE Z = C *)


Context {R : realType}.

Variables (UT UH UC UE : finType).
Variable P : R.-fdist (((UE * UC) * UT) * UH).
Variable outcomesT: finType.
Variable outcomesH: finType.
Variable outcomesC: finType.
Variable outcomesE: finType.

Variable fE : UE -> outcomesE.
Variable fC : UC -> outcomesE -> outcomesC.
Variable fT : UT -> outcomesC -> outcomesT.
Variable fH : UH -> outcomesE -> outcomesC -> outcomesT -> outcomesH.

Let E : {RV P -> outcomesE} :=
  fun p => fE p.1.1.1.
Let C : {RV P -> outcomesC} :=
  fun p => fC p.1.1.2 (E p).
Let T : {RV P -> outcomesT} :=
  fun p => fT p.1.2 (C p).
Let H : {RV P -> outcomesH} :=
  fun p => fH p.2 (E p) (C p) (T p).

Let Tinterv (t: outcomesT) : {RV P -> outcomesT} :=
  fun p => t.
Let Einterv (t: outcomesT) : {RV P -> outcomesE} :=
  fun p => fE p.1.1.1.
Let Cinterv (t: outcomesT) : {RV P -> outcomesC} :=
  fun p => fC p.1.1.2 (Einterv t p).
Let Hinterv (t: outcomesT) : {RV P -> outcomesH}:= 
  fun p => fH p.2 (Einterv t p) (Cinterv t p) t.

Let UTRV: {RV P -> UT} :=
  fun u => u.1.2.
Let UHRV: {RV P -> UH} :=
  fun u => u.2.
Let UCRV: {RV P -> UC} :=
  fun u => u.1.1.2.
Let UERV: {RV P -> UE} :=
  fun u => u.1.1.1.

Definition mutual_indep_three {X' Y' Z': finType}
  (X : {RV P -> X'}) (Y : {RV P -> Y'}) (Z: {RV P -> Z'}) := 
  (forall x y z,
  `Pr[ X = x ] * `Pr[ Y = y ] * `Pr[ Z = z ] 
    = `Pr[ [%[% X, Y], Z] = ((x,y), z)]) /\ 
    P |= X _|_ Y /\ P |= Y _|_ Z /\ P |= X _|_ Z.

Definition mutual_indep_four {W' X' Y' Z': finType}
  (W : {RV P -> W'}) (X : {RV P -> X'}) (Y : {RV P -> Y'}) (Z: {RV P -> Z'}) := 
  (forall w x y z,
  `Pr[ W = w ] * `Pr[ X = x ] * `Pr[ Y = y ] * `Pr[ Z = z ] 
    = `Pr[ [% [% [% W, X], Y], Z] = (((w,x),y),z)]) /\ 
  mutual_indep_three W X Y /\
  mutual_indep_three W X Z /\
  mutual_indep_three W Y Z /\
  mutual_indep_three X Y Z.

Lemma mult_one_right: forall (a : R),
  a * 1 = a.
Proof.
  apply GRing.mulr1.
Qed.

Lemma zero_div_zero': forall (a : R),
  a != 0 ->
  0 / a = 0.
Proof.
Admitted.

Lemma a_div_a_is_one: forall (a : R),
  a != 0 ->
  a / a = 1.
Proof.
Admitted.

Lemma pfwd1_diag_ext (U U': eqType) 
  (X : {RV P -> U}) (Y: {RV P -> U'}) (x : U) (y : U') : 
  `Pr[ [% Y, X, X] = (y, x, x) ] = `Pr[ [% Y, X] = (y, x) ].
Proof.
  rewrite pfwd1E.
  rewrite pfwd1E.
  rewrite /Pr.
  apply eq_bigl => a.
  rewrite !inE.
  rewrite !xpair_eqE.
  case Hx : (X a == x).
    case Hy : (Y a == y).
      simpl.
      reflexivity.
      simpl.
      reflexivity.
      rewrite !andbF.
      reflexivity.
(* by rewrite !pfwd1E /Pr; apply: eq_bigl=> a; rewrite !inE xpair_eqE andbb. *)
Qed.

Lemma if_one_is_true_the_other_isnt: forall {X': finType} 
  (X : {RV P -> X'}) b c a,
  b != c ->
  (X a == b) = true ->
  (X a == c) = false.
Proof.
  intros.
  by rewrite (eqP H1); exact/negbTE.
Qed.

Lemma pfwd1_diag_not_xx: forall {X': finType} (X : {RV P -> X'}) b c,
  b != c ->
  `Pr[ [% X, X] = (b, c) ] = 0.
Proof.
  intros.
  rewrite !pfwd1E /Pr.
  under eq_bigl => a.
  rewrite !inE.
  rewrite !xpair_eqE.
  case Hx : (X a == b).
    assert ((X a == c) = false). eapply if_one_is_true_the_other_isnt.
      exact H0.
      exact Hx. 
    rewrite H1.
    simpl.
    over.

    simpl.
    over.

    simpl.
    apply big_pred0_eq.
Qed.

Lemma pfwd1_diag_not: forall {X' Y' : finType} (X : {RV P -> X'}) 
  (Y : {RV P -> Y'}) b c y,
  b != c ->
  `Pr[ [% Y, X, X] = (y, b, c) ] = 0.
Proof.
  intros.
  rewrite !pfwd1E /Pr.
  under eq_bigl => a.
  rewrite !inE.
  rewrite !xpair_eqE.
  case Hx : (X a == b).
    assert ((X a == c) = false). eapply if_one_is_true_the_other_isnt.
      exact H0.
      exact Hx. 
    rewrite H1.
    rewrite andbF.
    over.

    rewrite andbF.
    simpl.
    over.

    simpl.
    apply big_pred0_eq.
Qed.

Lemma var_cond_diff_zero: forall {X': finType} (X : {RV P -> X'}) b c,
  b != c ->
  `Pr[ X = b | X = c ] = 0.
Proof.
  intros.
  case: (boolP (`Pr[ X = c ] == 0)).
    intros.
    move /eqP in p.
    apply cpr_eq0_denom.
    assumption.

  intros.
  rewrite cpr_eqE.
  rewrite pfwd1_diag_not_xx; try assumption.
  rewrite zero_div_zero'.
  reflexivity.
  assumption.
Qed.

Lemma var_cond_diff_zero_gen: forall {X' Y': finType} (X : {RV P -> X'}) 
  (Y : {RV P -> Y'}) b c y,
  b != c ->
  `Pr[ [% Y, X] = (y, b) | X = c ] = 0.
Proof.
  intros.
  case: (boolP (`Pr[ X = c ] == 0)).
    intros.
    move /eqP in p.
    apply cpr_eq0_denom.
    assumption.

  intros.
  rewrite cpr_eqE.
  rewrite pfwd1_diag_not; try assumption.
  rewrite zero_div_zero'.
  reflexivity.
  assumption.
Qed.

Lemma var_cond_diff_zero_gen2: forall {X' Y' W': finType} (X : {RV P -> X'}) 
  (Y : {RV P -> Y'}) (W : {RV P -> W'}) b c w y,
  b != c ->
  `Pr[ [% Y, X] = (y, b) | [% W, X] = (w, c) ] = 0.
Proof.
  intros.
  case: (boolP (`Pr[ [% W, X] = (w, c) ] == 0)).
    intros.
    move /eqP in p.
    apply cpr_eq0_denom.
    assumption.

  intros.
  rewrite cpr_eqE.
  rewrite pfwd1_pairCA.
  assert (`Pr[ [% W, [% Y, X, X]] = (w, (y, b, c)) ]
      = `Pr[ [% W, Y, X, X] = (w, y, b, c) ]).
    rewrite !pfwd1E /Pr.
    apply: eq_bigl=> a0.
    rewrite !inE.
    rewrite !xpair_eqE.
    case Hb : (X a0 == b).
      assert ((X a0 == c) = false). eapply if_one_is_true_the_other_isnt.
        exact H0.
        exact Hb. 
      rewrite H1.
      rewrite !andbF.
      reflexivity.
      rewrite !andbF.
      simpl.
      reflexivity.
  rewrite H1.
  rewrite pfwd1_diag_not; try assumption.
  rewrite zero_div_zero'.
  reflexivity.
  assumption.
Qed.

Lemma var_cond_diff_zero_gen3: forall {X' Y': finType} (X : {RV P -> X'}) 
  (Y : {RV P -> Y'}) b c y,
  b != c ->
  `Pr[ X = b | [% Y, X] = (y, c) ] = 0.
Proof.
  intros.
  case: (boolP (`Pr[ [% Y, X] = (y, c) ] == 0)).
    intros.
    move /eqP in p.
    apply cpr_eq0_denom.
    assumption.

  intros.
  rewrite cpr_eqE.
  rewrite pfwd1_pairCA.
  rewrite pfwd1_pairA.
  rewrite pfwd1_diag_not; try assumption.
  rewrite zero_div_zero'.
  reflexivity.
  assumption.
Qed.

Lemma extra_indentical_factor: forall t c,
  `Pr[ [% T, C] = (t, c) | C = c] = `Pr[ T = t | C = c].
Proof.
  intros.
  rewrite cpr_eqE.
  rewrite pfwd1_diag_ext.
  rewrite <- cpr_eqE.
  reflexivity.
Qed.

Lemma var_in_cond_true: forall {X' Y': finType} (X : {RV P -> X'}) 
  (Y : {RV P -> Y'}) x y,
  `Pr[ [% Y, X] = (y, x) ] != 0 ->
  `Pr[ X = x | [% Y, X] = (y, x) ] = 1.
Proof.
  intros.
  rewrite cpr_eqE.
  rewrite pfwd1_pairCA.
  rewrite pfwd1_pairA.
  rewrite pfwd1_diag_ext.
  rewrite a_div_a_is_one.
  reflexivity.
  assumption.
Qed.

(* Lemma extra_identical_factor_general: forall {X' Y' W': finType} 
  (X : {RV P -> X'}) (Y : {RV P -> Y'}) (W : {RV P -> W'}) w x a b,
  b != c ->
  `Pr[ [% Y, X] = (y, b) | X = c ] = 0.
  `Pr[ [% T, C] = (t, c) | C = c] = `Pr[ T = t | C = c]. *)

Lemma fvc_indep1:
  (* mutual_indep_four E C T H -> *)
  (forall c t, `Pr[ [% C, T] = (c, t) ] != 0) ->
  T _|_ C | C.
Proof.
  intros.
  unfold cinde_RV.
  intros.
  have [Hc | Hc'] := boolP (b == c).
    move/eqP: Hc => Hc.
    rewrite Hc.
    rewrite cPr_eq_id.
    rewrite extra_indentical_factor.
    rewrite mult_one_right.
    reflexivity.
  
    specialize (H0 c a).
    apply pair_to_single_non_zero in H0; eauto.
    (* apply pair_to_single_non_zero with (outcomesH := outcomesH)
        (outcomesT := outcomesT) (outcomesPaT := outcomesH) 
        (outcomesZ := outcomesH) (outcomesE := outcomesH) in H0; try eauto. *)

  rewrite var_cond_diff_zero; try assumption.
  rewrite mult_zero_right.
  rewrite var_cond_diff_zero_gen; try assumption.
  reflexivity.
Qed.

Lemma fvc_indep2:
  (* mutual_indep_four E C T H -> *)
  H _|_ C | [% T, C].
Proof.
  intros.
  unfold cinde_RV.
  intros.
  destruct c as [t c].
  case (boolP (b == c)).
    intros.
    move /eqP in i.
    inversion i.
    (* pose proof (remove_redundant_cond_term). *)
    rewrite -> remove_redundant_cond_term; eauto.
    (* rewrite -> remove_redundant_cond_term with (outcomesH := outcomesH)
        (outcomesT := outcomesT) (outcomesPaT := outcomesC) 
        (outcomesZ := outcomesC) (outcomesE := outcomesE); try eauto. *)
    case (boolP (`Pr[ [% T, C] = (t, c) ] == 0)).
      intros.
      move /eqP in i0.
      rewrite !cpr_eq0_denom; try assumption.
      rewrite GRing.mul0r.
      reflexivity.
    intros.
    rewrite var_in_cond_true.
    rewrite mult_one_right.
    reflexivity.
    assumption.
    
  intros.
  rewrite -> cond_term_makes_impossible; eauto.
  (* rewrite -> cond_term_makes_impossible with (outcomesH := outcomesH)
        (outcomesT := outcomesT) (outcomesPaT := outcomesC) 
        (outcomesZ := outcomesC) (outcomesE := outcomesE); try eauto. *)
  rewrite -> var_cond_diff_zero_gen3; try assumption.
  rewrite GRing.mulr0.
  reflexivity.
Qed.

(* Lemma extra_factor_in_nonzero:
  (forall i0 i2, `Pr[ [% C, T] = (i0, i2) ] != 0) ->
  (forall i0 i1 i2, `Pr[ [% C, T, C] = (i0, i2, i1) ] != 0).
Proof.
Admitted. *)

Lemma four_var_confounder_backdoor_adjustment: forall t,
  (forall h c e,
  `Pr[ [% (Hinterv t), (Cinterv t), (Einterv t)] = (h, c, e) ] 
      = `Pr[ [% H, T, C, E] = (h, t, c, e) ] / `Pr[ T = t | C = c ]) ->
  mutual_indep_four UERV UCRV UTRV UHRV ->
  (forall u t, `Pr[ T = t | C = u ] != 0) ->
  (forall h, `Pr[(Hinterv t) = h] = \sum_(c : outcomesC) 
      `Pr[ H = h | [% T, C] = (t, c)] * `Pr[C = c]).
Proof.
  intros.
  (* pose proof (fvc_indep1 H1).
  pose proof (fvc_indep2 H1).
  pose proof (extra_factor_in_nonzero H2). *)
  eapply graphfactor_indp_backdoor_adj with (paT := C) 
    (paTinterv := Cinterv) (Einterv := Einterv) (E := E); try assumption.
  info_eauto.
  apply fvc_indep1; try assumption.
  intros.
  specialize (H2 c t0).
  rewrite pfwd1_pairC. unfold swap. simpl.
  apply cond_to_pair_non_zero; eauto.
  (* apply cond_to_pair_non_zero with (outcomesH := outcomesH) 
      (outcomesZ := outcomesC) (outcomesE := outcomesE); eauto. *)
  apply fvc_indep2; try assumption.
  (* apply extra_factor_in_nonzero; try assumption. *)
Qed.

Lemma factorhold_four_var_helper_helper: forall t,
  [% (Hinterv t), E] _|_ T | C ->
  forall h e c, `Pr[ [% (Hinterv t), E] = (h, e) | [% T, C] = (t, c)] = 
  `Pr[ [% (Hinterv t), E] = (h, e) | C = c].
Proof.
Admitted.

Lemma factorhold_four_var_helper_helper': forall t, 
  mutual_indep_four UERV UCRV UTRV UHRV ->
   [% (Hinterv t), E] _|_ T | C.
Proof.
  intros.
  unfold cinde_RV.
  intros.

Admitted.

(* Lemma factorhold_four_var_helper_helper'': forall t, 
  mutual_indep_four UERV UCRV UTRV UHRV ->
  [% UCRV, UERV,] *)

Lemma factorhold_four_var_helper: forall t,
  mutual_indep_four UERV UCRV UTRV UHRV ->
  (forall h c e,
  `Pr[ [% (Hinterv t), (Einterv t)] = (h, e) | (Cinterv t) = c] 
      = `Pr[ [% H, E] = (h, e) | [% T, C] = (t, c)]).
Proof.
  intros.
  change (Cinterv t) with C.
  change (Einterv t) with E.
  rewrite !cPr_eq_def /Pr.
  (* rewrite cPr_eq_def.
  rewrite /Pr.
  apply: eq_bigl=> a0.
  rewrite !inE.
  rewrite !xpair_eqE.
  case Hx : (X a0 == x).
    case Hv : (V a0 == v).
      case Hy : (Y a0 == y).
        case Hw : (W a0 == w).
        simpl.
        reflexivity.

        simpl.
        reflexivity.

        simpl.
        rewrite !andbF.
        reflexivity.

        simpl.
        rewrite !andbF.
        reflexivity.

        simpl.
        rewrite !andbF.
        reflexivity. *)

Admitted.

Lemma factorhold_four_var: forall t,
  mutual_indep_four UERV UCRV UTRV UHRV ->
  (forall h c e,
  `Pr[ [% (Hinterv t), (Cinterv t), (Einterv t)] = (h, c, e) ] 
      = `Pr[ [% H, T, C, E] = (h, t, c, e) ] / `Pr[ T = t | C = c ]).
Proof.
  intros. 
Admitted.

(* Print Assumptions four_var_confounder_backdoor_adjustment. *)

End FourVarConfounderExample.


Section LargeExample.
Context {R : realType}.

Variables (UT UH UC UE UQ UD UF UG : finType).
Variable P : R.-fdist (((((((UG * UQ) * UD) * UF ) * UE) * UC) * UT) * UH).
Variable outcomesT: finType.
Variable outcomesH: finType.
Variable outcomesC: finType.
Variable outcomesE: finType.
Variable outcomesQ: finType.
Variable outcomesD: finType.
Variable outcomesF: finType.
Variable outcomesG: finType.

Variable fE : UE -> outcomesE.
Variable fC : UC -> outcomesE -> outcomesC.
Variable fQ : UQ -> outcomesQ.
Variable fF : UF -> outcomesF.
Variable fD : UD -> outcomesF -> outcomesD.
Variable fT : UT -> outcomesC -> outcomesQ -> outcomesD -> outcomesT.
Variable fH : UH -> outcomesE -> outcomesC -> outcomesF -> outcomesT -> outcomesH.
Variable fG : UG -> outcomesH -> outcomesT -> outcomesG.

Let E : {RV P -> outcomesE} :=
  fun p => fE p.1.1.1.2.
Let C : {RV P -> outcomesC} :=
  fun p => fC p.1.1.2 (E p).
Let Q: {RV P -> outcomesQ} :=
  fun p => fQ p.1.1.1.1.1.1.2.
Let F: {RV P -> outcomesF} :=
  fun p => fF p.1.1.1.1.2.
Let D: {RV P -> outcomesD} :=
  fun p => fD p.1.1.1.1.1.2 (F p).
Let T : {RV P -> outcomesT} :=
  fun p => fT p.1.2 (C p) (Q p) (D p).
Let H : {RV P -> outcomesH} :=
  fun p => fH p.2 (E p) (C p) (F p) (T p).
Let G : {RV P -> outcomesG} :=
  fun p => fG p.1.1.1.1.1.1.1 (H p) (T p).

Let Tinterv (t: outcomesT) : {RV P -> outcomesT} :=
  fun p => t.
Let Einterv (t: outcomesT) : {RV P -> outcomesE} :=
  fun p => fE p.1.1.1.2.
Let Cinterv (t: outcomesT) : {RV P -> outcomesC} :=
  fun p => fC p.1.1.2 (Einterv t p).
Let Qinterv (t: outcomesT) : {RV P -> outcomesQ} :=
  fun p => fQ p.1.1.1.1.1.1.2.
Let Finterv (t: outcomesT) : {RV P -> outcomesF} :=
  fun p => fF p.1.1.1.1.2.
Let Dinterv (t: outcomesT) : {RV P -> outcomesD} :=
  fun p => fD p.1.1.1.1.1.2 (F p).
Let Hinterv (t: outcomesT) : {RV P -> outcomesH}:= 
  fun p => fH p.2 (Einterv t p) (Cinterv t p) (Finterv t p) t.
Let Ginterv (t: outcomesT) : {RV P -> outcomesG} :=
  fun p => fG p.1.1.1.1.1.1.1 (Hinterv t p) t.

Let UTRV: {RV P -> UT} :=
  fun u => u.1.2.
Let UHRV: {RV P -> UH} :=
  fun u => u.2.
Let UCRV: {RV P -> UC} :=
  fun u => u.1.1.2.
Let UERV: {RV P -> UE} :=
  fun u => u.1.1.1.2.
Let UFRV: {RV P -> UF} := 
  fun u => u.1.1.1.1.2.
Let UDRV: {RV P -> UD} :=
  fun u => u.1.1.1.1.1.2.
Let UQRV: {RV P -> UQ} :=
  fun u => u.1.1.1.1.1.1.2.
Let UGRV: {RV P -> UG} :=
  fun u => u.1.1.1.1.1.1.1.

(*  H = H
    T = T
    paT = [% C, D, Q ]
    E = [% E, F]
    Z = [% C, F]
*)

Lemma eight_var_confounder_backdoor_adjustment: forall t,
  (forall h pa e,
  `Pr[ [% (Hinterv t), [% (Cinterv t), (Dinterv t), (Qinterv t)], 
      [% (Einterv t), (Finterv t) ]] = (h, pa, e) ] 
      = `Pr[ [% H, T, [% C, D, Q] , [% E, F]] = (h, t, pa , e ) ] 
        / `Pr[ T = t | [% C, D, Q] = pa ]) ->
  T _|_ [% C, F] | [% C, D, Q] ->
  H _|_ [% C, D, Q] | [% T, [% C, F]] ->
  (forall pa t, `Pr[ T = t | [% C, D, Q] = pa ] != 0) ->
  (* true. *)
  (forall h, `Pr[(Hinterv t) = h] = \sum_(cf : outcomesC * outcomesF) 
      `Pr[ H = h | [% T, [% C, F] ] = (t, cf)] * `Pr[[% C, F] = cf]).
Proof.
  intros.
  apply graphfactor_indp_backdoor_adj with 
      (outcomesPaT := (outcomesC*outcomesD*outcomesQ)%type)
      (outcomesE := (outcomesE*outcomesF)%type)
      (paT := [% C, D, Q]) (E := [% E, F])
      (paTinterv := (fun t => [% (Cinterv t), (Dinterv t), (Qinterv t)]))
      (Einterv := (fun t => [% (Einterv t), (Finterv t)])); eauto. 
  (* exact (fun t => [% (Cinterv t), (Finterv t)]). *)
Qed.

Lemma can_swap_indep_cond_order: forall  {A B C D : finType} (X : {RV P -> A}) (Y : {RV P -> B})
  (W : {RV P -> C}) (V : {RV P -> D}),
  X _|_ Y | [% W, V] ->
  X _|_ Y | [% V, W].
Proof.
Admitted.

Lemma adding_brackets_in_indep: forall  {A B C D A' : finType} (X : {RV P -> A}) (Y : {RV P -> B})
  (W : {RV P -> C}) (V : {RV P -> D}) (Z' : {RV P -> A'}),
  Z' _|_ V | [% W, X, Y] ->
  Z' _|_ V | [% W, [% X, Y]].
Proof.
  intros.
  unfold cinde_RV.
  unfold cinde_RV in H0.
  intros.
  destruct c as [w [x y]].
  specialize (H0 a b (w, x, y)).
Admitted.

Lemma eight_var_confounder_backdoor_adjustment_weaker_indp: forall t,
  (forall h pa e,
  `Pr[ [% (Hinterv t), [% (Cinterv t), (Dinterv t), (Qinterv t)], 
      [% (Einterv t), (Finterv t) ]] = (h, pa, e) ] 
      = `Pr[ [% H, T, [% C, D, Q] , [% E, F]] = (h, t, pa , e ) ] 
        / `Pr[ T = t | [% C, D, Q] = pa ]) ->
  T _|_ F | [% C, D, Q] ->
  H _|_ [% D, Q] | [% T, [% C, F]] ->
  (forall pa t, `Pr[ T = t | [% C, D, Q] = pa ] != 0) ->
  (* true. *)
  (forall h, `Pr[(Hinterv t) = h] = \sum_(cf : outcomesC * outcomesF) 
      `Pr[ H = h | [% T, [% C, F] ] = (t, cf)] * `Pr[[% C, F] = cf]).
Proof.
  intros.
  apply eight_var_confounder_backdoor_adjustment; try assumption.
  (* apply can_swap_indep_cond_order in H1. *)
  apply adding_brackets_in_indep in H1.
  pose proof (can_swap_indep_cond_order T F C [% D, Q] H1).
  (* apply adding_conditional_to_indep in H4. *)

  (* pose proof (adding_conditional_to_indep T F C [% D, Q]). *)
  unfold cinde_RV in H4. 
  apply adding_conditional_to_indep in H4.
  (* apply adding_conditional_to_indep with (outcomesH := outcomesH)
      (outcomesT := outcomesT) (outcomesPaT := outcomesH) (outcomesZ := outcomesH)
      (outcomesE := outcomesH) in H4; eauto. *)
  admit.
Admitted.
  

End LargeExample.
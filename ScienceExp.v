From mathcomp Require Import ssreflect ssrfun ssrbool eqtype fintype bigop.
Require Import Reals.
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
From project Require Import TwoVarThreeVarExamples.
From project Require Import GeneralParentalAdj.

Local Open Scope ring_scope.
Local Open Scope reals_ext_scope.
Local Open Scope fdist_scope.
Local Open Scope proba_scope.

Section SNSGPA.
Context {R : realType}.

Variables (UT UH UA UN UD UE UC UO : finType).
Variable P : R.-fdist (((UO * UD * UA * UN * UE * UC) * UT) * UH).
Variables ocT ocH ocD ocA ocN ocE ocC ocO : finType.

Let UTRV: {RV P -> UT} :=
  fun u => u.1.2.
Let UHRV: {RV P -> UH} :=
  fun u => u.2.
Let UCRV: {RV P -> UC} :=
  fun u => u.1.1.2.
Let UERV: {RV P -> UE} :=
  fun u => u.1.1.1.2.
Let UNRV: {RV P -> UN} := 
  fun u => u.1.1.1.1.2.
Let UARV: {RV P -> UA} :=
  fun u => u.1.1.1.1.1.2.
Let UDRV: {RV P -> UD} :=
  fun u => u.1.1.1.1.1.1.2.
Let UORV: {RV P -> UO} :=
  fun u => u.1.1.1.1.1.1.1.

Variable fD : UD -> ocD.
Variable fA : UA -> ocD -> ocA.
Variable fN : UN -> ocD -> ocN.
Variable fE : UE -> ocD -> ocE.
Variable fC : UC -> ocD -> ocE -> ocC.
Variable fO : UO -> ocD -> ocE -> ocC -> ocO.
Variable fT : UT -> ocD -> ocE -> ocC -> ocT.
Variable fH : UH -> ocD -> ocE -> ocC -> ocA -> ocN -> ocO -> ocT -> ocH.

Let D : {RV P -> ocD} :=
  fun p => fD (UDRV p).
Let A : {RV P -> ocA} :=
  fun p => fA (UARV p) (D p).
Let N: {RV P -> ocN} :=
  fun p => fN (UNRV p) (D p).
Let E: {RV P -> ocE} :=
  fun p => fE (UERV p) (D p).
Let C: {RV P -> ocC} :=
  fun p => fC (UCRV p) (D p) (E p).
Let Ot: {RV P -> ocO} :=
  fun p => fO (UORV p) (D p) (E p) (C p).
Let T : {RV P -> ocT} :=
  fun p => fT (UTRV p) (D p) (E p) (C p).
Let H : {RV P -> ocH} :=
  fun p => fH (UHRV p) (D p) (E p) (C p) (A p) (N p) (Ot p) (T p).

Let Tinterv (t: ocT) : {RV P -> ocT} :=
  fun p => t.
Let Dinterv (t: ocT) : {RV P -> ocD} :=
  fun p => fD (UDRV p).
Let Ainterv (t: ocT) : {RV P -> ocA} :=
  fun p => fA (UARV p) (Dinterv t p).
Let Ninterv (t: ocT) : {RV P -> ocN} :=
  fun p => fN (UNRV p) (Dinterv t p).
Let Einterv (t: ocT) : {RV P -> ocE} :=
  fun p => fE (UERV p) (Dinterv t p).
Let Cinterv (t: ocT) : {RV P -> ocC} :=
  fun p => fC (UCRV p) (Dinterv t p) (Einterv t p).
Let Ointerv (t: ocT) : {RV P -> ocO} :=
  fun p => fO (UORV p) (Dinterv t p) (Einterv t p) (Cinterv t p).
Let Hinterv (t: ocT) : {RV P -> ocH}:= 
  fun p => fH (UHRV p) (Dinterv t p) (Einterv t p) (Cinterv t p) 
      (Ainterv t p) (Ninterv t p) (Ointerv t p) t.

Lemma backdoor_adj_snsgpa : forall t,
  (forall h pa e,
  `Pr[ [% (Hinterv t), [% (Cinterv t), (Dinterv t), (Einterv t)], 
      [% (Ainterv t), (Ninterv t), (Ointerv t) ]] = (h, pa, e) ] 
      = `Pr[ [% H, T, [% C, D, E] , [% A, N, Ot]] = (h, t, pa, e) ] 
        / `Pr[ T = t | [% C, D, E] = pa ]) ->
  (forall pa t, `Pr[ T = t | [% C, D, E] = pa ] != 0) ->
  (forall h, `Pr[(Hinterv t) = h] = \sum_(cde : ocC * ocD * ocE) 
      `Pr[ H = h | [% T, [% C, D, E] ] = (t, cde)] * `Pr[[% C, D, E] = cde]).
Proof.
  move => t factor nonneg.
  (* apply parental. *)
  apply parental with (E := [% A, N, Ot ])
      (Einterv := (fun t => [% (Ainterv t), (Ninterv t), (Ointerv t) ])) 
      (paTinterv := (fun t => [% (Cinterv t), (Dinterv t), (Einterv t)])).
  assumption.
  intros.
  rewrite pfwd1_pairC.
  apply cond_to_pair_non_zero.
  simpl.
  specialize (nonneg i0 i1).
  assumption.
Qed.

End SNSGPA.








Section alcohol.
Context {R : realType}.

Variables (UT UH UD UM UP UF : finType).
Variable P : R.-fdist (((UD * UM * UP * UF) * UT) * UH).
Variables ocT ocH ocD ocM ocP ocF : finType.

Let UTRV: {RV P -> UT} :=
  fun u => u.1.2.
Let UHRV: {RV P -> UH} :=
  fun u => u.2.
Let UFRV: {RV P -> UF} :=
  fun u => u.1.1.2.
Let UPRV: {RV P -> UP} :=
  fun u => u.1.1.1.2.
Let UMRV: {RV P -> UM} := 
  fun u => u.1.1.1.1.2.
Let UDRV: {RV P -> UD} :=
  fun u => u.1.1.1.1.1.

Variable fD : UD -> ocD.
Variable fP : UP -> ocD -> ocP.
Variable fM : UM -> ocD -> ocP -> ocM.
Variable fT : UT -> ocD -> ocP -> ocM -> ocT.
Variable fF : UF -> ocD -> ocT -> ocF.
Variable fH : UH -> ocD -> ocP -> ocF -> ocT -> ocH.

Let D : {RV P -> ocD} :=
  fun p => fD (UDRV p).
Let Pa : {RV P -> ocP} :=
  fun p => fP (UPRV p) (D p).
Let M: {RV P -> ocM} :=
  fun p => fM (UMRV p) (D p) (Pa p).
Let T: {RV P -> ocT} :=
  fun p => fT (UTRV p) (D p) (Pa p) (M p).
Let F : {RV P -> ocF} :=
  fun p => fF (UFRV p) (D p) (T p).
Let H : {RV P -> ocH} :=
  fun p => fH (UHRV p) (D p) (Pa p) (F p) (T p).

Let Tinterv (t: ocT) : {RV P -> ocT} :=
  fun p => t.
Let Dinterv (t: ocT) : {RV P -> ocD} :=
  fun p => fD (UDRV p).
Let Pinterv (t: ocT) : {RV P -> ocP} :=
  fun p => fP (UPRV p) (Dinterv t p).
Let Minterv (t: ocT) : {RV P -> ocM} :=
  fun p => fM (UMRV p) (Dinterv t p) (Pinterv t p).
Let Finterv (t: ocT) : {RV P -> ocF} :=
  fun p => fF (UFRV p) (Dinterv t p) t.
Let Hinterv (t: ocT) : {RV P -> ocH}:= 
  fun p => fH (UHRV p) (Dinterv t p) (Pinterv t p) (Finterv t p) t.

Definition mutual_indep_three' {TU X' Y' Z': finType} {P' : R.-fdist(TU)}
  (X : {RV P' -> X'}) (Y : {RV P' -> Y'}) (Z: {RV P' -> Z'}) := 
  (forall x y z,
  `Pr[ X = x ] * `Pr[ Y = y ] * `Pr[ Z = z ] 
    = `Pr[ [%[% X, Y], Z] = ((x,y), z)]) /\ 
    P' |= X _|_ Y /\ P' |= Y _|_ Z /\ P' |= X _|_ Z.

Lemma a_div_b_eq_one : forall (a b : R),
  a = b ->
  a != 0 ->
  a / b = 1.
Proof.
  intros.
  rewrite H0.
  apply GRing.divff.
  rewrite H0 in H1.
  assumption.
Qed.

Lemma extend_non_zero : forall  {B' D' : finType} 
  (Y' : {RV P -> B'}) (V' : {RV P -> D'}) y v,
  `Pr[ [% Y', V'] = (y, v) ] != 0 ->
  `Pr[ [% V', [% Y', V']] = (v, (y, v)) ] != 0.
Proof.
  intros.
  assert (`Pr[ [% Y', V'] = (y, v) ] = `Pr[ [% V', [% Y', V']] = (v, (y, v)) ]).
    intros.
    rewrite !pfwd1E /Pr.
    apply: eq_bigl=> a0.
    rewrite !inE.
    rewrite !xpair_eqE.
    case Hy : (Y' a0 == y).
    case Hv : (V' a0 == v).
      all: simpl; try rewrite andbF; try reflexivity.
  rewrite -H1.
  assumption.
Qed.

Lemma remove_redundant_cond_term_to_one : forall  {B' D' : finType} 
  (Y' : {RV P -> B'}) (V' : {RV P -> D'}) y v,
  `Pr[ [% Y', V'] = (y, v) ] != 0 ->
  `Pr[ V' = v | [% Y', V'] = (y, v)] = 1.
Proof.
  intros.
  rewrite cpr_eqE.
  apply a_div_b_eq_one.

  rewrite !pfwd1E /Pr.
  apply: eq_bigl=> a0.
  rewrite !inE.
  rewrite !xpair_eqE.
  case Hv : (V' a0 == v).
    case Hy : (Y' a0 == y).
      simpl.
      reflexivity.

      simpl.
      reflexivity.

      simpl.
      rewrite andbF.
      reflexivity.
  
  apply extend_non_zero.
  assumption.
Qed.

Lemma cond_term_makes_impossible_smaller_num: forall  {B D : finType} 
  (Y : {RV P -> B}) (V : {RV P -> D}) y v1 v2,
  v1 != v2 ->
  `Pr[ V = v1 | [% Y, V] = (y, v2)] = 0.
Proof.
  intros.
  have [Hz | Hnz ] := ( boolP (`Pr[ [% Y, V] = (y, v2) ] == 0)).
    intros.
    move /eqP in Hz.
    rewrite cpr_eq0_denom; try assumption. 
    reflexivity.

  rewrite cpr_eqE.
  assert (`Pr[ [% V, [% Y, V]] = (v1, (y, v2)) ] = 0).
  rewrite pfwd1E.
  rewrite /Pr.
  under eq_bigl => a.
  rewrite !inE.
  rewrite !xpair_eqE.
  case Hv1 : (V a == v1).
    assert ((V a == v2) = false).
      by rewrite (eqP Hv1); exact/negbTE.
    rewrite H1.
    rewrite andbF.
    rewrite andbF.
    over.
    
    simpl.
    over.
  
    simpl.
    apply big_pred0_eq.
  
  rewrite H1.
  apply zero_div_zero.
  assumption.
Qed.

Lemma alc_indep1_helper :
  (forall pa t, `Pr[ T = t | [% D, M, Pa] = pa ] != 0) ->
  T _|_ [% D, Pa] | [% M, [% D, Pa]].
Proof.
  move => nonneg.
  unfold cinde_RV.
  intros.
  destruct c as [m b2].
  have [Heq | Hneq ] := (boolP (b == b2)).
  intros.
  move /eqP in Heq.
  rewrite <- Heq.
  rewrite remove_redundant_cond_term.
  rewrite remove_redundant_cond_term_to_one.
  rewrite mult_one_right.
  reflexivity.
  destruct b as [d p].
  specialize (nonneg (d, m, p) a).
  (* Check cond_to_pair_non_zero. *)
  pose proof (cond_to_pair_non_zero _ P a (d, m, p) nonneg).
  apply pair_to_single_non_zero_right in H0.
  rewrite pfwd1_pairAC in H0.
  rewrite pfwd1_pairC in H0.
  unfold swap in H0. 
  simpl in H0.
  assumption.

  rewrite cond_term_makes_impossible.
  rewrite cond_term_makes_impossible_smaller_num.
  rewrite mult_zero_right.
  reflexivity.
  all : exact Hneq.
Qed.

Lemma move_in_cond : forall  {A' B' D' G' : finType} (X : {RV P -> A'}) 
  (Y : {RV P -> B'}) (V : {RV P -> D'}) (W : {RV P -> G'}) w x y v,
  `Pr[ W = w | [% X, Y, V] = (x, y, v)]
  = `Pr[ W = w | [% Y, [% X, V]] = (y, (x, v))].
Proof.
  intros.
  assert (`Pr[ [% W, [% X, Y, V]] = (w, (x, y, v)) ] =
      `Pr[ [% W, [% Y, [% X, V]]] = (w, (y, (x, v)))]).
    intros.
    rewrite !pfwd1E /Pr.
    apply: eq_bigl=> a0.
    rewrite !inE.
    rewrite !xpair_eqE.
    case Hw : (W a0 == w).
    case Hx : (X a0 == x).
    case Hy : (Y a0 == y).
    case Hv : (V a0 == v).
      all: simpl; try rewrite andbF; try reflexivity.
  assert (`Pr[ [% X, Y, V] = (x, y, v) ] = 
      `Pr[ [% Y, [% X, V]] = (y, (x, v))]).
    intros.
    rewrite !pfwd1E /Pr.
    apply: eq_bigl=> a0.
    rewrite !inE.
    rewrite !xpair_eqE.
    case Hx : (X a0 == x).
    case Hy : (Y a0 == y).
    case Hv : (V a0 == v).
      all: simpl; try rewrite andbF; try reflexivity.
  
  rewrite !cpr_eqE.
  rewrite H1.
  apply div_both_sides.
  rewrite H0.
  reflexivity.
Qed.

Lemma alc_indep1 : 
  (forall pa t, `Pr[ T = t | [% D, M, Pa] = pa ] != 0) ->
  T _|_ [% D, Pa] | [% D, M, Pa].
Proof.
  intros.
  unfold cinde_RV.
  intros.
  destruct c as [[d m] p].
  rewrite move_in_cond.
  rewrite move_in_cond.
  rewrite move_in_cond.
  pose proof (alc_indep1_helper H0).
  unfold cinde_RV in H1.
  specialize (H1 a b (m, (d, p))).
  exact H1.
Qed.

Lemma change_to_set_three_way': forall {TA TB TD TU: finType} {P' : R.-fdist(TU)}
  (X : {RV P' -> TA}) (Y : {RV P' -> TB}) (Z: {RV P' -> TD}), 
  (forall (x : TA) (y : TB) (z : TD),
  `Pr[ X = x ] * `Pr[ Y = y ] * `Pr[ Z = z ] =
  `Pr[ [% X, Y, Z] = (x, y, z) ]) ->
  (forall (x : TA) (y : TB) (z' : {set TD}),
  `Pr[ X = x ] * `Pr[ Y = y ] * `Pr[ Z \in z' ] =
  `Pr[ [% X, Y, Z] \in ([set x] `* [set y] `* z') ]).
Proof.
  intros.
  specialize (H0 x y).
  rewrite sets_are_sums.
  rewrite sets_are_sums.
  (* Check big_distrr. *)
  rewrite <- mult_factor_in_sum with (k := (`Pr[ X = x ] * `Pr[ Y = y ])).
  assert (forall a : TD, true -> `Pr[ X = x ] * `Pr[ Y = y ] * `Pr[ Z = a ] = `Pr[ [% X, Y, Z] = (x, y, a) ]).
    intros.
    specialize (H0 a).
    assumption.
  rewrite -> eq_bigr with (F1 := (fun z => `Pr[ X = x ] * `Pr[ Y = y ] * `Pr[ Z = z ]))
      (F2 := (fun z => `Pr[ [% X, Y, Z] = (x, y, z) ])); try assumption.
  (* Check big_map.
  Check big_seq1. *)

  rewrite big_enum.
  rewrite big_enum.
  simpl.
  rewrite same_singleton_sets.
  pose proof (removing_singleton_from_sum (x,y) z' (fun i => `Pr[ [% X, Y, Z] = i])).
  simpl in H2.
  rewrite H2.
  reflexivity.
Qed.

Lemma mut_indp_with_fn': 
  forall {TU TA TB TD UD : finType} {P' : R.-fdist(TU)}
  (X : {RV P' -> TA}) (Y : {RV P' -> TB}) (Z: {RV P' -> TD}) (h : TD -> UD),
  mutual_indep_three' X Y Z ->
  mutual_indep_three' X Y (h `o Z).
Proof.
  intros.
  unfold mutual_indep_three'.
  intros.
  unfold mutual_indep_three' in H0.
  destruct H0 as [Indp3 [IndpXY [IndpYZ IndpXZ]]].
  split.

  intros.
  pose proof (set_A'_always_exists h z).
  (* destruct (classic  (exists (A': {set TD}), forall (a : TD), a \in A' -> h a = z)) as [ [a Hf] | Hfnotin ]. *)
  case: H0 => A [H0 H1].
  pose proof (change_to_set_three_way' X Y Z Indp3) as Indp3'.
  specialize (Indp3' x y A).

  rewrite -> pfwd1_comp_sets with (A' := A); try assumption.
  rewrite pfwd1_pairC.
  unfold swap.
  simpl.

  rewrite -> pfwd1_comp_sets_joint with (A' := A) (f := h) (X := Z) (Y := [% X, Y]); try assumption.
  rewrite pr_in_pairC.
  unfold swap.
  simpl.
  rewrite <- same_singleton_sets.
  exact Indp3'.

  split; try split; try assumption.
  pose proof (inde_RV_comp (fun x => x) h IndpYZ).
  exact H0.
  pose proof (inde_RV_comp (fun x => x) h IndpXZ).
  exact H0.
Qed.

(* Check (fst \o [% T, H, M]). *)

Lemma alc_indep2_helper : 
  mutual_indep_three' [% UFRV, UHRV] UMRV [% UMRV, UTRV, UDRV, UPRV] ->
  (* [% UFRV, UHRV] _|_ UMRV | [% UMRV, UTRV, UDRV, UPRV] -> *)
  H _|_ M | [% T, [% D, Pa]].
Proof.
  move=> mutind.
  unfold M.
  unfold H.
  unfold F. 
  (* apply cinde_fn_transform_gen. *)
  Check cinde_fn_transform_gen.

  (* f(T D Pa UFRV UHRV) _|_ f(T D Pa UMRV) | T D Pa *)
  (* UFRV UHRV _|_ UMRV | T D Pa *)
  (* UFRV UHRV _|_ UMRV | UMRV UTRV UDRV UPRV*)
Admitted.



Check cinde_alt.

Lemma inde_RV_alt : forall {TU TA TB : finType} {P' : R.-fdist(TU)}
  (X : {RV P' -> TA}) (Y : {RV P' -> TB}),
  P' |= X _|_ Y ->
  forall y, `Pr[ Y = y ] != 0 ->
  forall x, `Pr[ X = x ] = `Pr[ X = x | Y = y ].
Proof.
  intros.
  unfold inde_RV in H0.
  specialize (H0 x y).
  rewrite cpr_eqE.
  rewrite H0.
  rewrite mult_div; try assumption.
  reflexivity.
Qed.

Lemma pair_to_single_indep : forall {TU TA TB TD : finType} {P' : R.-fdist(TU)}
  (X : {RV P' -> TA}) (Y : {RV P' -> TB}) (Z: {RV P' -> TD}),
  P' |= X _|_ [% Y, Z ] ->
  P' |= X _|_ Z.
Proof.
  move=> TU TA TB TD P' X Y Z Hindep.
  unfold inde_RV.
  intros.
  rewrite -> total_prob' with (X := Z) (C := TB) (W := Y).
  rewrite -> total_prob' with (X := [% X, Z]) (C := TB) (W := Y).
  assert (`Pr[ X = x ] * (\sum_(u in TB)  `Pr[ [% Z, Y] = (y, u) ]) = 
      (\sum_(u in TB)  `Pr[ X = x ] * `Pr[ [% Z, Y] = (y, u) ])).
    rewrite -big_distrr.
    (* rewrite -big_distrr with (a := `Pr[ X = x ]). *)
    simpl.
    reflexivity.
  rewrite H0.
  apply eq_bigr => i _.
  unfold inde_RV in Hindep.
  specialize (Hindep x (i, y)).
  rewrite [in RHS] pfwd1_pairC.
  rewrite pfwd1_pairAC.
  rewrite <- pfwd1_pairA.
  unfold swap.
  simpl.
  assumption.
Qed.

(* Lemma swap_spots_indep : forall {TU TA TB TD : finType} {P' : R.-fdist(TU)}
  (X : {RV P' -> TA}) (Y : {RV P' -> TB}) (Z: {RV P' -> TD}),
  P' |= X _|_ [% Y, Z ] ->
  P' |= X _|_ [% Z, Y].
Proof.
  intros.
Admitted. *)

Lemma pair_to_cond_indep : forall {TU TA TB TD : finType} {P' : R.-fdist(TU)}
  (X : {RV P' -> TA}) (Y : {RV P' -> TB}) (Z: {RV P' -> TD}),
  P' |= X _|_ [% Y, Z ] ->
  P' |= X _|_ Y | Z.
Proof.
  intros.
  assert (P' |= X _|_ [% Y, Z]). assumption.
  unfold inde_RV in H0.
  unfold cinde_RV.
  intros.
  specialize (H0 a (b, c)).
  have [Hz | Hnz ] := boolP (`Pr[ Z = c ] == 0).
    move /eqP in Hz.
    rewrite !cpr_eq0_denom_gen; try assumption.
    rewrite mult_zero_left.
    reflexivity.
  rewrite !cpr_eqE.
  rewrite pfwd1_pairA in H0.
  rewrite H0.
  rewrite GRing.mulrA.
  apply div_both_sides.
  apply mult_both_sides_r.
  rewrite -cpr_eqE.
  apply inde_RV_alt; try assumption.
  (* apply swap_spots_indep in H1. *)
  apply pair_to_single_indep in H1.
  assumption.
Qed.

Lemma rv_equiv : 
  [% M, [% T, [% D, Pa]]] = ((fun y => (fM y.1.1.1 (fD y.1.2) (fP y.2 (fD y.1.2)),
                      ( fT y.1.1.2 (fD y.1.2) (fP y.2 (fD y.1.2)) (fM y.1.1.1 (fD y.1.2) (fP y.2 (fD y.1.2))),
                      (fD y.1.2, fP y.2 (fD y.1.2)))))
      `o [% UMRV, UTRV, UDRV, UPRV]).
Proof.
  unfold comp_RV.
  simpl.
  unfold T.
  unfold M.
  unfold Pa.
  unfold D.
  reflexivity.
Qed.

Lemma alc_indep2_helper3' : 
  P |= [% UHRV, UFRV] _|_ [% UMRV, UTRV, UDRV, UPRV] ->
  P |= [% UHRV, UFRV] _|_ [% M, [% T, [% D, Pa]]].
Proof.
  intros.
  pose proof (inde_RV_comp (fun x => x)
    (fun y => (fM y.1.1.1 (fD y.1.2) (fP y.2 (fD y.1.2)),
                      ( fT y.1.1.2 (fD y.1.2) (fP y.2 (fD y.1.2)) (fM y.1.1.1 (fD y.1.2) (fP y.2 (fD y.1.2))),
                      (fD y.1.2, fP y.2 (fD y.1.2))))) H0).
  unfold comp_RV in H1.
  simpl in H1.
  unfold T.
  unfold M.
  unfold Pa.
  unfold D.
  assumption.
Qed.

Lemma indp_not_affected_by_adding_cond_rev_gen: forall {TA TB TD UU: finType}
  {P' : R.-fdist(UU)} (X : {RV P' -> TA}) (Y : {RV P' -> TB}) (Z: {RV P' -> TD}),
  [% X, Z] _|_ [% Y, Z ] | Z ->
  X _|_ Y | Z. 
Proof.
  intros.
  unfold cinde_RV.
  intros.
  unfold cinde_RV in H0.
  specialize (H0 (a, c) (b, c) c).

  have [Hzero | Hnonzero] := boolP (`Pr[Z = c] == 0).
    move/eqP: Hzero => Hz'.
    rewrite !cpr_eq0_denom_gen; try assumption.
    rewrite mult_zero_left.
    reflexivity.

  rewrite can_move_cond_gen in H0.
  rewrite can_move_cond_gen in H0.
  rewrite <- H0.

  rewrite cpr_eqE.
  rewrite cpr_eqE.
  apply div_both_sides.

  rewrite pfwd1E. 
  rewrite pfwd1E.
  rewrite /Pr.
  apply eq_bigl => a0.
  rewrite !inE.
  rewrite !xpair_eqE.
  rewrite !andbA.
  rewrite <- andbA.
  destruct (X a0 == a).
  destruct (Y a0 == b).
  destruct (Z a0 == c).
  all: simpl.
  reflexivity.
  reflexivity.
  rewrite andbF.
  simpl.
  reflexivity.
  reflexivity.
Qed.

Lemma alc_indep2_helper2' :
  P |= [% UHRV, UFRV] _|_ [% M, [% T, [% D, Pa]]] ->
  H _|_ [% M, [% D, Pa]] | [% T, [% D, Pa]].
Proof.
  move => Hindep.
  pose proof (pair_to_cond_indep [% UHRV, UFRV] M [% T, [% D, Pa]] Hindep).
  apply adding_conditional_to_indep in H0.
  (* apply indp_not_affected_by_adding_cond_gen in H0. *)
  pose proof (indp_not_affected_by_adding_cond_gen _ _ _ H0).
  Check cinde_fn_transform_gen.
  pose proof (cinde_fn_transform_gen [% UHRV, UFRV] [% M, [% D, Pa]] [% T, [% D, Pa]]
      (fun x => fH x.1.1 x.2.2.1 x.2.2.2 (fF x.1.2 x.2.2.1 x.2.1) x.2.1)
      (fun y => y.1) H1).
  unfold comp_RV in H2.
  simpl in H2.
  unfold H.
  unfold F.
  assumption.
Qed.

Lemma alc_indep2_helper1' :
  H _|_ [% M, [% D, Pa]] | [% T, [% D, Pa]] ->
  H _|_ [% D, M, Pa] | [% T, [% D, Pa]].
Proof.
  intros.
  unfold cinde_RV.
  intros.
  destruct b as [[d m] p].
  assert (`Pr[ [% H, [% M, [% D, Pa]]] = (a, (m, (d, p))) | [% T, [% D, Pa]] = c] =
      `Pr[ [% H, [% D, M, Pa]] = (a, (d, m, p)) | [% T, [% D, Pa]] = c]).
    case: (boolP ( `Pr[ [% T, [% D, Pa]] = c ] == 0 )).
      intros.
      move /eqP in p0.
      rewrite !cpr_eq0_denom_gen; try assumption.
      reflexivity.
    intros.
    rewrite !cpr_eqE.
    apply div_both_sides.
    destruct c as [t' [d' p']].

    rewrite !pfwd1E /Pr.
    apply: eq_bigl=> a0.
    rewrite !inE.
    rewrite !xpair_eqE.
    case Ht : (H a0 == a).
    case Mt : (M a0 == m).
    case Dt : (D a0 == d).
    case Pt : (Pa a0 == p).
    case Ttt : (T a0 == t').
    case Dtt : (D a0 == d').
    case Ptt : (Pa a0 == p').
      all: simpl; try rewrite andbF; try reflexivity.

  assert (`Pr[ [% M, [% D, Pa]] = (m, (d, p)) | [% T, [% D, Pa]] = c] =
      `Pr[ [% D, M, Pa] = (d, m, p) | [% T, [% D, Pa]] = c]).
    case: (boolP ( `Pr[ [% T, [% D, Pa]] = c ] == 0 )).
      intros.
      move /eqP in p0.
      rewrite !cpr_eq0_denom_gen; try assumption.
      reflexivity.
    intros.
    rewrite !cpr_eqE.
    apply div_both_sides.
    destruct c as [t' [d' p']].

    rewrite !pfwd1E /Pr.
    apply: eq_bigl=> a0.
    rewrite !inE.
    rewrite !xpair_eqE.
    case Mt : (M a0 == m).
    case Dt : (D a0 == d).
    case Pt : (Pa a0 == p).
    case Ttt : (T a0 == t').
    case Dtt : (D a0 == d').
    case Ptt : (Pa a0 == p').
      all: simpl; try rewrite andbF; try reflexivity.
    
  rewrite -H1.
  rewrite -H2.
  unfold cinde_RV in H0.
  clear H1.
  clear H2.
  specialize (H0 a (m, (d, p)) c).
  assumption.
Qed.

Lemma alc_indep2 :
  P |= [% UHRV, UFRV] _|_ [% UMRV, UTRV, UDRV, UPRV] ->
  H _|_ [% D, M, Pa] | [% T, [% D, Pa]].
Proof.
  intros.
  apply alc_indep2_helper1'.
  apply alc_indep2_helper2'.
  apply alc_indep2_helper3'.
  assumption.
  (* Check adding_conditional_to_indep.
  apply pair_to_cond_indep.

  Check adding_conditional_to_indep. *)
Qed.

Lemma backdoor_adj_alcohol : forall t,
  (forall h pa e,
  `Pr[ [% (Hinterv t), [% (Dinterv t), (Minterv t), (Pinterv t)], 
      (Finterv t)] = (h, pa, e) ] 
      = `Pr[ [% H, T, [% D, M, Pa] , F] = (h, t, pa, e) ] 
        / `Pr[ T = t | [% D, M, Pa] = pa ]) ->
  (forall pa t, `Pr[ T = t | [% D, M, Pa] = pa ] != 0) ->
  P |= [% UHRV, UFRV] _|_ [% UMRV, UTRV, UDRV, UPRV] ->
  (forall h, `Pr[(Hinterv t) = h] = \sum_(dp : ocD * ocP) 
      `Pr[ H = h | [% T, [% D, Pa] ] = (t, dp)] * `Pr[[% D, Pa] = dp]).
Proof.
  move => t Hfactor Hindep Hnonneg.
  eapply graphfactor_indp_backdoor_adj with 
    (paTinterv := (fun t => [% (Dinterv t), (Minterv t), (Pinterv t)]))
    (Einterv := Finterv)
    (paT := [% D, M, Pa])
    (E := F); try assumption.
    apply alc_indep1; try assumption.
    apply alc_indep2; try assumption.
Qed.

Print Assumptions backdoor_adj_alcohol.

End alcohol.
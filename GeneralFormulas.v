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

Local Open Scope ring_scope.
Local Open Scope reals_ext_scope.
Local Open Scope fdist_scope.
Local Open Scope proba_scope.

Section GeneralLemmas.

Context {R : realType}.

(*  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
                        SECTION : DEFINITIONS 
    %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%  *)

Definition mutual_indep_three {A : finType} {P : R.-fdist (A)} {X' Y' Z': finType}
  (X : {RV P -> X'}) (Y : {RV P -> Y'}) (Z: {RV P -> Z'}) := 
  (forall x y z,
  `Pr[ X = x ] * `Pr[ Y = y ] * `Pr[ Z = z ] 
    = `Pr[ [%[% X, Y], Z] = ((x,y), z)]) /\ 
    P |= X _|_ Y /\ P |= Y _|_ Z /\ P |= X _|_ Z.


(*  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
                        SECTION : MATH LEMMAS 
    %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%  *)

Lemma mult_both_sides_r: forall (a b c : R),
  a = b ->
  a * c = b * c.
Proof.
  by move=> a b c ->.
Qed.

Lemma mult_both_sides_l: forall (a b c : R),
  a = b ->
  c * a = c * b.
Proof.
  by move=> a b c ->.
Qed.

Lemma mult_div: forall (a b: R),
  b != 0 ->
  a * b / b = a.
Proof.
  intros.
  apply esym.
  rewrite <- GRing.mulrA.
  rewrite GRing.mulfV.
  rewrite GRing.mulr1.
  reflexivity.
  assumption.
Qed.

Lemma div_mult: forall (a b: R),
  b != 0 ->
  a / b * b = a.
Proof.
  intros.
  apply esym.
  eapply eqr_divrMr.
  assumption.
  reflexivity.
Qed.

Lemma mult_in_middle: forall (a b c : R),
  b != 0 ->
  a / b * ( b / c ) = a / c.
Proof.
  move=> a b c hb.
  rewrite GRing.mulrA.
  rewrite GRing.divfK.
  reflexivity.
  assumption.
Qed.

Lemma div_num_and_denom: forall (a b c d : R),
  b != 0 ->
  a / b / (c / b) = a / c.
Proof.
  intros.
  rewrite GRing.invfM GRing.invrK.
  rewrite -!GRing.mulrA.
  rewrite [c^-1 * b]GRing.mulrC.
  rewrite GRing.mulrA.
  rewrite GRing.mulrA.
  rewrite GRing.divfK.
  reflexivity.
  assumption.
Qed.

Lemma mult_zero_right: forall (a : R),
  a * 0 = 0.
Proof.
  intros.
  rewrite GRing.mulr0.
  reflexivity.
Qed.

Lemma mult_zero_left: forall (a : R),
  0 * a = 0.
Proof.
  intros.
  rewrite GRing.mul0r.
  reflexivity.
Qed.

Lemma div_div: forall (a b c : R),
  b != 0 ->
  c != 0 -> 
  a / (b / c) = a / b * c.
Proof.
  move=> a b c Hb Hc.
  rewrite GRing.invrM ?GRing.unitfE ?GRing.invr_neq0 //.
  rewrite GRing.invrK.
  rewrite GRing.mulrAC.
  rewrite GRing.mulrA.
  reflexivity.
Qed.

Lemma div_both_sides: forall (a b c : R),
  a = b ->
  a / c = b / c.
Proof.
  by move=> a b c ->.
Qed.

Lemma change_ord_mult: forall (a b c : R),
  a * b * c  = a * c * b.
Proof.
  intros.
  rewrite -!GRing.mulrA.
  rewrite [b * c]GRing.mulrC.
  reflexivity.
Qed.

Lemma zero_div_zero: forall (a : R),
  a != 0 ->
  0 / a = 0.
Proof.
  intros.
  rewrite GRing.mul0r.
  reflexivity.
Qed.

Lemma div_not_zero: forall (a b : R),
  b != 0 ->
  a / b != 0 ->
  a != 0.
Proof.
  move=> a b _. apply: contra.
  by move/eqP=> ->; rewrite GRing.mul0r.
Qed.

Lemma false_cant_be:
  (0 : R) != 0 ->
  ~~true.
Proof.
  intros.
  rewrite eqxx in H.
  assumption.
Qed.

Lemma b_in_set_b : forall {B: finType} (b: B),
  b \in [set b].
Proof.
  intros.
  rewrite inE.
  apply eqxx.
Qed.

Lemma not_b_not_in_set_b: forall {B: finType} (b: B) (a: B),
  a != b ->
  a \notin [set b].
Proof.
  intros.
  rewrite inE.
  assumption.
Qed.

Lemma same_singleton_sets: forall {A B : finType} (x : A) (y : B),
  setX [set x] [set y] = [set (x, y)].
Proof.
  intros.
  apply/setP => p.
  rewrite !inE.
  apply @erefl.
Qed.

(* Helper lemma.
   fin_img is a set with no repeated elements. *)
Lemma fin_img_uniq: forall {U : finType} f1,
  uniq (fin_img (A:=U) (B:=R) f1).
Proof.
  intros.
  unfold fin_img.
  apply undup_uniq.
Qed.

(* Helper lemma.
   Given two sets without repeats ordering based on one
   and conditioning on the other results in the same set
   of elements regradless of which you pick for ordering
   vs conditioning. *)
Lemma seq_cond_or_cond_seq: forall (A B : seq R),
  uniq A ->
  uniq B ->
  perm_eq [seq i <- A | i  \in B] [seq i <- B | i  \in A].
Proof.
  intros.
  apply uniq_perm.
  - apply filter_uniq.
    assumption.
  - apply filter_uniq.
    assumption.
  - move=> x.
    rewrite mem_filter.
    rewrite mem_filter.
    apply Bool.andb_comm.
Qed.

(*  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
                  SECTION : SIMPLE PROBABILITY LEMMAS 
    %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%  *)

(* Important Lemma that says that if the thing you're
   conditioning on in a probability is 0, the entire 
   conditional probability is zero. Is used to deal
   with annyoing P[Z=b] != 0 cases throughout proofs. *)
Lemma cpr_eq0_denom: forall {TA TD: finType}
  {U : finType} {P : R.-fdist (U)}
  (X : {RV P -> TA}) (Y: {RV P -> TD}) a b,
  `Pr[Y = b] = 0 ->
  `Pr[X = a | Y = b] = 0.
Proof.
  move => TA TD U P X Y a b Hz.
  rewrite cPr_eq_finType.
  apply cPr_eq0P.
  rewrite setIC. 
  apply Pr_domin_setI.
  rewrite <- cpr_eq_unit_RV in Hz.
  rewrite cPr_eq_finType in Hz.
  apply cPr_eq0P in Hz.
  assert (Y @^-1: [set b] :&: unit_RV P @^-1: [set tt] = Y @^-1: [set b]) as H1.
    simpl.
    apply/setP => u.
    rewrite !inE.
    destruct (Y u == b).
    simpl.
    unfold unit_RV.
    rewrite eq_refl.
    reflexivity.
    simpl.
    reflexivity.
  rewrite <- Hz.
  rewrite H1.
  reflexivity.
Qed.

Lemma rearrange_cond: forall {A B C : finType} 
  {U : finType} {P : R.-fdist (U)}
  (X : {RV P -> A}) (Y : {RV P -> B}) (W : {RV P -> C}) w x y,
  `Pr[ W = w | [% X, Y] = (x, y)] = `Pr[ W = w | [% Y, X] = (y, x)].
Proof.
  intros.
  rewrite !cpr_eqE.
  rewrite -> pfwd1_pairC with (TY := X) (TX := Y).
  unfold swap.
  simpl.
  rewrite pfwd1_pairA.
  rewrite pfwd1_pairAC.
  rewrite <- pfwd1_pairA.
  reflexivity.
Qed.

Lemma pair_to_single_non_zero: forall {A B : finType} 
  {U : finType} {P : R.-fdist (U)}
  (X : {RV P -> A}) (Y : {RV P -> B}) x y,
  `Pr[ [% X, Y] = (x, y) ] != 0 ->
  `Pr[ X = x ] != 0.
Proof.
  move => A B U P X Y x y Hnz.
  intros.
  have [Hzero | Hnonzero] := boolP (`Pr[X = x] == 0).
  move/eqP: Hzero => Hzero.
  apply pfwd1_domin_RV2 with (TX := X) (TY := Y) (b := y) in Hzero.
  rewrite Hzero in Hnz .
  apply false_cant_be in Hnz.
  discriminate.

  exact is_true_true.
Qed.

Lemma indep_to_equality: forall {A B C : finType} 
  {U : finType} {P : R.-fdist (U)}
  (X : {RV P -> A}) (Y : {RV P -> B}) (W : {RV P -> C}) x y w,
  X _|_ Y | W ->
  `Pr[ [% Y, W] = (y, w) ] != 0 ->
  `Pr[ X=x | W=w ] = `Pr[ X=x | [% W, Y] = (w,y)]. 
Proof.
  intros.
  rewrite rearrange_cond.
  rewrite cinde_alt.
  reflexivity.
  assumption.
  assumption.
Qed.

(* Needed for infotheo libaray's total_prob and total_prob_cond lemmas *)
Lemma disjoint_true: forall {C: finType} 
  {U : finType} {P : R.-fdist (U)}
  (W : {RV (P) -> C}), 
  (forall i j : C,
  i != j ->
  [disjoint finset (T:=U) (preim W (pred1 i)) & finset (T:=U) (preim W (pred1 j))]).
Proof.
  move => C U P W i j Hneq.
  rewrite <- setI_eq0.
  rewrite eqEsubset.
  rewrite sub0set.
  rewrite Bool.andb_true_r.
  apply/subsetP => y.
  rewrite in_set0.
  rewrite inE.
  rewrite !in_set.
  simpl.
  move => H1.
  move/andP in H1.
  inversion H1 as [H2 H3].
  move/eqP in H2.
  move/eqP in H3.
  rewrite <- H2 in Hneq.
  rewrite <- H3 in Hneq.
  rewrite eqxx in Hneq.
  exact Hneq.
Qed.

(* Needed for infotheo libaray's total_prob and total_prob_cond lemmas *)
Lemma cover_true: forall {C: finType} 
  {U : finType} {P : R.-fdist (U)}
  (W : {RV (P) -> C}),
  cover [set finset (T:=U) (preim W (pred1 i)) | i : C] = [set: U].
Proof.
  intros.
  apply/setP=> y. 
  rewrite inE.
  apply/bigcupP.
  exists ((finset (T:=U) (preim W (pred1 (W y))))).
  apply/imsetP.
  exists (W y).
  rewrite inE.
  reflexivity.
  reflexivity.
  
  rewrite inE.
  rewrite /=.
  apply eqxx.
Qed.

Lemma total_prob': forall {A C : finType} 
  {U : finType} {P : R.-fdist (U)}
  (X : {RV P -> A})
  (W : {RV P -> C}) x,
  `Pr[ X = x ] = \sum_(u in C) `Pr[ [% X, W] = (x, u) ].
Proof.
  move => A C U P X W x.
  rewrite pfwd1E.
  rewrite -> total_prob with (I := C)
      (F := (fun i => (finset (T:=U) (preim W (pred1 i))))).
  apply eq_bigr => u _.
  unfold RV2.
  rewrite pfwd1E.
  assert ((finset (T:=U) (preim X (pred1 x)) :&: finset (T:=U) (preim W (pred1 u))) = 
      (finset (T:=U) (preim (fun x0 : U => (X x0, W x0)) (pred1 (x, u))))) as H0.
    apply/setP => t.
    rewrite !inE.
    apply xpair_eqE.
  rewrite H0.
  reflexivity.

  apply disjoint_true.
  apply cover_true.
Qed.

Lemma marginalize: forall {A C : finType} 
  {U : finType} {P : R.-fdist (U)}
  (X : {RV P -> A}) (W : {RV P -> C}) x,
  `Pr[ X = x ] = \sum_(u in C) 
      `Pr[ X = x | W = u ] * `Pr[ W = u ].
Proof.
  intros.
  rewrite pfwd1E.
  rewrite -> total_prob_cond with (I := C) 
      (F := (fun i => (finset (T:=U) (preim W (pred1 i))))).
  apply eq_bigr => u _.
  rewrite <- pfwd1E.
  rewrite <- cPr_eq_def.
  reflexivity.
  apply disjoint_true.
  apply cover_true.
Qed.

Lemma marginalize_cond: forall {A B C : finType} 
  {U : finType} {P : R.-fdist (U)}
  (X : {RV P -> A}) (Y : {RV P -> B}) (W : {RV P -> C}) x y,
  `Pr[ X=x | Y=y ] = \sum_(u in C) 
      `Pr[ X=x | [% Y, W] = (y, u) ] * `Pr[ W=u | Y = y ].
Proof.
  move => A B C U P X Y W x y.

  have [Hzero | Hnonzero] := boolP (`Pr[Y = y] == 0).
    move/eqP: Hzero => Hzero.
    rewrite !cpr_eq0_denom; try assumption.
    under eq_bigr => u _.
      rewrite !cpr_eq0_denom; try assumption; cycle 1.
      apply pfwd1_domin_RV2.
      assumption.
      rewrite mult_zero_right.
      over.
    simpl.
    rewrite big1; intros; reflexivity.

  rewrite cpr_eqE.

  assert (\sum_(u in C) `Pr[ X = x | [% Y, W] = (y, u) ] * `Pr[ W = u | Y = y ]
        = \sum_(u in C) `Pr[ [% X, [% Y, W]] = (x, (y, u)) ] / `Pr[ Y = y ]) as H0.
    apply eq_bigr => u _.
    case: (boolP (`Pr[ [% W, Y] = (u, y) ] == 0)).
      intros.
      move /eqP in p.
      rewrite pfwd1_pairC in p. unfold swap in p. simpl in p.
      rewrite -> cpr_eq0_denom with (Y := [% Y, W]); try assumption.
      rewrite mult_zero_left.
      rewrite -> pfwd1_domin_RV1 with (TX := X) (a := x); try assumption.
      rewrite zero_div_zero; try assumption.
      reflexivity.

    move => Hnz.
    rewrite !cpr_eqE.
    rewrite -> pfwd1_pairC with (TY := Y) (TX := W).
    unfold swap.
    simpl.
    rewrite mult_in_middle; try assumption.
    reflexivity.

  rewrite H0.
  rewrite -[RHS]big_enum.
  simpl.
  rewrite -[RHS]big_distrl.
  simpl.
  rewrite big_enum.
  simpl.
  rewrite eqr_divrMr; try assumption.
  rewrite div_mult; try assumption.
  rewrite -> total_prob' with (X := ([% X, Y])) (W := W).
  apply eq_bigr => w _.
  rewrite pfwd1_pairA.
  reflexivity.
Qed.

Lemma rearrange_brackets: forall {A B C D : finType} 
  {U : finType} {P : R.-fdist (U)}
  (X : {RV P -> A}) (Y : {RV P -> B})
  (W : {RV P -> C}) (V : {RV P -> D}) v w x y,
  `Pr[ W = w | [% X, [% Y, V]] = (x, (y, v))] = 
      `Pr[ W = w | [% [%X, Y], V] = ((x, y), v)].
Proof.
  intros.

  case: (boolP (`Pr[ [% X, Y, V] = (x, y, v) ] == 0)).
    intros.
    move /eqP in p.
    rewrite cpr_eq0_denom.
    rewrite cpr_eq0_denom.
    reflexivity.
    exact p.
    rewrite pfwd1_pairA.
    exact p.

  intros.
  rewrite cpr_eqE.
  rewrite cpr_eqE.
  rewrite pfwd1_pairA.
  apply div_both_sides; try assumption.
  rewrite pfwd1_pairA.
  rewrite pfwd1_pairA.
  
  rewrite !pfwd1E /Pr.
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
        reflexivity.
Qed.

Lemma pair_to_single_non_zero_right: forall {A B : finType} 
  {U : finType} {P : R.-fdist (U)}
  (X : {RV P -> A}) (Y : {RV P -> B}) x y,
  `Pr[ [% X, Y] = (x, y) ] != 0 ->
  `Pr[ Y = y ] != 0.
Proof.
  move => A B U P X Y x y H0.
  have [Hzero | Hnonzero] := boolP (`Pr[Y = y] == 0).
    move/eqP: Hzero => Hz'.
    rewrite pfwd1_domin_RV1 in H0.
      apply false_cant_be; assumption.
      assumption.
    
    exact is_true_true.
Qed.

Lemma pair_to_single_non_zero_left: forall {A B : finType} 
  {U : finType} {P : R.-fdist (U)}
  (X : {RV P -> A}) (Y : {RV P -> B}) x y,
  `Pr[ [% X, Y] = (x, y) ] != 0 ->
  `Pr[ X = x ] != 0.
Proof.
  move => A B U P X Y x y H0.
  rewrite pfwd1_pairC in H0.
  unfold swap in H0. simpl in H0.
  eapply pair_to_single_non_zero_right.
  exact H0.
Qed.

Lemma pfwd1_pairA_cond: forall {TA TB TC TD : finType} 
  {U : finType} {P : R.-fdist (U)}
  {TX : {RV P -> TA}} {TY : {RV P -> TB}} 
  {TZ : {RV P -> TC}} {TW : {RV P -> TD}} {a b c d},
  `Pr[ [% TX, [% TY, TZ]] = (a, (b, c)) | TW = d ] =
  `Pr[ [% TX, TY, TZ] = (a, b, c) | TW = d].
Proof.
  intros.
  case: (boolP (`Pr[ TW = d ] == 0)).
    intros.
    move /eqP in p.
    rewrite cpr_eq0_denom.
    rewrite cpr_eq0_denom.
    reflexivity.
    exact p.
    exact p.

  intros.
  rewrite cpr_eqE.
  rewrite cpr_eqE.
  apply div_both_sides; try assumption.
  
  rewrite !pfwd1E /Pr.
  apply: eq_bigl=> a0.
  rewrite !inE.
  rewrite !xpair_eqE.
  case Hx : (TX a0 == a).
    case Hv : (TY a0 == b).
      case Hy : (TZ a0 == c).
        case Hw : (TW a0 == d).
        simpl.
        reflexivity.

        simpl.
        reflexivity.

        simpl.
        reflexivity.

        simpl.
        reflexivity.

        simpl.
        reflexivity.
Qed.

Lemma remove_redundant_cond_term: forall  {A B D : finType} 
  {U : finType} {P : R.-fdist (U)}
  (X : {RV P -> A}) (Y : {RV P -> B}) (V : {RV P -> D}) x y v,
  `Pr[ [% X, V] = (x, v) | [% Y, V] = (y, v)]
  = `Pr[ X = x | [% Y, V] = (y, v)].
Proof.
  intros.
  destruct (classic (`Pr[ [% Y, V] = (y, v) ] == 0)) as [H0 | H0].
    move /eqP in H0.
    rewrite cpr_eq0_denom; try assumption.
    rewrite cpr_eq0_denom; try assumption.
    reflexivity.

  rewrite cpr_eqE.
  rewrite cpr_eqE.
  apply div_both_sides with (c := `Pr[ [% Y, V] = (y, v) ]); try assumption.
  rewrite !pfwd1E /Pr.
  apply: eq_bigl=> a0.
  rewrite !inE.
  rewrite !xpair_eqE.
  case Hx : (X a0 == x).
    case Hv : (V a0 == v).
      case Hy : (Y a0 == y).
        simpl.
        reflexivity.

        simpl.
        reflexivity.

        simpl.
        rewrite andbF.
        reflexivity.

        simpl.
        reflexivity.
Qed.

Lemma cond_term_makes_impossible: forall  {A B D : finType} 
  {U : finType} {P : R.-fdist (U)}
  (X : {RV P -> A}) (Y : {RV P -> B}) (V : {RV P -> D}) x y v1 v2,
  v1 != v2 ->
  `Pr[ [% X, V] = (x, v1) | [% Y, V] = (y, v2)] = 0.
Proof.
  move => A B D U P X Y V x y v1 v2 H0.
  destruct (classic (`Pr[ [% Y, V] = (y, v2) ] == 0)) as [H1 | H1].
    move /eqP in H1.
    rewrite cpr_eq0_denom; try assumption. 
    reflexivity.

  rewrite cpr_eqE.
  assert (`Pr[ [% X, V, [% Y, V]] = (x, v1, (y, v2)) ] = 0) as H2.
  rewrite pfwd1E.
  rewrite /Pr.
  under eq_bigl => a.

  rewrite !inE.
  rewrite !xpair_eqE.
  case Hv1 : (V a == v1).
    assert ((V a == v2) = false) as H2.
      by rewrite (eqP Hv1); exact/negbTE.
    rewrite H2.
    rewrite andbF.
    rewrite andbF.
    over.
    
    rewrite andbF.
    simpl.
    over.
  
    simpl.
    apply big_pred0_eq.
  
  rewrite H2.
  apply zero_div_zero.
  apply /negP.
  assumption.
Qed.

Lemma adding_conditional_to_indep: forall {A B C D : finType} 
  {U : finType} {P : R.-fdist (U)}
  (X : {RV P -> A}) (Y : {RV P -> B})
  (W : {RV P -> C}) (V : {RV P -> D}),
  X _|_ Y | [% W, V] ->
  X _|_ [% Y, V] | [% W, V].
Proof.
  move => A B C D U P X Y W V H0.
  unfold cinde_RV in H0.
  unfold cinde_RV.
  intros.
  destruct b as [y z1].
  specialize (H0 a y c).
  destruct c as [w z2].
  rewrite cpr_eq_pairA.
  destruct (classic (z1 == z2)) as [H1 | H1].
    move /eqP in H1.
    inversion H1.
  rewrite remove_redundant_cond_term.
  (* rewrite -> remove_redundant_cond_term with (X := [% X, Y]) (V := V) (Y := W). *)
  rewrite remove_redundant_cond_term.
  assumption.

  rewrite cond_term_makes_impossible.
  rewrite cond_term_makes_impossible.
  rewrite mult_zero_right.
  reflexivity.
  all: apply /negP; assumption.
Qed.

(* Alternate independence definition *)
Lemma indep_then_cond_irrelevant: 
    forall {U TX TZ: finType} {P: R.-fdist (U) }
    (X: {RV P -> TX}) (Z: {RV P -> TZ}),
  P |= Z _|_ X ->
  forall x, `Pr[ X = x ] != 0 ->
  forall z, `Pr[ Z = z ] = `Pr[ Z = z | X = x ].
Proof.
  move => U TX TZ P X Z H0 x H1 z.
  unfold inde_RV in H0.
  specialize (H0 z x).
  rewrite cpr_eqE.
  rewrite H0.
  set y := `Pr[ X = x].
  assert (y != 0) by exact H1.
  apply esym.
  apply mult_div.
  assumption.
Qed.

(* This lemma states that mutual independence gives us
   conditional independence. *)
Lemma mut_indp_cond_indp : forall {X' Y' Z': finType}
  {U: finType} {P: R.-fdist(U)}
  (X : {RV P -> X'}) (Y : {RV P -> Y'}) (Z: {RV P -> Z'}),
  mutual_indep_three X Y Z ->
  X _|_ Y | Z.
Proof.ar
  intros.
  unfold mutual_indep_three in H.
  unfold cinde_RV.
  intros.
  destruct H as [Indp3 [IndpXY [IndpYZ IndpXZ]]].
  specialize (Indp3 a b c).
  unfold inde_RV in IndpXY.
  unfold inde_RV in IndpXZ.
  unfold inde_RV in IndpYZ.
  specialize (IndpXY a b).
  specialize (IndpXZ a c).
  specialize (IndpYZ b c).
  have [Hzero | Hnonzero] := boolP (`Pr[Z = c] == 0).
    move/eqP: Hzero => H0.
    rewrite !cpr_eq0_denom; try assumption.
    rewrite mult_zero_left.
    reflexivity.
  rewrite !cpr_eqE.
  rewrite IndpYZ.
  rewrite IndpXZ.
  rewrite mult_div.
  rewrite mult_div.
  rewrite eqr_divrMr.
  rewrite Indp3.
  reflexivity.
  all: assumption.
Qed.

(* Lemma that states that if there is no value d such
   that h d = z, then we also know that the RV h `o Z
   can also never be z. *)
Lemma no_fn_val_prob_zero : forall {TD UD : finType}
  {U: finType} {P: R.-fdist (U)}
  (Z: {RV P -> TD}) (h : TD -> UD) z,
  ~ (exists d : TD, h d = z) ->
  `Pr[ (h `o  Z) = z ] = 0.
Proof.
  intros.
  apply pfwd1_eq0.
  rewrite /fin_img.
  apply /negP.
  rewrite mem_undup.
  move /mapP.
  move => Hhoz.
  move: Hhoz => [x Hx Hhoz].
  unfold comp_RV in Hhoz.
  assert (exists d : TD, h d = z).
    exists (Z x).
    rewrite Hhoz.
    reflexivity.
  contradiction.
Qed. 

Lemma same_RV_two_vals: forall {TA UU: finType} {P' : R.-fdist(UU)}
  (X : {RV P' -> TA}) a b,
  b <> a ->
  `Pr[ [% X, X] = (a, b)] = 0.
Proof.
  intros.
  rewrite pfwd1_eq0.
  reflexivity.
  rewrite /fin_img.
  apply /negP.
  rewrite mem_undup.
  move /mapP.
  move => Hpair.
  move: Hpair => [x Hx Hpair].
  unfold RV2 in Hpair.
  inversion Hpair.
  rewrite H2 in H.
  rewrite H1 in H.
  contradiction.
Qed.

Lemma can_move_cond: forall {TA TD UU: finType} {P' : R.-fdist(UU)}
  (X : {RV P' -> TA}) (Z: {RV P' -> TD}) a c,
  `Pr[ [% X, Z] = (a, c) | Z = c ] = `Pr[ X = a | Z = c].
Proof.
  intros.
  
  have [Hzero | Hnonzero] := boolP (`Pr[Z = c] == 0).
    move/eqP: Hzero => H0.
    rewrite !cpr_eq0_denom; try assumption.
    reflexivity.

  rewrite cpr_eqE.
  simpl.
  rewrite cpr_eqE.
  eapply eqr_divrMr.
  assumption.
  rewrite div_mult.

  rewrite pfwd1E. rewrite pfwd1E.
  rewrite /Pr.
  apply eq_bigl => a0.
  rewrite !inE.
  rewrite xpair_eqE.
  rewrite xpair_eqE.
  rewrite <- andbA.
  rewrite Bool.andb_diag.
  reflexivity.
  assumption.
Qed.

Lemma cond_not_match_arg: forall {TA TD UU: finType} {P' : R.-fdist(UU)}
  (X : {RV P' -> TA}) (Z: {RV P' -> TD}) a b c,
  b <> c ->
  `Pr[ [% X, Z] = (a, b) | Z = c ] = 0.
Proof.
  intros.
  
  have [Hzero | Hnonzero] := boolP (`Pr[Z = c] == 0).
    move/eqP: Hzero => Hz'.
    rewrite !cpr_eq0_denom; try assumption.
    reflexivity.

  rewrite cpr_eqE.
  eapply eqr_divrMr.
  assumption.
  rewrite mult_zero_left.
  rewrite <- pfwd1_pairA.
  apply pfwd1_domin_RV1.
  apply same_RV_two_vals.
  apply nesym.
  assumption.
Qed.


Lemma indp_not_affected_by_adding_cond: forall {TA TB TD UU: finType}
  {P' : R.-fdist(UU)} (X : {RV P' -> TA}) (Y : {RV P' -> TB}) (Z: {RV P' -> TD}),
  X _|_ Y | Z ->
  [% X, Z] _|_ [% Y, Z ] | Z. 
Proof.
  intros.
  unfold cinde_RV.
  intros.
  destruct a as [a a2].
  destruct b as [b b2].

  have [Hzero | Hnonzero] := boolP (`Pr[Z = c] == 0).
    move/eqP: Hzero => Hz'.
    rewrite !cpr_eq0_denom; try assumption.
    rewrite mult_zero_left.
    reflexivity.

  destruct (a2 =P c) as [Heq1 | Hneq1].
  destruct (b2 =P c) as [Heq2 | Hneq2].
  rewrite Heq1.
  rewrite Heq2.
  rewrite can_move_cond.
  rewrite can_move_cond.

  unfold cinde_RV in H.
  specialize (H a b c).
  rewrite <- H.
  rewrite cpr_eqE.
  rewrite cpr_eqE.
  rewrite eqr_divrMr.
  rewrite div_mult.

  rewrite pfwd1E. 
  rewrite pfwd1E.
  rewrite /Pr.
  apply eq_bigl => a0.
  rewrite !inE.
  rewrite !xpair_eqE.
  rewrite !andbA.
  rewrite <- andbA.
  rewrite Bool.andb_diag.
  destruct (X a0 == a).
  destruct (Y a0 == b).
  destruct (Z a0 == c).
  all: simpl.
  reflexivity.
  reflexivity.
  destruct (Z a0 == c).
  simpl.
  reflexivity.
  simpl.
  reflexivity.
  reflexivity.
  assumption.
  assumption.

  inversion Heq1.
  clear H0.
  rewrite can_move_cond.
  rewrite cond_not_match_arg; try assumption.
  rewrite cpr_eqE.
  rewrite -> pfwd1_pairC.
  unfold swap.
  simpl.
  rewrite -> pfwd1_pairA.
  rewrite -> pfwd1_pairA. 
  rewrite mult_zero_right.
  rewrite eqr_divrMr.
  rewrite mult_zero_left.
  rewrite <- pfwd1_pairA.
  rewrite <- pfwd1_pairA.
  apply pfwd1_domin_RV1 with (TX := Z) (TY := [% X, Z, [% Y, Z]]).
  rewrite <- pfwd1_pairA.
  apply pfwd1_domin_RV1 with (TX := X) (TY := [% Z, [% Y, Z]]).
  rewrite pfwd1_pairCA.
  apply pfwd1_domin_RV1 with (TX := Y) (TY := [% Z, Z]).
  apply same_RV_two_vals.
  assumption.
  assumption.
  
  rewrite cond_not_match_arg; try assumption.
  rewrite mult_zero_left.
  rewrite cpr_eqE.
  rewrite eqr_divrMr.
  rewrite mult_zero_left.
  rewrite <- pfwd1_pairA.
  rewrite <- pfwd1_pairA.
  apply pfwd1_domin_RV1 with (TX := X) (TY := [% Z, [% Y, Z, Z]]).
  rewrite -> pfwd1_pairCA.
  rewrite <- pfwd1_pairA.
  apply pfwd1_domin_RV1.
  apply pfwd1_domin_RV1.
  apply same_RV_two_vals.
  apply nesym.
  assumption.
  assumption.
Qed.

End GeneralLemmas.

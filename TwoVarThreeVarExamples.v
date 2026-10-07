From mathcomp Require Import ssreflect ssrfun ssrbool eqtype fintype bigop.
From Stdlib Require Import Reals.
(* Require Import Arith. *)
From infotheo.probability Require Import proba fdist. (* fsdist jfdist_cond. *)
Require Import List.
Import ListNotations.
From mathcomp Require Import reals.
From mathcomp Require Import all_ssreflect all_algebra fingroup lra ssralg.
From mathcomp Require Import unstable mathcomp_extra reals exp.
(* Require Import ssr_ext ssralg_ext bigop_ext realType_ext realType_ln. *)
From infotheo Require Import ssr_ext ssralg_ext bigop_ext realType_ext realType_ln.
Require Import Classical.
Require Import Field.
(* Require Import Lia. *)

From project Require Import GeneralFormulas.

Local Open Scope ring_scope.
Local Open Scope reals_ext_scope.
Local Open Scope fdist_scope.
Local Open Scope proba_scope.

(*
OUTLINE:
Graph T -> H (Section TwoVarExample)
- *prob_version_wo_indp* states that P[H|T] = P[H|do(T)],
  assuming that some probabilities are non-zero, and that
  unobserved distributions are independent.
  In other words, under interventional treatment, and
  observation of the treatement health outcomes are the
  same (so a RCT where we assign T would be valid for
  learning the interventional probability).
  This is basically complete, the only missing lemma is:
  + *inde_RV_comp*, which is pulled directly from the 
  infotheo library (and proven there), but for whatever 
  reason I'm struggling to access it.
- *doint_equiv_wo_indp* states that E[H|T] = E[H|do(T)] 
  with the same assumptions as in the probability case, and 
  also with the assumption that the function that maps the 
  outcomes to real numbers is injective.
  Work left:
  + *change_to_R_version* is not proven. I'm running into
    issues with type mismatches (realType and finType). This
    seems like it is potentially rather difficult to fix,
    since the type mismatch means I can't use their lemmas.
Graph O -> T -> H, O -> H (confounder, Section ThreeVarConfounderExample)
- doint_equiv_with_confounder_prob states that
  P[H|T,O] = P[H|do(T),O], but has the assumption
  (Hnodefnint t) _|_ Tnodefn | Cnodefn, as well as some
  assumptions about certain probabilities being non-zero.
  Almost done. Work left:
  + 2 lemmas that assert basic arithmetic facts, 
    *zero_div_zero* and *div_num_and_denom*
- doint_equiv_with_confounder_prob_wo_indp states
  the same thing, but now instead assumes that
  UT, UT, UO are mutually independent instead of the
  independence assumption in the previous lemma.
  Work left:
  + Lots of gaps between this proof and the one above.
Graph T -> H, T -> O <- H (collider) 
- Done
Graph T -> O -> H, T -> H (mediator, Section ThreeVarColliderExample)
- Done
General case
- Will be done in new file but rough sketch is here:
  Theorem:
    set Z d-separates H and T ->
    underlying variables for set Z, H, T are all mutually independent ->
    P[H|T,Z] = P[H|do(T),Z].
  This is the general theorem that states that if we
  satisfy the backdoor criterion, then we can use
  observational probabilities to learn about interventional
  probabilities.

  Lemma:
    underlying variables for set Z, H, T are all mutually independent ->
    T _|_ H | Z
  
  Lemma:
    T _|_ H | Z ->
    Tnodefn _|_ Hnodefnint | Znodefns

  Lemma:
    T _|_ H | Z ->
    P[Z] != 0 -> P [T|Z] != 0 ->
    P [H | Z] = P [H | T, Z].
*)

Section TwoVarExample. (* Graph: T -> H *)

Context {R : realType}.
Variables (UT UH : finType).
Variables (outcomes: finType).
Variable P : R.-fdist (UT * UH).
(* Variables (UTRV : {RV P -> UT}) (UHRV : {RV P -> UH}). *)
Variable fT : UT -> outcomes.
Variable fH : UH -> outcomes -> outcomes.
Let T (p : UT * UH ): outcomes :=
  fT p.1.
Let Hinterv (p : UT * UH) t : outcomes :=
  fH p.2 t. 
Let H (p : UT * UH) : outcomes :=
  fH p.2 (T p).
Let Hnodefn : {RV P -> outcomes} :=
  fun u => H u.
Type Hnodefn : {RV P -> outcomes}.
Let Hnodefnint (t:outcomes) : {RV P -> outcomes} :=
  fun u => Hinterv u t.
Let Tnodefn : {RV P -> outcomes} :=  (*T.*)
  fun u => T u.

Variable fn_outcomes_R : outcomes -> GRing.regular R.
Let RHnodefn : {RV P -> GRing.regular R} :=
  fn_outcomes_R `o Hnodefn.
Let RHnodefnint (t:outcomes) : {RV P -> GRing.regular R} :=
  fn_outcomes_R `o (Hnodefnint t).
Let RTnodefn : {RV P -> GRing.regular R} :=
  fn_outcomes_R `o Tnodefn.
Let UTRV: {RV P -> UT} :=
  fun u => u.1.
Let UHRV: {RV P -> UH} :=
  fun u => u.2.

(* Probability lemma with stronger assumption than desired *)
Lemma prob_version: forall t,
  P |= (Hnodefnint t) _|_ Tnodefn ->
  `Pr[ Tnodefn = t ] != 0 ->
  forall a, `Pr[ Hnodefn = a | Tnodefn = t] = `Pr[ (Hnodefnint t) = a].
Proof.
  intros.
  pose proof (indep_then_cond_irrelevant Tnodefn (Hnodefnint t) H0 t H1 a) as H3.
  rewrite H3.
  unfold Hnodefn.
  unfold H.
  unfold Tnodefn.
  unfold T.
  unfold Hnodefnint.
  unfold Hinterv.
  rewrite cpr_eqE.
  rewrite cpr_eqE.
  unfold Tnodefn in H1.
  unfold T in H1.
  eapply eqr_divrMr. assumption.
  rewrite div_mult; try assumption.

  rewrite !pfwd1E /Pr.
  apply: eq_bigl=> a0.
  rewrite !inE.
  rewrite xpair_eqE.
  rewrite xpair_eqE.
  case Ht : (fT a0.1 == t).
  - move/eqP : Ht => Ht.
    rewrite Ht.
    reflexivity.
  - rewrite !andbF.
    reflexivity.
Qed.

(* If the unobserved terms are independent, then the nodefns are
   independent on the intervention graph *)
Lemma indep_implication: forall t,
  P |= UHRV _|_ UTRV ->
  P |= (Hnodefnint t) _|_ Tnodefn.
Proof.
  intros.
  unfold Hnodefnint.
  unfold Hinterv.
  unfold Tnodefn.
  unfold T.
  pose proof (inde_RV_comp (fun u => fH u t) (fun u => fT u) H0).
  unfold comp_RV in H1. 
  unfold UTRV in H1.
  unfold UHRV in H1.
  apply H1.
Qed.

(* The probability lemma without independence, which is what 
   we are after.
   If the unobserved factors are independent, and some
   probability isn't 0, then if we are observe T then the
   probability is equal to if we intervene on T. We denote
   P[H=a|do(T=t)] as P[Hint=a] since if we write out 
   probabilities, do(T=t) change the node functions depending
   on T, which in this case is H, but doesn't actually have an
   extra probability associated with doing (T=t). *)
Lemma prob_version_wo_indp: forall (t : outcomes), 
  P |= UHRV _|_ UTRV ->
  `Pr[ Tnodefn = t ] != 0 ->
  forall a, `Pr[ Hnodefn = a | Tnodefn = t] = `Pr[ (Hnodefnint t) = a].
Proof.
  intros.
  apply prob_version.
  apply indep_implication.
  assumption.
  assumption.
Qed.

Lemma two_var_backdoor_adjustment: forall (t : outcomes), 
  P |= UHRV _|_ UTRV ->
  `Pr[ Tnodefn = t ] != 0 ->
  forall a, `Pr[ (Hnodefnint t) = a] = `Pr[ Hnodefn = a | Tnodefn = t].
Proof.
  intros.
  apply esym.
  apply prob_version_wo_indp; assumption.
Qed.

Print Assumptions two_var_backdoor_adjustment.

End TwoVarExample.



Section ThreeVarConfounderExample. (* C -> T -> H, C -> H *)

Context {R : realType}.

Variables (UT UH UC : finType).
Variable P : R.-fdist ((UC * UT) * UH).
Variable outcomes: finType.

Variable fC : UC -> outcomes.
Variable fT : UT -> outcomes -> outcomes.
Variable fH : UH -> outcomes -> outcomes -> outcomes.

Let C (p: UC * UT * UH) : outcomes :=
  fC p.1.1.
Let T (p : UC * UT * UH ): outcomes :=
  fT p.1.2 (C p).
Let H (p : UC * UT * UH) : outcomes :=
  fH p.2 (C p) (T p).
Let Hinterv (p : UC * UT * UH) t : outcomes :=
  fH p.2 (C p) t.  

Let Cnodefn : {RV P -> outcomes} :=
  fun u => C u.
Let Tnodefn : {RV P -> outcomes} :=
  fun u => T u.
Let Hnodefn : {RV P -> outcomes} :=
  fun u => H u.
Let Hnodefnint (t: outcomes) : {RV P -> outcomes}:= 
  fun u => Hinterv u t.

Let UTRV: {RV P -> UT} :=
  fun u => u.1.2.
Let UHRV: {RV P -> UH} :=
  fun u => u.2.
Let UCRV: {RV P -> UC} :=
  fun u => u.1.1.

(* Lemma joint_then_cond_nonzero: forall {A B : finType} (X : {RV P -> A})
  (Y : {RV P -> B}) x,
  (forall y, `Pr[ [% X, Y] = (x, y)] != 0) ->
  (forall y, `Pr[ X = x | Y = y ] != 0).
Proof.
  intros.
  specialize (H0 y).
Admitted. *)

(* Another definition of indepedence. I wrote it because I needed
   this for the 2 variable case, but I actually think it was already
   defined for condition indepence in cinde_alt, and I should change
   this to cinde_alt at some point instead. *)
Lemma indep_then_cond_irrelevant_wcond: 
  forall (TX TY TZ: finType) (P: R.-fdist ((TY*TX)*TZ) ) (X Y Z: {RV P -> outcomes}),
  Z _|_ X | Y->
  forall y, `Pr[ Y = y ] != 0 ->
  forall x, `Pr[ X = x | Y = y ] != 0 ->
  forall z, `Pr[ Z = z | Y = y] = `Pr[ Z = z | [%X, Y] = (x, y) ].
Proof.
  intros.
  unfold cinde_RV in H0.
  specialize (H0 z x y).
  
  rewrite [in RHS] cpr_eqE.
  apply eqr_divrMr in H0; cycle 1. assumption.
  rewrite <- H0.
  rewrite cpr_eqE.
  rewrite cpr_eqE.
  rewrite pfwd1_pairA.
  set `Pr[ [% Z, X, Y] = (z, x, y) ] as Pxyz.
  rewrite div_num_and_denom.
  reflexivity.
  assumption.
  assumption.
Qed.

(* Lemma prob_cond_simplify: forall h t c,
  `Pr[ (fun u : UC * UT * UH => fH u.2 (fC u.1.1) (fT u.1.2 (fC u.1.1))) = h | 
      [% fun u : UC * UT * UH => fT u.1.2 (fC u.1.1), 
      fun u : UC * UT * UH => fC u.1.1] = (t, c) ] =
  `Pr[ (fun u : UC * UT * UH => fH u.2 c t) = h | 
      [% fun u : UC * UT * UH => fT u.1.2 (fC u.1.1), 
      fun u : UC * UT * UH => fC u.1.1] = (t, c) ]. *)

Lemma cond_then_joint_zero: forall (A B : {RV P -> outcomes}) (a b : outcomes), 
  `Pr[ A = a ] != 0 ->
  `Pr[ B = b | A = a ] != 0 ->
  `Pr[ [% B, A] = (b, a) ] != 0.
Proof.
  intros.
  rewrite cpr_eqE in H1.
  case PBA : (`Pr[ [% B, A] = (b, a) ] == 0).
  move/eqP in PBA.
  rewrite PBA in H1.
  pose proof (zero_div_zero `Pr[ A = a ] H0).
  rewrite H2 in H1.
  rewrite eq_refl in H1.
  exact H1.
  rewrite <- PBA.
  move/eqP in PBA.
  apply/negP.
  move/eqP.
  assumption.
Qed.

(* If we have that nodefunctions are independent, then on 
   the graph
   C -> T -> H, C -> H
   we get that once we condition on C, the observational
   and interventional probability distributions for H
   are the same.
   This is a precursor to the stronger theorem that instead
   assumes the unobserved variables are mutually independent. *)
Lemma doint_equiv_with_confounder_prob: forall t c, 
  (Hnodefnint t) _|_ Tnodefn | Cnodefn ->
  `Pr[ Cnodefn = c ] != 0 ->
  `Pr[ Tnodefn = t | Cnodefn = c ] != 0 ->
  (forall h, `Pr[ Hnodefn = h | [% Tnodefn, Cnodefn] = (t, c) ] 
      = `Pr[ (Hnodefnint t) = h | Cnodefn = c ]).
Proof.
  intros.
  pose proof (indep_then_cond_irrelevant_wcond UT UC UH P 
      Tnodefn Cnodefn (Hnodefnint t) H0 c H1 t H2 h).
  rewrite H3.
  
  rewrite cpr_eqE.
  rewrite cpr_eqE.
  eapply eqr_divrMr.
  apply cond_then_joint_zero; assumption.
  rewrite div_mult.
  unfold Hnodefn.
  unfold H.
  unfold Tnodefn.
  unfold T.
  unfold Cnodefn.
  unfold Hnodefnint.
  unfold Hinterv.
  unfold C.
  (* rewrite cpr_eqE.
  rewrite cpr_eqE. *)
  unfold Tnodefn in H1.
  unfold T in H1.
  (* eapply eqr_divrMr. *)
    (* rewrite cpr_eqE in H2. *)
    (* admit. *)
  (* rewrite div_mult. try assumption. *)

  rewrite !pfwd1E /Pr.
  apply: eq_bigl=> a.
  rewrite !inE.
  rewrite xpair_eqE.
  rewrite xpair_eqE.
  rewrite xpair_eqE.
  rewrite xpair_eqE.
  case Hc : (fC a.1.1 == c).
  - move/eqP : Hc => Hc.
    rewrite Hc.
    case Ht : (fT a.1.2 c == t).
    + move/eqP : Ht => Ht.
      rewrite Ht.
      reflexivity.
    + rewrite !andbF.
    reflexivity.
  - rewrite !andbF.
    reflexivity.
  apply cond_then_joint_zero; assumption.
Qed.

Lemma pfwd1_comp_in_joint: 
  forall {TA TD UA UD : finType}
  (X : {RV P -> TA}) (Z: {RV P -> TD})
  (f : TA -> UA) (x: TA) z,
  injective f ->
  `Pr[ [% (f `o  X), Z] = ((f x), z) ] = `Pr[ [% X, Z] = (x, z) ].
Proof.
  intros.
  (* unfold RV2. *)
  set g := (fun p:(TA * TD) => (f p.1, p.2)).
  assert (injective g).
    unfold injective.
    intros.
    destruct x1 as [xa xd].
    destruct x2 as [xa' xd'].
    unfold g in H1.
    inversion H1.
    unfold injective in H0.
    specialize (H0 xa xa').
    apply H0 in H3.
    rewrite H3.
    reflexivity.
  assert (g `o [% X, Z] = [% (f `o X), Z]).
    unfold comp_RV.
    unfold g.
    unfold RV2. 
    simpl.
    reflexivity.
  assert (g (x, z) = (f x, z)).
    unfold g.
    simpl.
    reflexivity.
  rewrite <- H2.
  rewrite <- H3.
  rewrite -> pfwd1_comp with (f := g) (X := [% X, Z]) (a := (x, z)).
  reflexivity.
  assumption.
Qed.

Lemma cinde_fn_transform:
  forall {TA TB TD UA UB UD : finType}
  (X : {RV P -> TA}) (Y : {RV P -> TB}) (Z: {RV P -> TD})
  (f : (TA*TD) -> UA) (g : (TB*TD) -> UB) (h : TD -> UD),
  injective f ->
  injective g ->
  injective h ->
  [% X, Z] _|_ [% Y, Z ] | Z ->
  f `o [% X, Z] _|_ g `o [% Y, Z ] | (h `o Z).
Proof.
  intros.
  unfold cinde_RV.
  intros.

  have [Hzero | Hnonzero] := boolP (`Pr[(h `o Z) = c] == 0).
    move/eqP: Hzero => Hz'.
    rewrite !cpr_eq0_denom; try assumption.
    rewrite mult_zero_left.
    reflexivity.
  
  destruct (classic  (exists xz, f xz = a)) as [ [xz Hf] | Hfnotin ].
  destruct (classic  (exists yz, g yz = b)) as [ [yz Hg] | Hgnotin ].
  destruct (classic  (exists z, h z = c)) as [ [z Hh] | Hhnotin ].
  rewrite <- Hf.
  rewrite <- Hg.
  rewrite <- Hh.
  rewrite !cpr_eqE.
  rewrite pfwd1_comp; try assumption.
  destruct xz as [xf zf].
  destruct yz as [yg zg].
  rewrite !pfwd1_comp_in_joint; try assumption.

  rewrite [in RHS] pfwd1_pairC.
  unfold swap.
  simpl.
  rewrite pfwd1_comp_in_joint; try assumption.
  rewrite [in RHS] pfwd1_pairC.
  unfold swap.
  simpl.
  rewrite -> pfwd1_pairC with (TY := [% Y, Z]).
  unfold swap.
  simpl.
  rewrite pfwd1_comp_in_joint; try assumption.
  rewrite -> pfwd1_pairC with (TX := [% Y, Z]).
  unfold swap.
  simpl.
  
  rewrite <- cpr_eqE with (X := [% X, Z]) (Y := Z).
  rewrite <- cpr_eqE.
  unfold cinde_RV in H3.
  
  rewrite <- pfwd1_pairA.
  rewrite pfwd1_comp_in_joint; try assumption.
  rewrite -> pfwd1_pairA with (TX := [% X, Z]) (TY := (g `o [% Y, Z])) 
      (TZ := (h `o Z)) (a:= (xf, zf)).
  rewrite -> pfwd1_pairC with (TY := [% X, Z, (g `o [%Y, Z])]).
  unfold swap.
  simpl.
  rewrite pfwd1_comp_in_joint; try assumption.
  rewrite -> pfwd1_pairC with (TX := [% X, Z, (g `o [%Y, Z])]).
  unfold swap.
  simpl.
  rewrite <- pfwd1_pairA.
  rewrite -> pfwd1_pairCA.
  rewrite pfwd1_comp_in_joint; try assumption.
  rewrite -> pfwd1_pairCA with (TX := [% Y, Z]) (TY := [% X, Z]) 
      (TZ := Z).
  rewrite -> pfwd1_pairA.
  rewrite <- cpr_eqE.

  specialize (H3 (xf, zf) (yg, zg) z).
  exact H3.

  pose proof (no_fn_val_prob_zero Z _ _ Hhnotin).
  rewrite H4 in Hnonzero.
  move/eqP: Hnonzero.
  intros.
  contradiction.

  pose proof (no_fn_val_prob_zero [% Y, Z] _ _ Hgnotin).
  rewrite !cpr_eqE.
  pose proof (pfwd1_domin_RV2 (h `o Z) c H4).
  pose proof (pfwd1_domin_RV1 (f `o [% X, Z]) a H5).
  rewrite H5.
  rewrite pfwd1_pairA in H6.
  rewrite H6.
  rewrite zero_div_zero.
  rewrite mult_zero_right.
  reflexivity.
  assumption.
  
  pose proof (no_fn_val_prob_zero [% X, Z] _ _ Hfnotin).
  rewrite !cpr_eqE.
  pose proof (pfwd1_domin_RV2 (h `o Z) c H4).
  pose proof (pfwd1_domin_RV2 (g `o [% Y, Z]) b H4).
  pose proof (pfwd1_domin_RV2 (h `o Z) c H6).
  rewrite H5.
  rewrite H7.
  rewrite zero_div_zero.
  rewrite mult_zero_left.
  reflexivity.
  assumption.
Qed.

Lemma inj_Hnodefnintt_formulations: forall t,
  (exists t' : UT, True) ->
  injective (Hnodefnint t) ->
  injective (fun u : UH * UC => fH u.1 (fC u.2) t).
Proof.
  intros.
  unfold Hnodefnint in H1.
  unfold Hinterv in H1.
  unfold C in H1.
  unfold injective.
  unfold injective in H1.
  intros.
  destruct x1 as [x1h x1c].
  destruct x2 as [x2h x2c].
  simpl in H2.
  destruct H0 as [t' _].
  specialize (H1 (x1c, t', x1h) (x2c, t', x2h)).
  simpl in H1.
  apply H1 in H2.
  inversion H2.
  reflexivity.
Qed.

Lemma inj_Tnodefn_formulations:
  (exists h : UH, True) ->
  injective (fun u' : UC * UT * UH => fT u'.1.2 (fC u'.1.1)) ->
  injective (fun u : UT * UC => fT u.1 (fC u.2)).
Proof.
  intros.
  unfold injective.
  unfold injective in H1.
  intros.
  destruct x1 as [x1t x1c].
  destruct x2 as [x2t x2c].
  simpl in H2.
  destruct H0 as [h _].
  specialize (H1 (x1c, x1t, h) (x2c, x2t, h)).
  simpl in H1.
  apply H1 in H2.
  inversion H2.
  reflexivity.
Qed.

Lemma inj_Cnodefn_formulations:
  (exists t : UT, True) ->
  (exists h : UH, True) ->
  injective (fun u : UC * UT * UH => fC u.1.1) ->
  injective fC.
Proof.
  intros.
  unfold injective.
  intros.
  unfold injective in H2.
  destruct H0 as [t _].
  destruct H1 as [h _].
  specialize (H2 (x1, t, h) (x2, t, h)).
  simpl in H2.
  apply H2 in H3.
  inversion H3.
  reflexivity.
Qed.

(* Lemma removing previous stricter condition, claiming
   that if we start with mutual independence and some 
   injectivity and non-zero set properties, then we get
   the conditional independence condition that was used
   in doint_equiv_with_confounder_prob lemma. *)
Lemma mut_unobs_indp_cond_indp: forall t, 
  mutual_indep_three UHRV UTRV UCRV ->
  injective (Hnodefnint t) ->
  injective Tnodefn ->
  injective Cnodefn ->
  (exists h : UH, True) ->
  (exists t : UT, True) ->
  (Hnodefnint t) _|_ Tnodefn | Cnodefn.
Proof.
  intros.
  apply mut_indp_cond_indp in H0.
  apply indp_not_affected_by_adding_cond in H0.
  unfold Hnodefnint.
  unfold Hinterv.
  unfold Tnodefn.
  unfold T.
  unfold Cnodefn.
  unfold C.
  assert (injective (fun u : UH * UC => fH u.1 (fC u.2) t)).
    apply inj_Hnodefnintt_formulations; assumption.
  assert (injective (fun u : UT * UC => fT u.1 (fC u.2))).
    unfold Tnodefn in H2.
    unfold T in H2.
    unfold C in H2. 
    apply inj_Tnodefn_formulations; assumption.
  assert (injective fC).
    unfold Cnodefn in H3.
    unfold C in H3.
    apply inj_Cnodefn_formulations; assumption.
  pose proof (cinde_fn_transform UHRV UTRV UCRV 
      (fun u => fH u.1 (fC u.2) t) 
      (fun u => fT u.1 (fC u.2))
      (fun u => fC u)
      H6 H7 H8 H0) as Hcindp.
  unfold comp_RV in Hcindp. 
  simpl in Hcindp.
  (* rewrite fn_same_TC in H7.
  rewrite fn_same_HC in H7. *)
  unfold UCRV in Hcindp.
  unfold UTRV in Hcindp.
  unfold UHRV in Hcindp.
  simpl.
  exact Hcindp.
Qed. 


(* If we have mutual independence, then on the graph
   C -> T -> H, C -> H
   we get that once we condition on C, the observational
   and interventional probability distributions for H
   are the same. *)
Lemma doint_equiv_with_confounder_prob_wo_indp: forall t c, 
  mutual_indep_three UHRV UTRV UCRV ->
  injective (Hnodefnint t) ->
  injective Tnodefn ->
  injective Cnodefn ->
  (exists h : UH, True) ->
  (exists t : UT, True) ->
  `Pr[ Cnodefn = c ] != 0 ->
  `Pr[ Tnodefn = t | Cnodefn = c ] != 0 ->
  (forall h, `Pr[ Hnodefn = h | [% Tnodefn, Cnodefn] = (t, c) ] 
      = `Pr[ (Hnodefnint t) = h | Cnodefn = c ]).
Proof.
  intros. 
  apply doint_equiv_with_confounder_prob; try assumption.
  apply mut_unobs_indp_cond_indp; assumption. 
Qed.

(* REWORKING CONFOUNDER EXAMPLE TO NOT HAVE INJECTIVITY *)

Lemma mult_factor_in_sum: forall {TD: finType} (k : R) (z' : {set TD})
  {U : finType} {P0 : R.-fdist U} (Z : {RV (P0) -> (TD)}),
  \sum_(a <- enum z') (k * `Pr[Z = a]) = k * \sum_(a <- enum z') `Pr[Z = a].
Proof.
  intros.
  rewrite big_distrr.
  simpl.
  reflexivity.
Qed.

Lemma div_factor_in_sum: forall {TD: finType} (k : R) (z' : {set TD})
  {U : finType} {P0 : R.-fdist U} (Z : {RV (P0) -> (TD)}),
  \sum_(a <- enum z') (`Pr[Z = a] / k) = (\sum_(a <- enum z') `Pr[Z = a]) / k.
Proof.
  intros.
  rewrite big_distrl.
  simpl.
  reflexivity.
Qed.
 
Lemma sets_are_sums: forall {TA : finType} (A: {set TA})
  {U : finType} {P0 : R.-fdist U} (X : {RV (P0) -> (TA)}),
  `Pr[ X \in A ] = \sum_(a <- enum A) `Pr[ X = a ].
Proof.
  intros.
  rewrite pr_inE'.
  rewrite /Pr.
  rewrite big_enum.
  simpl.
  apply eq_bigr.
  intros.
  apply dist_of_RVE.
Qed.

(* setX change *)
Lemma enum_pair_is_seq_pair: forall {TA TB : finType} (A : {set TA}) (B : {set TB}),
  perm_eq [seq (i1, i2) | i1 <- enum A, i2 <- enum B] (enum (setX A B)).
Proof.
  intros.
  apply/uniq_perm.

  apply/allpairs_uniq.
  apply enum_uniq.
  apply enum_uniq.
  move=> x y Hx Hy.
  rewrite /uncurry.
  destruct x as [x1 x2].
  destruct y as [y1 y2].
  intros.
  assumption.
  apply enum_uniq.

  move=> [a b].
  rewrite !mem_enum.
  rewrite inE.
  simpl.
  apply/idP/idP.

  intros.
  move/allpairsP in H0.
  move: H0 => [p [/= Hp1 Hp2 Heq]].
  inversion Heq.
  rewrite mem_enum in Hp1.
  rewrite mem_enum in Hp2.
  apply/andP.
  split; assumption.

  intros.
  move/andP: H0 => [Ha Hb].
  fold prod_enum.
  apply/allpairsP.
  exists (a, b).
  simpl.
  split.
  rewrite mem_enum.
  assumption.
  rewrite mem_enum.
  assumption.
  reflexivity.
Qed.

(* setX change *)
Lemma singleton_and_set_in_cond_seq: forall {TA TB : finType} (x : TA) 
  (z' : {set TB}),
  perm_eq (enum (setX [set x] z')) [seq (x, i) | i <- enum z'].
Proof.
  intros.
  apply/uniq_perm.
  apply enum_uniq.
    assert (uniq [seq (x, i)  | i <- enum z'] = uniq (enum z')).
      apply map_inj_in_uniq.
      move=> i j _ _ /=.
      intros.
      inversion H0.
      reflexivity.
    rewrite H0.
    apply enum_uniq.

  move=> [a b].
  rewrite !mem_enum.
  rewrite inE.
  simpl.
  apply/idP/idP.
  intros.
  move/andP: H0 => [Ha Hb].
  rewrite inE in Ha.
  move/eqP in Ha.
  rewrite Ha.
  rewrite mem_map.
  rewrite mem_enum.
  exact Hb.
  unfold injective.
  intros.
  inversion H0.
  reflexivity.

  case H0 : (a == x).
  move/eqP in H0.
  rewrite H0.
  rewrite -> mem_map with (f := [eta pair x]) (s := (enum z')).
  rewrite mem_enum.
  intros.
  apply/andP.
  split.
  apply b_in_set_b.
  assumption.
  unfold injective.
  intros.
  inversion H1.
  reflexivity.

  move/eqP in H0.
  intros.
  move/mapP in H1.
  case: H1 => x' Hx1 Hx2.
  inversion Hx2.
  rewrite H2 in H0.
  contradiction.
Qed.

(* setX change *)
Lemma singleton_and_set_in_cond_seq2: forall {TA TB : finType} (x : TA) 
  (z' : {set TB}),
  perm_eq (enum (setX z' [set x])) [seq (i, x) | i <- enum z'].
Proof.
  intros.
  apply/uniq_perm.
  apply enum_uniq.
    assert (uniq [seq (i, x)  | i <- enum z'] = uniq (enum z')).
      apply map_inj_in_uniq.
      move=> i j _ _ /=.
      intros.
      inversion H0.
      reflexivity.
    rewrite H0.
    apply enum_uniq.

  move=> [a b].
  rewrite !mem_enum.
  rewrite inE.
  simpl.
  apply/idP/idP.
  intros.
  move/andP: H0 => [Ha Hb].
  rewrite inE in Hb.
  move/eqP in Hb.
  rewrite Hb.
  rewrite mem_map.
  rewrite mem_enum.
  exact Ha.
  unfold injective.
  intros.
  inversion H0.
  reflexivity.

  case H0 : (b == x).
  move/eqP in H0.
  rewrite H0.
  rewrite -> mem_map with (f := (pair^~ x)) (s := (enum z')).
  rewrite mem_enum.
  intros.
  apply/andP.
  split.
  assumption.
  apply b_in_set_b.
  unfold injective.
  intros.
  inversion H1.
  reflexivity.

  move/eqP in H0.
  intros.
  move/mapP in H1.
  case: H1 => x' Hx1 Hx2.
  inversion Hx2.
  rewrite H3 in H0.
  contradiction.
Qed.

(* setX change *)
Lemma product_of_sums: forall {TA TB TC TD: finType} (A : {set TA})
  (B : {set TB}) (f : TA -> R) (g : TB -> R),
  (\sum_(a <- enum A) f a) * (\sum_(b <- enum B) g b) = 
    \sum_(c <- enum (setX A B)) (f c.1) * (g c.2).
Proof.
  intros.
  rewrite big_distrr.
  simpl.
  assert (forall i, true -> (\sum_(a <- enum A)  f a) * g i = (\sum_(a <- enum A)  f a * g i)).
    intros.
    rewrite big_distrl.
    simpl.
    reflexivity.
  rewrite -> eq_bigr with (F2 := (fun i => \sum_(a <- enum A)  f a * g i)); try assumption.
  rewrite exchange_big.
  
  simpl.
  assert (\sum_(j <- enum A)  \sum_(i <- enum B)  f j * g i = 
      \sum_(j <- enum A)  \sum_(i <- enum B)  (fun p => f p.1 * g p.2) (j, i)).
    apply eq_bigr.
    intros.
    apply eq_bigr.
    intros.
    simpl.
    reflexivity.
  rewrite -[RHS](big_allpairs (r1 := enum A) (r2 := enum B) 
      (F := fun p : TA * TB => f p.1 * g p.2)) in H1.
  simpl in H1.
  rewrite H1.
  apply perm_big.
  apply enum_pair_is_seq_pair.
Qed.

(* setX change *)
Lemma removing_singleton_from_sum: forall {TA TB : finType} (x : TA) 
  (z' : {set TB}) (f : (TA * TB) -> R),
  \sum_(i in (setX [set x] z')) f i = \sum_(i in z') f (x, i).
Proof.
  intros.
  rewrite -[RHS]big_enum.
  rewrite -[LHS]big_enum.
  simpl.
  pose proof (singleton_and_set_in_cond_seq x z').
  pose proof (perm_big (op := (GRing.Algebra_add__canonical__Monoid_Law R)) (x := 0) ([seq (x, i)  | i <- enum z']) (F := f) (P := predT) H0).
  simpl in H1.
  rewrite H1.
  rewrite big_map.
  reflexivity.
Qed.

(* setX change *)
Lemma removing_singleton_from_sum2: forall {TA TB : finType} (x : TA) 
  (z' : {set TB}) (f : (TB * TA) -> R),
  \sum_(i in (setX z' [set x])) f i = \sum_(i in z') f (i, x).
Proof.
  intros.
  rewrite -big_enum.
  rewrite -big_enum.
  simpl.
  pose proof (singleton_and_set_in_cond_seq2 x z').
  pose proof (perm_big (op := (GRing.Algebra_add__canonical__Monoid_Law R)) (x := 0) ([seq (i, x)  | i <- enum z']) (F := f) (P := predT) H0).
  simpl in H1.
  rewrite H1.
  rewrite big_map.
  reflexivity.
Qed.

(* Introduces classic assumption *)
Lemma pr_in_comp_sets: forall {U : finType} {P0 : R.-fdist U}
  (A B : finType) (X : {RV (P0) -> (A)})
  (f : A -> B) (B' : {set B}) (A' : {set A}),
  (forall (a : A), a \in A' -> f a \in B') ->
  (forall (a : A), not (a \in A') -> not (f a \in B')) ->
  `Pr[ (f `o  X) \in B' ] = `Pr[ X \in A' ].
Proof.
  intros.
  rewrite pr_in_comp'.
  assert (A' = (f @^-1: B')).
    apply/setP => a.
    rewrite inE.
    apply/idP/idP.
    specialize (H0 a).
    assumption.
    specialize (H1 a).
    intros.
    apply NNPP.
    intro H3.
    apply H1 in H3.
    contradiction.
  rewrite H2.
  reflexivity.
Qed.

Lemma pfwd1_comp_sets: forall {U : finType} {P0 : R.-fdist U}
  (A B : finType) (X : {RV (P0) -> (A)})
  (f : A -> B) (b : B) (A' : {set A}),
  (forall (a : A), a \in A' -> f a = b) ->
  (forall (a : A), not (a \in A') -> f a != b) ->
  `Pr[ (f `o X) = b ] = `Pr[ X \in A' ].
Proof.
  intros.
  rewrite <- pr_in1.
  apply pr_in_comp_sets.
  intros.
  specialize (H0 a).
  apply H0 in H2.
  rewrite H2.
  apply b_in_set_b.
  intros.
  specialize (H1 a).
  apply H1 in H2.
  rewrite inE.
  apply/negP.
  assumption.
Qed.

Lemma set_A'_always_exists: forall {TD UD : finType} (h : TD -> UD) z,
  exists A' : {set TD},
  (forall a : TD, a  \in A' -> h a = z) /\
  (forall (a : TD), not (a \in A') -> h a != z).
Proof.
  intros.
  exists [set a : TD | h a == z].
  split.
  intros.
  rewrite inE in H0.
  apply/eqP.
  assumption.

  intros.
  rewrite inE in H0.
  apply/negbT.
  apply/negP.
  assumption.
Qed.

(* setX change *)
Lemma pr_in_comp_sets_joint: forall {U : finType} {P0 : R.-fdist U}
  (A B D : finType) (X : {RV (P0) -> (A)}) (Y : {RV (P0) -> (D)})
  (f : A -> B) (b : B) (D': {set D}) (A' : {set A}),
  (forall (a : A), a \in A' -> f a = b) ->
  (forall (a : A), not (a \in A') -> f a != b) ->
  `Pr[ [% (f `o  X), Y] \in ([set b] `* D') ] = `Pr[ [% X, Y] \in (A' `* D') ].
Proof.
  intros.
  pose proof (pfwd1_comp_sets A B X f b A' H0 H1).
  rewrite <- pr_in1 in H2.


  set g := (fun p:(A * D) => (f p.1, p.2)).
  assert (g `o [% X, Y] = [% (f `o X), Y]).
    unfold comp_RV.
    unfold g.
    unfold RV2. 
    simpl.
    reflexivity.

  (* Want `Pr[ g `o [% X, Y] \in blah] = Pr[ x \in A']*)
  rewrite <- H3.
  rewrite -> pr_in_comp_sets with (f := g) (X := [% X, Y]) (A' := (setX A' D')).
  reflexivity.

  intros.
  destruct a as [aa ad].
  unfold g.
  simpl.
  rewrite inE.
  simpl.
  rewrite inE in H4.
  simpl in H4.
  move/andP: H4 => [Haa Had].
  apply/andP.
  split.
  apply H0 in Haa.
  rewrite Haa.
  apply b_in_set_b.
  exact Had.

  intros.
  destruct a as [aa ad].
  unfold g.
  simpl.
  rewrite inE.
  simpl.
  rewrite inE in H4.
  move=> /negP in H4.
  rewrite negb_and in H4.
  simpl in H4.
  apply/negP.
  rewrite negb_and.
  apply/orP.
  case/orP: H4 => Hnot.
  left.
  move/negP: Hnot => Hnot.
  apply H1 in Hnot.
  apply not_b_not_in_set_b.
  assumption.
  right.
  assumption.
Qed.

(* setX change *)
Lemma pfwd1_comp_sets_joint: forall {U : finType} {P0 : R.-fdist U}
  (A B D : finType) (X : {RV (P0) -> (A)}) (Y : {RV (P0) -> (D)})
  (f : A -> B) (b : B) (d: D) (A' : {set A}),
  (forall (a : A), a \in A' -> f a = b) ->
  (forall (a : A), not (a \in A') -> f a != b) ->
  `Pr[ [% (f `o  X), Y] = (b, d) ] = `Pr[ [% X, Y] \in (setX A' [set d]) ].
Proof.
  intros.
  pose proof (pr_in_comp_sets_joint A B D X Y f b [set d] A') H0 H1.
  rewrite <- H2.
  rewrite <- pr_in1 with (X := [% f `o X, Y]).
  rewrite same_singleton_sets.
  reflexivity.
Qed.

Lemma change_to_set_three_way: forall {TA TB TD: finType}
  (X : {RV P -> TA}) (Y : {RV P -> TB}) (Z: {RV P -> TD}), 
  (forall (x : TA) (y : TB) (z : TD),
  `Pr[ X = x ] * `Pr[ Y = y ] * `Pr[ Z = z ] =
  `Pr[ [% X, Y, Z] = (x, y, z) ]) ->
  (forall (x : TA) (y : TB) (z' : {set TD}),
  `Pr[ X = x ] * `Pr[ Y = y ] * `Pr[ Z \in z' ] =
  `Pr[ [% X, Y, Z] \in [set x] `* [set y] `* z' ]).
Proof.
  intros.
  specialize (H0 x y).
  rewrite sets_are_sums.
  rewrite sets_are_sums.
  (* Check big_distrr. *)
  rewrite <- mult_factor_in_sum.
  assert (forall z : TD, true -> `Pr[ X = x ] * `Pr[ Y = y ] * `Pr[ Z = z ] = `Pr[ [% X, Y, Z] = (x, y, z) ]).
    intros.
    specialize (H0 z).
    assumption.
  rewrite -> eq_bigr with (F1 := (fun z => `Pr[ X = x ] * `Pr[ Y = y ] * `Pr[ Z = z ]))
      (F2 := (fun z => `Pr[ [% X, Y, Z] = (x, y, z) ])); try assumption.

  rewrite big_enum.
  rewrite big_enum.
  simpl.
  rewrite same_singleton_sets.
  rewrite -> removing_singleton_from_sum with (x := (x, y)) (z' := z').
  reflexivity.
Qed.

Lemma mut_indp_with_fn: 
  forall {TA TB TD UD : finType}
  (X : {RV P -> TA}) (Y : {RV P -> TB}) (Z: {RV P -> TD}) (h : TD -> UD),
  mutual_indep_three X Y Z ->
  mutual_indep_three X Y (h `o Z).
Proof.
  intros.
  unfold mutual_indep_three.
  intros.
  unfold mutual_indep_three in H0.
  destruct H0 as [Indp3 [IndpXY [IndpYZ IndpXZ]]].
  split.

  intros.
  pose proof (set_A'_always_exists h z).
  case: H0 => A [H0 H1].
  pose proof (change_to_set_three_way X Y Z Indp3) as Indp3'.
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

Lemma can_condition_on_val_or_set:
  forall {TA TB TD : finType}
  (X : {RV P -> TA}) (Y : {RV P -> TB}) (Z: {RV P -> TD}),
  (forall A B c,
    `Pr[ [% X, Y] \in (A `* B) | Z = c ] =
    `Pr[ X \in A | Z = c ] *
    `Pr[ Y \in B | Z = c ]) ->
  (forall A B c,
    `Pr[ [% X, Y] \in (A `* B) | Z \in [set c] ] =
    `Pr[ X \in A | Z \in [set c] ] *
    `Pr[ Y \in B | Z \in [set c] ]).
Proof.
  intros.
  specialize (H0 A B c).
  assumption.
Qed.

Lemma cinde_RV_sets:
  forall {TA TB TD UU : finType} {P' : R.-fdist(UU)}
  (X : {RV P' -> TA}) (Y : {RV P' -> TB}) (Z: {RV P' -> TD}),
  X _|_ Y | Z ->
  (forall A B c,
    `Pr[ [% X, Y] \in (A `* B) | Z = c ] =
    `Pr[ X \in A | Z = c ] *
    `Pr[ Y \in B | Z = c ]).
Proof.
  intros.
  unfold cinde_RV in H0.
  rewrite cpr_inEdiv.
  rewrite cpr_inEdiv.
  rewrite cpr_inEdiv.

  assert (forall (i : TA * TB), true ->
      `Pr[ [% X, Y, Z] = (i.1, i.2, c)] / `Pr[ Z = c ] =
      `Pr[ [% X, Z] = (i.1, c)] / `Pr[ Z = c ] * (`Pr[ [% Y, Z] = (i.2, c)] / `Pr[ Z = c ])).
    intros.
    destruct i as [a b].
    specialize (H0 a b c).
    rewrite !cpr_eqE in H0.
    assumption.

  rewrite sets_are_sums.
  rewrite pr_in1.
  rewrite <- div_factor_in_sum.
  rewrite big_enum.
  simpl.
  rewrite -> removing_singleton_from_sum2 with (z' := setX A B) (x := c).
  rewrite -big_enum.
  simpl.
  rewrite -> eq_bigr with (F1 := (fun i => `Pr[ [% X, Y, Z] = (i.1, i.2, c) ] / `Pr[ Z = c ]))
      (F2 := (fun i => `Pr[ [% X, Z] = (i.1, c) ] / `Pr[ Z = c ] * (`Pr[ [% Y, Z] = (i.2, c) ] / `Pr[ Z = c ]))); try assumption.
  
  rewrite sets_are_sums.
  rewrite <- div_factor_in_sum.
  rewrite sets_are_sums.
  rewrite <- div_factor_in_sum.
  rewrite [in RHS] big_enum.
  simpl.
  rewrite -> removing_singleton_from_sum2 with (z' := A) (x := c).
  rewrite -big_enum.
  simpl.
  assert ((\sum_(a <- enum (setX B [set c])) `Pr[ [% Y, Z] = a ] / `Pr[ Z = c ]) = 
      (\sum_(a <- enum B) `Pr[ [% Y, Z] = (a, c) ] / `Pr[ Z = c ])).
    intros.
    rewrite big_enum.
    rewrite -> removing_singleton_from_sum2 with (z' := B) (x := c).
    rewrite big_enum.
    simpl.
    reflexivity.
  rewrite H2.
  clear H2.

  rewrite product_of_sums; try assumption.
  reflexivity.
Qed.

Lemma cinde_fn_transform':
  forall {TA TB TD UA UB UU : finType} {P' : R.-fdist(UU)}
  (X : {RV P' -> TA}) (Y : {RV P' -> TB}) (Z: {RV P' -> TD})
  (f : (TA*TD) -> UA) (g : (TB*TD) -> UB),
  [% X, Z] _|_ [% Y, Z ] | Z ->
  f `o [% X, Z] _|_ g `o [% Y, Z ] | Z.
Proof.
  intros.
  unfold cinde_RV.
  intros.

  have [Hzero | Hnonzero] := boolP (`Pr[Z = c] == 0).
    move/eqP: Hzero => Hz'.
    rewrite !cpr_eq0_denom; try assumption.
    rewrite mult_zero_left.
    reflexivity.

  pose proof (set_A'_always_exists f a).
  pose proof (set_A'_always_exists g b).
  case: H1 => Af [Hf0 Hf1].
  case: H2 => Ag [Hg0 Hg1].

  rewrite !cpr_eqE.
  rewrite -> pfwd1_comp_sets_joint with (A' := Af); try assumption.
  rewrite -> pfwd1_comp_sets_joint with (A' := Ag); try assumption.

  rewrite <- pr_in1.
  rewrite <- cpr_inEdiv.
  rewrite <- cpr_inEdiv.

  rewrite <- pfwd1_pairA.
  (* rewrite <- pr_in_pairA with (X := (f `o [% X, Z])) (Y := (g `o [% Y, Z])) (Z := Z) (). *)
  rewrite -> pfwd1_comp_sets_joint with (A' := Af) (f := f) (X := [% X, Z]) (Y := [% g `o [% Y, Z], Z]); try assumption.
  assert (setX Af [set (b, c)] = setX Af ([set b] `* [set c])).
    pose proof (same_singleton_sets b c).
    rewrite H1.
    reflexivity.
  rewrite H1.
  rewrite -> pr_in_pairCA with (X := [% X, Z]) (Y := (g `o [% Y, Z])) (Z := Z).
  rewrite -> pr_in_comp_sets_joint with (X := [% Y, Z]) (Y := [% X, Z, Z]) (A' := Ag); try assumption.
  rewrite <- pr_in_pairCA with (X := [% X, Z]) (Y := [% Y, Z]) (Z := Z).
  rewrite -> pr_in_pairA with (X := [% X, Z]) (Y := [% Y, Z]) (Z := Z).
  rewrite <- cpr_inEdiv.

  apply cinde_RV_sets.
  assumption.
Qed.

(* Lemma removing previous stricter condition, claiming
   that if we start with mutual independence and some 
   injectivity and non-zero set properties, then we get
   the conditional independence condition that was used
   in doint_equiv_with_confounder_prob lemma. *)
Lemma mut_unobs_indp_cond_indp_wo_inj: forall t, 
  mutual_indep_three UHRV UTRV UCRV ->
  (Hnodefnint t) _|_ Tnodefn | Cnodefn.
Proof.
  intros.
  unfold Hnodefnint.
  unfold Hinterv.
  unfold Tnodefn.
  unfold T.
  unfold Cnodefn.
  unfold C.
  pose proof (mut_indp_with_fn UHRV UTRV UCRV fC).
  apply mut_indp_cond_indp in H1; try assumption.
  apply indp_not_affected_by_adding_cond in H1.
  pose proof (cinde_fn_transform' UHRV UTRV (fC `o UCRV) (fun u => fH u.1 u.2 t)
    (fun u => fT u.1 u.2) H1).
  unfold comp_RV in H2.
  simpl in H2.
  unfold UHRV in H2.
  unfold UCRV in H2.
  unfold UTRV in H2.
  exact H2.
Qed. 

(* If we have mutual independence, then on the graph
   C -> T -> H, C -> H
   we get that once we condition on C, the observational
   and interventional probability distributions for H
   are the same. *)
Lemma doint_equiv_with_confounder_prob_wo_indp_wo_inj: forall t c, 
  mutual_indep_three UHRV UTRV UCRV ->
  `Pr[ Cnodefn = c ] != 0 ->
  `Pr[ Tnodefn = t | Cnodefn = c ] != 0 ->
  (forall h, `Pr[ Hnodefn = h | [% Tnodefn, Cnodefn] = (t, c) ] 
      = `Pr[ (Hnodefnint t) = h | Cnodefn = c ]).
Proof.
  intros. 
  apply doint_equiv_with_confounder_prob; try assumption.
  apply mut_unobs_indp_cond_indp_wo_inj; assumption. 
Qed.

Lemma three_var_confounder_backdooor_adjustment_eq: forall t c, 
  mutual_indep_three UHRV UTRV UCRV ->
  `Pr[ Tnodefn = t | Cnodefn = c ] != 0 ->
  (forall h, `Pr[ (Hnodefnint t) = h | Cnodefn = c ] = 
      `Pr[ Hnodefn = h | [% Tnodefn, Cnodefn] = (t, c) ]).
Proof.
  intros.
  apply esym.
  apply doint_equiv_with_confounder_prob_wo_indp_wo_inj; try assumption.
  have [Hzero | Hnonzero] := boolP (`Pr[Cnodefn =  c] == 0).
    move/eqP: Hzero => Hz'.
    apply cpr_eq0_denom with (X := Tnodefn) (a := t) in Hz'.
    rewrite Hz' in H1.
    apply false_cant_be in H1.
    assumption.

    exact is_true_true.
Qed.

Lemma three_var_confounder_backdoor_adjustment: forall t,      
  mutual_indep_three UHRV UTRV UCRV ->
  (forall c, `Pr[ Tnodefn = t | Cnodefn = c ] != 0) ->
  (forall h, `Pr[ (Hnodefnint t) = h] =  
  \sum_(c in outcomes) (`Pr[Hnodefn = h | [%Tnodefn, Cnodefn] = (t, c)] * 
      `Pr[ Cnodefn = c ])).
Proof.
  intros.
  under eq_bigr => c _.
    rewrite <- three_var_confounder_backdooor_adjustment_eq; cycle 1; try assumption.
    specialize (H1 c).
    assumption.
    over.
  simpl.
  rewrite -[RHS] marginalize.
  reflexivity.
Qed.

Print Assumptions three_var_confounder_backdoor_adjustment.

End ThreeVarConfounderExample.



Section ThreeVarMediatorExample. (* T -> C -> H, T -> H*)
Context {R : realType}.

Variables (UT UH UC : finType).
Variable P : R.-fdist ((UT * UC) * UH).
Variable outcomes: finType.

Variable fC : UC -> outcomes -> outcomes.
Variable fT : UT -> outcomes.
Variable fH : UH -> outcomes -> outcomes -> outcomes.

Let T (p : UT * UC * UH ): outcomes :=
  fT p.1.1.
Let C (p: UT * UC * UH) : outcomes :=
  fC p.1.2 (T p).
Let H (p : UT * UC * UH) : outcomes :=
  fH p.2 (C p) (T p).
Let Cinterv (p: UT * UC * UH) t : outcomes :=
  fC p.1.2 t.
Let Hinterv (p : UT * UC * UH) t : outcomes :=
  fH p.2 (Cinterv p t) t. 

Let Cnodefn : {RV P -> outcomes} :=
  fun u => C u.
Let Tnodefn : {RV P -> outcomes} :=
  fun u => T u.
Let Hnodefn : {RV P -> outcomes} :=
  fun u => H u.
Let Cnodefnint (t: outcomes) : {RV P -> outcomes}:= 
  fun u => Cinterv u t.
Let Hnodefnint (t: outcomes) : {RV P -> outcomes}:= 
  fun u => Hinterv u t.

Let UTRV: {RV P -> UT} :=
  fun u => u.1.1.
Let UHRV: {RV P -> UH} :=
  fun u => u.2.
Let UCRV: {RV P -> UC} :=
  fun u => u.1.2.

(* Probability lemma with stronger assumption than desired *)
Lemma doint_prob_mediator_w_assump: forall t,
  P |= (Hnodefnint t) _|_ Tnodefn ->
  `Pr[ Tnodefn = t ] != 0 ->
  forall a, `Pr[ Hnodefn = a | Tnodefn = t] = `Pr[ (Hnodefnint t) = a].
Proof.
  intros.
  pose proof (indep_then_cond_irrelevant Tnodefn (Hnodefnint t) H0).
  specialize (H2 t).
  pose proof (H2 H1).
  specialize (H3 a).
  clear H2.
  rewrite H3.
  unfold Hnodefn.
  unfold H.
  unfold Tnodefn.
  unfold Hnodefnint.
  unfold Hinterv.
  unfold C.
  unfold T.
  rewrite cpr_eqE.
  rewrite cpr_eqE.
  unfold Tnodefn in H1.
  unfold T in H1.
  eapply eqr_divrMr. assumption.
  rewrite div_mult; try assumption.

  rewrite !pfwd1E /Pr.
  apply: eq_bigl=> a0.
  rewrite !inE.
  rewrite xpair_eqE.
  rewrite xpair_eqE.
  case Ht : (fT a0.1.1 == t).
  - move/eqP : Ht => Ht.
    rewrite Ht.
    reflexivity.
  - rewrite !andbF.
    reflexivity.
Qed.

Lemma mediator_indpU_indpNF: forall t,
  P |= [% UHRV, UCRV] _|_ UTRV ->
  P |= (Hnodefnint t) _|_ Tnodefn.
Proof.
  intros.
  unfold Hnodefnint.
  unfold Hinterv.
  unfold Cinterv.
  unfold Tnodefn.
  unfold T.
  pose proof (inde_RV_comp 
      (fun u => fH u.1 (fC u.2 t) t) 
      (fun u => fT u) H0).
  unfold comp_RV in H1. 
  unfold UTRV in H1.
  unfold UHRV in H1.
  apply H1.
Qed.

Lemma mediator_mut_indp_to_pair_indp:
  mutual_indep_three UHRV UTRV UCRV ->
  P |= [% UHRV, UCRV] _|_ UTRV.
Proof.
  intros.
  unfold inde_RV.
  unfold mutual_indep_three in H0.
  inversion H0.
  clear H0.
  inversion H2.
  clear H2.
  inversion H3.
  clear H3.
  destruct x as [h c].
  intros.
  specialize (H1 h y c).
  rewrite pfwd1_pairAC.
  unfold inde_RV in H4.
  specialize (H4 h c).
  rewrite H4.
  apply esym.
  rewrite change_ord_mult in H1.
  exact H1.
Qed.

Lemma three_var_mediator_backdoor_adjustment: forall t,
  mutual_indep_three UHRV UTRV UCRV ->
  `Pr[ Tnodefn = t ] != 0 ->
  forall a, `Pr[ Hnodefn = a | Tnodefn = t] = `Pr[ (Hnodefnint t) = a].
Proof.
  intros.
  apply doint_prob_mediator_w_assump.
  apply mediator_indpU_indpNF.
  apply mediator_mut_indp_to_pair_indp.
  exact H0.
  assumption.
Qed.

Print Assumptions three_var_mediator_backdoor_adjustment.
End ThreeVarMediatorExample.



Section ThreeVarColliderExample.
Context {R : realType}.

Variables (UT UH UC : finType).
Variable P : R.-fdist ((UT * UC) * UH).
Variable outcomes: finType.

Variable fC : UC -> outcomes -> outcomes -> outcomes.
Variable fT : UT -> outcomes.
Variable fH : UH -> outcomes -> outcomes.

Let T (p : UT * UC * UH ): outcomes :=
  fT p.1.1.
Let H (p : UT * UC * UH) : outcomes :=
  fH p.2 (T p).
Let C (p: UT * UC * UH) : outcomes :=
  fC p.1.2 (T p) (H p).
Let Hinterv (p : UT * UC * UH) t : outcomes :=
  fH p.2 t. 
Let Cinterv (p: UT * UC * UH) t : outcomes :=
  fC p.1.2 t (Hinterv p t).

Let Cnodefn : {RV P -> outcomes} :=
  fun u => C u.
Let Tnodefn : {RV P -> outcomes} :=
  fun u => T u.
Let Hnodefn : {RV P -> outcomes} :=
  fun u => H u.
Let Cnodefnint (t: outcomes) : {RV P -> outcomes}:= 
  fun u => Cinterv u t.
Let Hnodefnint (t: outcomes) : {RV P -> outcomes}:= 
  fun u => Hinterv u t.

Let UTRV: {RV P -> UT} :=
  fun u => u.1.1.
Let UHRV: {RV P -> UH} :=
  fun u => u.2.
Let UCRV: {RV P -> UC} :=
  fun u => u.1.2.

(* Probability lemma with stronger assumption than desired *)
Lemma doint_prob_collider_w_assump: forall t,
  P |= (Hnodefnint t) _|_ Tnodefn ->
  `Pr[ Tnodefn = t ] != 0 ->
  forall a, `Pr[ Hnodefn = a | Tnodefn = t] = `Pr[ (Hnodefnint t) = a].
Proof.
  intros.
  pose proof (indep_then_cond_irrelevant Tnodefn (Hnodefnint t) H0).
  specialize (H2 t).
  pose proof (H2 H1).
  specialize (H3 a).
  clear H2.
  rewrite H3.
  unfold Hnodefn.
  unfold H.
  unfold Tnodefn.
  unfold Hnodefnint.
  unfold Hinterv.
  unfold C.
  unfold T.
  rewrite cpr_eqE.
  rewrite cpr_eqE.
  unfold Tnodefn in H1.
  unfold T in H1.
  eapply eqr_divrMr. assumption.
  rewrite div_mult; try assumption.

  rewrite !pfwd1E /Pr.
  apply: eq_bigl=> a0.
  rewrite !inE.
  rewrite xpair_eqE.
  rewrite xpair_eqE.
  case Ht : (fT a0.1.1 == t).
  - move/eqP : Ht => Ht.
    rewrite Ht.
    reflexivity.
  - rewrite !andbF.
    reflexivity.
Qed.

Lemma collider_mut_indp_to_pair_indp:
  mutual_indep_three UHRV UTRV UCRV ->
  P |= UHRV _|_ UTRV.
Proof.
  intros.
  unfold mutual_indep_three in H0.
  inversion H0.
  clear H0.
  inversion H2.
  assumption.
Qed.

Lemma collider_indpU_indpNF: forall t,
  P |= UHRV _|_ UTRV ->
  P |= (Hnodefnint t) _|_ Tnodefn.
Proof.
  intros.
  unfold Hnodefnint.
  unfold Hinterv.
  unfold Tnodefn.
  unfold T.
  pose proof (inde_RV_comp (fun u => fH u t) (fun u => fT u) H0).
  unfold comp_RV in H1. 
  unfold UTRV in H1.
  unfold UHRV in H1.
  apply H1.
Qed.

Lemma doint_collider: forall t,
  mutual_indep_three UHRV UTRV UCRV ->
  `Pr[ Tnodefn = t ] != 0 ->
  forall a, `Pr[ Hnodefn = a | Tnodefn = t] = `Pr[ (Hnodefnint t) = a].
Proof. 
  intros.
  apply doint_prob_collider_w_assump.
  apply collider_indpU_indpNF.
  apply collider_mut_indp_to_pair_indp.
  exact H0.
  assumption.
Qed.

Lemma three_var_collider_backdoor_adjustment: forall t,
  mutual_indep_three UHRV UTRV UCRV ->
  `Pr[ Tnodefn = t ] != 0 ->
  forall a, `Pr[ (Hnodefnint t) = a] = `Pr[ Hnodefn = a | Tnodefn = t].
Proof.
  intros.
  apply esym.
  apply doint_collider; try assumption.
Qed.

Print Assumptions three_var_collider_backdoor_adjustment.
End ThreeVarColliderExample.

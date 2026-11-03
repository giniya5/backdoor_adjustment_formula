Set Warnings "-notation-overridden,-deprecated-library-file,-ambiguous-paths".

From mathcomp Require Import all_ssreflect all_algebra fingroup lra ssralg.
From mathcomp Require Import unstable mathcomp_extra reals exp.
From Stdlib Require Import Reals FunctionalExtensionality Classical.
From infotheo.probability Require Import proba fdist.
From infotheo Require Import ssr_ext ssralg_ext bigop_ext realType_ext realType_ln.
From DAGs Require Import Basics.

(* the old development: GeneralFormulas supplies mutual_indep_three,
   mut_indp_cond_indp, indp_not_affected_by_adding_cond, marginalize, ...
   TwoVarThreeVarExamples supplies the P-independent helper lemmas
   (cinde_fn_transform', set_A'_always_exists, pfwd1_comp_sets(_joint),
   sets_are_sums, removing_singleton_from_sum, ...) *)
From project Require Import GeneralFormulas TwoVarThreeVarExamples.

(* the new node definitions *)
From Experiment Require Import Prob.
From CondIndep Require Import RandomVariableDef.

Local Open Scope ring_scope.
Local Open Scope reals_ext_scope.
Local Open Scope fdist_scope.
Local Open Scope proba_scope.

(* ===================================================================== *)
(* Part 1.  Probability-only core, for ANY finite probability space.      *)
(*                                                                        *)
(* The original lemmas below were stated for                              *)
(*     P : R.-fdist ((UC * UT) * UH)                                      *)
(* but none of the proofs look inside that product, and the new setting   *)
(* lives on  Pc : R.-fdist (context dom).  So they are re-stated for an   *)
(* arbitrary  P : R.-fdist U.  The scripts are the originals, except that *)
(* anonymous hypotheses now get explicit names (the old scripts relied on *)
(* the section's [Let H] forcing intros to call the first one [H0]).      *)
(* ===================================================================== *)
Section GenericConfounderAdjustment.
Context {R : realType} {U : finType} {P : R.-fdist U}.

Lemma change_to_set_three_way_gen {TA TB TD : finType}
  (X : {RV P -> TA}) (Y : {RV P -> TB}) (Z : {RV P -> TD}) :
  (forall (x : TA) (y : TB) (z : TD),
    `Pr[ X = x ] * `Pr[ Y = y ] * `Pr[ Z = z ] =
    `Pr[ [% X, Y, Z] = (x, y, z) ]) ->
  (forall (x : TA) (y : TB) (z' : {set TD}),
    `Pr[ X = x ] * `Pr[ Y = y ] * `Pr[ Z \in z' ] =
    `Pr[ [% X, Y, Z] \in [set x] `* [set y] `* z' ]).
Proof.
  move=> Hind x y z'.
  have H0 := Hind x y.
  rewrite sets_are_sums.
  rewrite sets_are_sums.
  rewrite big_distrr /=.
  (* rewrite <- mult_factor_in_sum. *)
  assert (forall z : TD, true ->
      `Pr[ X = x ] * `Pr[ Y = y ] * `Pr[ Z = z ] =
      `Pr[ [% X, Y, Z] = (x, y, z) ]).
    intros z _.
    exact: (H0 z).
  rewrite -> eq_bigr with
      (F1 := (fun z => `Pr[ X = x ] * `Pr[ Y = y ] * `Pr[ Z = z ]))
      (F2 := (fun z => `Pr[ [% X, Y, Z] = (x, y, z) ])); try assumption.
  rewrite big_enum.
  rewrite big_enum.
  simpl.
  rewrite same_singleton_sets.
  symmetry.
  exact: (removing_singleton_from_sum (x, y) z'
            (fun i => `Pr[ [% X, Y, Z] = i ])).
Qed.

Lemma mut_indp_with_fn_gen {TA TB TD UD : finType}
  (X : {RV P -> TA}) (Y : {RV P -> TB}) (Z : {RV P -> TD}) (h : TD -> UD) :
  mutual_indep_three X Y Z ->
  mutual_indep_three X Y (h `o Z).
Proof.
  move=> Hm.
  unfold mutual_indep_three.
  unfold mutual_indep_three in Hm.
  destruct Hm as [Indp3 [IndpXY [IndpYZ IndpXZ]]].
  split.
  - intros x y z.
    pose proof (set_A'_always_exists h z) as Hex.
    case: Hex => A [H0 H1].
    pose proof (change_to_set_three_way_gen X Y Z Indp3) as Indp3'.
    specialize (Indp3' x y A).
    rewrite -> pfwd1_comp_sets with (A' := A); try assumption.
    rewrite pfwd1_pairC.
    unfold swap.
    simpl.
    rewrite -> pfwd1_comp_sets_joint with (A' := A) (f := h) (X := Z)
        (Y := [% X, Y]); try assumption.
    rewrite pr_in_pairC.
    unfold swap.
    simpl.
    rewrite <- same_singleton_sets.
    exact Indp3'.
  - split; try split; try assumption.
    + pose proof (inde_RV_comp (fun x => x) h IndpYZ) as Hc.
      exact Hc.
    + pose proof (inde_RV_comp (fun x => x) h IndpXZ) as Hc.
      exact Hc.
Qed.

(* generalisation of indep_then_cond_irrelevant_wcond *)
Lemma cinde_cond_irrel_gen {TX TY TZ : finType}
  (X : {RV P -> TX}) (Y : {RV P -> TY}) (Z : {RV P -> TZ}) :
  Z _|_ X | Y ->
  forall y, `Pr[ Y = y ] != 0 ->
  forall x, `Pr[ X = x | Y = y ] != 0 ->
  forall z, `Pr[ Z = z | Y = y ] = `Pr[ Z = z | [% X, Y] = (x, y) ].
Proof.
  intros H0 y H1 x H2 z.
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

(* THE adjustment formula, with all graph structure abstracted away.
   Cn = confounder, Tn = treatment, Hn = observed outcome,
   Hi = outcome under do(Tn := t).
   Only three things are used:
     (1) Hn and Hi agree wherever Tn = t           (pointwise)
     (2) Hi _|_ Tn | Cn
     (3) Pr[Tn = t | Cn = c] <> 0 for every c.            *)
Lemma adjust_gen {TA TB TD : finType}
  (Cn : {RV P -> TA}) (Tn : {RV P -> TB}) (Hn Hi : {RV P -> TD}) (t : TB) :
  (forall w, Tn w = t -> Hn w = Hi w) ->
  Hi _|_ Tn | Cn ->
  (forall c, `Pr[ Tn = t | Cn = c ] != 0) ->
  forall h, `Pr[ Hi = h ] =
    \sum_(c in TA) (`Pr[ Hn = h | [% Tn, Cn] = (t, c) ] * `Pr[ Cn = c ]).
Proof.
  move=> Hagree Hind HT h.
  have HCnz : forall c, `Pr[ Cn = c ] != 0.
    move=> c; have HTc := HT c.
    apply/negP => /eqP Hz.
    apply cpr_eq0_denom with (X := Tn) (a := t) in Hz.
    by move: HTc; rewrite Hz eqxx.
  have Hstep : forall c,
      `Pr[ Hn = h | [% Tn, Cn] = (t, c) ] = `Pr[ Hi = h | Cn = c ].
    move=> c.
    rewrite (cinde_cond_irrel_gen Tn Cn Hi Hind c (HCnz c) t (HT c) h).
    have Hnum : `Pr[ [% Hn, [% Tn, Cn]] = (h, (t, c)) ] =
                `Pr[ [% Hi, [% Tn, Cn]] = (h, (t, c)) ].
      rewrite !pfwd1E /Pr.
      apply: eq_bigl => a.
      rewrite !inE !xpair_eqE.
      case Ht : (Tn a == t).
      - by move/eqP: Ht => Ht; rewrite (Hagree a Ht).
      - by rewrite !andFb !andbF.
    by rewrite !cpr_eqE Hnum.
  under eq_bigr => c _ do rewrite (Hstep c).
  by rewrite -[RHS]marginalize.
Qed.

End GenericConfounderAdjustment.

(* ===================================================================== *)
(* Part 2.  The confounder graph  C -> T -> H,  C -> H  on the NEW        *)
(*          node definitions (nodeRV / doRV / unobsRV over Pc).           *)
(*                                                                        *)
(* What changed relative to the old Section ThreeVarConfounderExample:    *)
(*  * No product space (UC*UT)*UH and no [Let C/T/H/Hinterv].  The        *)
(*    sample space is  context dom  with the product law  Pc.            *)
(*  * Cnodefn / Tnodefn / Hnodefn  become  nodeRV nC / nT / nH.           *)
(*    Hnodefnint t               becomes  doRV nT t nH.                   *)
(*    UCRV / UTRV / UHRV         become   unobsRV nC / nT / nH.           *)
(*  * Every node has its OWN finite domain [dom n] (the old file forced   *)
(*    one [outcomes] type for all three).                                 *)
(*  * The old proofs unfolded the Lets by [unfold].  The new RVs are      *)
(*    defined through find_value, which does not unfold to the mechanism  *)
(*    by itself -- that is exactly the "elaboration correctness" lemma    *)
(*    Prob.v says is still open (needs range-closure of enc).  It enters  *)
(*    below as the three hypotheses Hnode / Hdo_on / Hdo_off; once it is  *)
(*    proved in Prob.v they become lemmas and this section loses them.    *)
(* ===================================================================== *)
Section ConfounderBackdoorNew.

Variable R : realType.
Variable G : graph.
Variable dom : Node G -> finType.
Variable enc : forall n : Node G, dom n -> nat.
Variable dec : forall n : Node G, nat -> dom n.
Variable Pn : forall n : Node G, R.-fdist (dom n).
Variable tF : tgraphfun dom.
Hypothesis encK : forall n : Node G, cancel (enc n) (dec n).

(* readable names for the new definitions *)
Local Notation NR := (@nodeRV R G dom enc dec Pn tF).   (* solved node value *)
Local Notation DR := (@doRV R G dom enc dec Pn tF).     (* node under do(.)  *)
Local Notation UR := (@unobsRV R G dom Pn).             (* exogenous slot    *)

(* the three nodes: confounder C, treatment T, outcome H *)
Variables nC nT nH : Node G.
Hypothesis HcT : nC != nT.
Hypothesis HhT : nH != nT.

(* declared edges  C -> T,  C -> H,  T -> H *)
Hypothesis HpCT : is_parent nT nC.
Hypothesis HpCH : is_parent nH nC.
Hypothesis HpTH : is_parent nH nT.

(* the typed mechanisms (replacing  fC, fT, fH  of the old file) *)
Variable fC : dom nC -> dom nC.
Variable fT : dom nT -> dom nC -> dom nT.
Variable fH : dom nH -> dom nC -> dom nT -> dom nH.

Hypothesis HFC : forall (u : dom nC) (pa : parent_view dom nC),
  tF nC u pa = fC u.
Hypothesis HFT : forall (u : dom nT) (pa : parent_view dom nT),
  tF nT u pa = fT u (pa nC HpCT).
Hypothesis HFH : forall (u : dom nH) (pa : parent_view dom nH),
  tF nH u pa = fH u (pa nC HpCH) (pa nT HpTH).

(* elaboration correctness (open in Prob.v): the solver computes what the
   typed mechanism says, both in G and in the surgically altered graph *)
Hypothesis Hnode : forall (n : Node G) (w : context dom),
  NR n w = tF n (w n) (fun p _ => NR p w).
Hypothesis Hdo_on : forall (n0 : Node G) (v : dom n0) (w : context dom),
  DR n0 v n0 w = v.
Hypothesis Hdo_off : forall (n0 : Node G) (v : dom n0) (n : Node G)
    (w : context dom),
  n != n0 -> DR n0 v n w = tF n (w n) (fun p _ => DR n0 v p w).

(* --- the pointwise equations the old proofs got from [unfold] --------- *)

Lemma nodeC w : NR nC w = fC (w nC).
Proof. exact: (etrans (Hnode nC w) (HFC _ _)). Qed.

Lemma nodeT w : NR nT w = fT (w nT) (NR nC w).
Proof. exact: (etrans (Hnode nT w) (HFT _ _)). Qed.

Lemma nodeH w : NR nH w = fH (w nH) (NR nC w) (NR nT w).
Proof. exact: (etrans (Hnode nH w) (HFH _ _)). Qed.

Lemma doC (v : dom nT) w : DR nT v nC w = fC (w nC).
Proof. exact: (etrans (Hdo_off nT v nC w HcT) (HFC _ _)). Qed.

Lemma doH (v : dom nT) w :
  DR nT v nH w = fH (w nH) (DR nT v nC w) v.
Proof.
  have e := etrans (Hdo_off nT v nH w HhT) (HFH _ _).
  exact: (etrans e (f_equal (fun x => fH (w nH) (DR nT v nC w) x)
                            (Hdo_on nT v w))).
Qed.

(* Hinterv _|_ T | C, from independence of the exogenous slots.
   Old name: mut_unobs_indp_cond_indp_wo_inj. *)
Lemma cinde_do (v : dom nT) :
  mutual_indep_three (UR nH) (UR nT) (UR nC) ->
  (DR nT v nH) _|_ (NR nT) | (NR nC).
Proof.
  move=> Hmut.
  have Hm := mut_indp_with_fn_gen (UR nH) (UR nT) (UR nC) fC Hmut.
  apply mut_indp_cond_indp in Hm.
  apply indp_not_affected_by_adding_cond in Hm.
  have e1 : DR nT v nH =
      (fun u : dom nH * dom nC => fH u.1 u.2 v) `o [% UR nH, (fC `o UR nC)].
    apply: functional_extensionality => w.
    exact: (etrans (doH v w) (f_equal (fun x => fH (w nH) x v) (doC v w))).
  have e2 : NR nT =
      (fun u : dom nT * dom nC => fT u.1 u.2) `o [% UR nT, (fC `o UR nC)].
    apply: functional_extensionality => w.
    exact: (etrans (nodeT w) (f_equal (fun x => fT (w nT) x) (nodeC w))).
  have e3 : NR nC = fC `o UR nC.
    apply: functional_extensionality => w.
    exact: (nodeC w).
  rewrite e1 e2 e3.
  exact: (cinde_fn_transform' (UR nH) (UR nT) (fC `o UR nC)
            (fun u : dom nH * dom nC => fH u.1 u.2 v)
            (fun u : dom nT * dom nC => fT u.1 u.2) Hm).
Qed.

(* ===================================================================== *)
(* THE LEMMA, rewritten.                                                  *)
(*                                                                        *)
(* Old:                                                                   *)
(*   forall t, mutual_indep_three UHRV UTRV UCRV ->                       *)
(*     (forall c, Pr[Tnodefn = t | Cnodefn = c] != 0) ->                  *)
(*     forall h, Pr[Hnodefnint t = h] =                                   *)
(*       \sum_(c in outcomes) Pr[Hnodefn = h | [%Tnodefn,Cnodefn]=(t,c)]  *)
(*                            * Pr[Cnodefn = c]                           *)
(* ===================================================================== *)
Lemma three_var_confounder_backdoor_adjustment (v : dom nT) :
  mutual_indep_three (UR nH) (UR nT) (UR nC) ->
  (forall c, `Pr[ (NR nT) = v | (NR nC) = c ] != 0) ->
  forall h, `Pr[ (DR nT v nH) = h ] =
    \sum_(c in dom nC)
      (`Pr[ (NR nH) = h | [% (NR nT), (NR nC)] = (v, c) ] * `Pr[ (NR nC) = c ]).
Proof.
  move=> Hmut HT.
  apply: (adjust_gen (NR nC) (NR nT) (NR nH) (DR nT v nH) v _
        (cinde_do v Hmut) HT).
  move=> w Hw.
  by rewrite (nodeH w) (doH v w) (doC v w) -(nodeC w) Hw.
Qed.

End ConfounderBackdoorNew.

Set Warnings "notation-overridden,deprecated-library-file,ambiguous-paths".
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
From CondIndep Require Import DSepCondIndepv2.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From mathcomp Require Import all_ssreflect ssralg ssrnum finalg reals matrix.
From infotheo Require Import ssr_ext ssralg_ext fdist proba.
Import Order.POrderTheory Order.TotalTheory GRing.Theory Num.Theory.

Import ListNotations.

(* ================================================================== *)
(* d-separation implies conditional independence, for SETS X, Y, Z     *)
(* ================================================================== *)

Section DSepImpliesCondIndepSets.

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

Local Notation Pc      := (@Pc R G dom Pn).
Local Notation nodeRV  := (@nodeRV R G dom enc dec Pn tF).
Local Notation setRV   := (@setRV R G dom enc dec Pn tF).
Local Notation j0      := (@j0 R G dom Pn).
Local Notation fact_comp := (@fact_comp R).
Local Notation cinde_of_factorization := (@cinde_of_factorization R).
Local Notation cinde_of_blocks_ctx := (@cinde_of_blocks R G dom enc dec Pn tF encK).
(* Lemmas of v2 used by [cinde_of_blocks_sets].  If Coq complains about
   argument order/count, run [About <name>.] and adjust. *)
Local Notation factor_split := (@factor_split R G dom Pn tF).
Local Notation pfwd1_ancestral := (@pfwd1_ancestral R G dom enc dec Pn tF encK).

(* ------------------------------------------------------------------ *)
(* Definitions                                                         *)
(* ------------------------------------------------------------------ *)

(* Z d-separates the SET X from the SET Y: every pair (x, y) is
   d-separated by Z.  (This is the standard definition.) *)
Definition d_separated_sets (X Y Z : {set Node G}) : Prop :=
  forall x y : Node G, x \in X -> y \in Y ->
    d_separated_bool (ssval x) (ssval y) G (set_nodes G Z) = true.

(* Z separates X from Y in the moral graph of G[A] *)
Definition moral_sep_sets (A Z X Y : {set Node G}) : Prop :=
  forall x y : Node G, x \in X -> y \in Y -> moral_sep G A Z x y.

(* ------------------------------------------------------------------ *)
(* Step 1 (probability): blocks with sets in place of single nodes     *)
(* ------------------------------------------------------------------ *)

(* PLAN.  Copy the proof of [cinde_of_blocks] from v2 verbatim up to and
   including [Hfac] (the joint law of (setRV C, setRV Rs, setRV Z) as
   g0 * h0).  Only the last paragraph changes.  There v2 pushes the law down
   along the coordinate maps  al |-> al X  and  be |-> be Y.  Here use the
   masking maps
       fX al := [ffun n => if n \in X then al n else j0 n]
       fY be := [ffun n => if n \in Y then be n else j0 n]
   with  HXe : setRV X u = fX (setRV C u)   (ext. by ffunP; case n \in X;
   uses X \subset C)   and   HYe : setRV Y u = fY (setRV Rs u)  (uses
   Y \subset Rs, which follows from Y \subset A, Y disjoint from C and Z).
   Then [fact_comp] with f := fX, f' := fY, followed by
   [cinde_of_factorization] with
       g x z := \sum_(al | fX al == x) g0 al z,
       h y z := \sum_(be | fY be == y) h0 be z
   exactly as in v2.  (v2's coordinate projection is the special case.) *)
Lemma cinde_of_blocks_sets (A Z C X Y : {set Node G}) :
  G_well_formed G = true /\ contains_cycle G = false ->
  ancestral G A ->
  Z \subset A -> C \subset A -> (forall n : Node G, n \in C -> n \notin Z) ->
  (forall a b : Node G, a \in C -> moral_adj G A a b -> b \in C \/ b \in Z) ->
  X \subset C -> Y \subset A -> [disjoint Y & C] -> [disjoint Y & Z] ->
  Pc |= setRV X _|_ setRV Y | setRV Z.
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
  (* push the block law down along the masking maps *)
  pose fX (al : world dom) : world dom :=
    [ffun n => if n \in X then al n else j0 n].
  pose fY (be : world dom) : world dom :=
    [ffun n => if n \in Y then be n else j0 n].
  have HYR : forall n, n \in Y -> n \in Rs.
    move=> n HnY; apply: HAcases.
    - exact: (subsetP HYA n HnY).
    - pose proof (disjointFr HYC HnY).
      apply/negP.
      rewrite H.
      exact not_false_is_true.
    - pose proof (disjointFr HYS HnY).
      apply/negP.
      rewrite H.
      exact not_false_is_true.
  have HXe : forall u : context dom, setRV X u = fX (setRV C u).
    move=> u; apply/ffunP => n; rewrite /setRV /fX !ffunE.
    case: (boolP (n \in X)) => HnX.
    - pose proof (subsetP HXC n HnX).
      rewrite H.
      reflexivity.
    - reflexivity.
  have HYe : forall u : context dom, setRV Y u = fY (setRV Rs u).
    move=> u; apply/ffunP => n; rewrite /setRV /fY !ffunE.
    case: (boolP (n \in Y)) => HnY.
    - pose proof (HYR n HnY).
      rewrite H.
      reflexivity.
    - reflexivity.
  have Hfc := fact_comp _ _ _ _ _ (setRV C) (setRV Rs) (setRV Z)
      (world dom) (world dom) fX fY (setRV X) (setRV Y) HXe HYe g0 h0 Hfac.
  exact: (cinde_of_factorization _ _ _ _ _ (setRV X) (setRV Y) (setRV Z)
      (fun (x : world dom) (z : world dom) => \sum_(al : world dom | fX al == x) g0 al z)
      (fun (y : world dom) (z : world dom) => \sum_(be : world dom | fY be == y) h0 be z)
      Hfc).
Qed.

(* PLAN.  Same as [cinde_of_moral_sep], with
     A := anc_set G (X :|: (Y :|: Z))
     C := [set n | [exists x in X, connect (moral_adj_avoid G A Z) x n]]
   Needed facts:
     * X \subset C: connect0 (needs nothing).
     * C \subset A and C disjoint from Z: the [Hpath] argument, started at
       any x in X; this needs X \subset A (X inside the anc_set, as in v2's
       [HinA]) and [disjoint X & Z] to start the path outside Z.
     * Hclosed: identical (connect_trans from the witness x).
     * Y disjoint from C: if y in Y were in C, some x in X has a path
       x ~> y, contradicting [moral_sep_sets].
     * Y \subset A and [disjoint Y & Z]: given / as in v2.
   Conclude with [cinde_of_blocks_sets]. *)
Lemma cinde_of_moral_sep_sets (X Y Z : {set Node G}) :
  G_well_formed G = true /\ contains_cycle G = false ->
  [disjoint X & Z] -> [disjoint Y & Z] ->
  moral_sep_sets (anc_set G (X :|: (Y :|: Z))) Z X Y ->
  Pc |= setRV X _|_ setRV Y | setRV Z.
Proof using encK.
  move=> Hdag HXZ HYZ Hsep.
  pose A := anc_set G (X :|: (Y :|: Z)).
  have Hanc : ancestral G A := anc_set_ancestral G _ Hdag.
  have HinA : forall t, t \in X :|: (Y :|: Z) -> t \in A.
    move=> t Ht; rewrite /A /anc_set inE; apply/existsP; exists t.
    by rewrite Ht (self_in_ancestors G t).
  have HXA : X \subset A.
    apply/subsetP => t Ht; apply: HinA; apply/setUP; left; exact: Ht.
  have HYA : Y \subset A.
    apply/subsetP => t Ht; apply: HinA; apply/setUP; right.
    apply/setUP; left; exact: Ht.
  have HSA : Z \subset A.
    apply/subsetP => t Ht; apply: HinA; apply/setUP; right.
    apply/setUP; right; exact: Ht.
  have Hma_r : forall a b, moral_adj G A a b -> b \in A.
    move=> a b; rewrite /moral_adj => /andP [/andP [/andP [_ _] Hb] _].
    exact: Hb.
  pose C : {set Node G} :=
    [set n | [exists x in X, connect (moral_adj_avoid G A Z) x n]].
  have Hpath : forall (p : seq (Node G)) (x : Node G),
      path (moral_adj_avoid G A Z) x p -> x \in A -> x \notin Z ->
      last x p \in A /\ last x p \notin Z.
    move=> p; elim: p => [| y p IH] x /=.
    - by move=> _ HxA HxS; split; [exact: HxA | exact: HxS].
    - move=> /andP [Hxy Hp] _ _.
      move: Hxy; rewrite /moral_adj_avoid => /andP [/andP [Hm _] HyS].
      exact: IH y Hp (Hma_r x y Hm) HyS.
  have HXC : X \subset C.
    apply/subsetP => x Hx; rewrite /C inE; apply/existsP; exists x.
    by rewrite Hx connect0.
  have HCsub : forall n, n \in C -> n \in A /\ n \notin Z.
    move=> n; rewrite /C inE => /existsP [x /andP [Hx Hc]].
    move: Hc => /connectP [p Hp ->].
    assert (x \notin Z).
      pose proof (disjointFr HXZ Hx).
      apply/negP.
      rewrite H.
      exact not_false_is_true. 
    pose proof (Hpath p x Hp (subsetP HXA x Hx) H).
    exact: Hpath p x Hp (subsetP HXA x Hx) H.
  have HCA : C \subset A.
    by apply/subsetP => n Hn; exact: (HCsub n Hn).1.
  have Hdis : forall n : Node G, n \in C -> n \notin Z :=
    fun n HnC => (HCsub n HnC).2.
  have Hclosed : forall a b : Node G, a \in C -> moral_adj G A a b ->
      b \in C \/ b \in Z.
    move=> a b HaC Hab.
    case: (boolP (b \in Z)) => [HbS | HbS]; first by right.
    left.
    have HaS := (HCsub a HaC).2.
    move: HaC; rewrite /C !inE => /existsP [x /andP [Hx Hxa]].
    apply/existsP; exists x; apply/andP; split; first exact: Hx.
    apply: (connect_trans Hxa).
    apply: connect1.
    by rewrite /moral_adj_avoid Hab HaS HbS.
  have HYC : [disjoint Y & C].
  rewrite disjoints_subset; apply/subsetP => y Hy.
  rewrite inE; apply/negP => HyC.
  move: HyC; rewrite /C inE => /existsP [x /andP [Hx Hxy]].
  exact: (elimT negP (Hsep x y Hx Hy) Hxy).
  exact: (cinde_of_blocks_sets A Z C X Y Hdag Hanc HSA HCA Hdis Hclosed
          HXC HYA HYC HYZ).
Qed.

(* ------------------------------------------------------------------ *)
(* Step 2 (graph): d-separation of sets gives moral separation          *)
(* ------------------------------------------------------------------ *)
 
(* PLAN.  Almost everything in v2 is reused UNCHANGED, because [Wk],
   [wk_out], [wk_in_from_out], [wk_in_from_in], [wk_up], [wk_down],
   [wk_to_desc], [walk_to_path] and [end_case] already take the walk's
   start X as a plain node parameter.  Only the "state machine" lemmas
   need to be re-stated, with the invariant
 
      Inv v :=  exists x, x \in X /\ exists d, Wk S (ssval x) (ssval v) d
 
   i.e. the START of the open walk is allowed to move around inside X.
   This is exactly what is needed: at a bad collider c (no descendant in S)
   c is an ancestor of some t in X :|: Y :|: S, and t is not in S, so
 
     - t in Y :  [wk_to_desc] gives a walk from the CURRENT start x0 to t.
                 Done: x0 in X, t in Y are d-connected.
     - t in X :  [wk_up] gives a walk from t (a DIFFERENT element of X)
                 up to c, with direction [false].  Restart from t.
                 (With single nodes t = X always, so v2 never needed this.)
 
   The restart is the only new idea. *)
 
(* PLAN: v2's [bad_resolve].  Proof = same case split on t; in the X case
   return [exists x, x \in X /\ Wk _ (ssval x) (ssval c) false] with x := t. *)
Lemma bad_resolve_sets (X Y : {set Node G}) (c x0 : Node G) (S : {set Node G})
    (d : bool) :
  G_well_formed G = true /\ contains_cycle G = false ->
  c \in anc_set G (X :|: (Y :|: S)) ->
  (forall e, In e (find_descendants (ssval c) G) -> ~ In e (set_nodes G S)) ->
  x0 \in X ->
  Wk G (set_nodes G S) (ssval x0) (ssval c) d ->
  (exists x y, x \in X /\ y \in Y /\
      exists d', Wk G (set_nodes G S) (ssval x) (ssval y) d') \/
  (exists x, x \in X /\ Wk G (set_nodes G S) (ssval x) (ssval c) false).
Proof.
  move=> Hdag Hc Hnz Hx0 Hw.
  (* c is an ancestor of some t in X :|: (Y :|: S) *)
  move: Hc; rewrite /anc_set inE => /existsP [t /andP [Ht Hct]].
  have Htd : In (ssval t) (find_descendants (ssval c) G) :=
    proj2 (descendants_ancestors_correct G (ssval t) (ssval c)
      (conj (node_in_graph_ssval t) (node_in_graph_ssval c))) (mem_In Hct).
  move: Ht; rewrite !inE => /orP [HtX | /orP [HtY | HtS]].
  - (* t in X: restart the walk from t, going up to c *)
    right; exists t; split; first exact: HtX.
    exact: (wk_up G (set_nodes G S) (ssval t) (ssval c) Hdag Htd Hnz).
  - (* t in Y: extend the current walk from x0 down to t *)
    left; exists x0, t; split; first exact: Hx0.
    split; first exact: HtY.
    exact: (wk_to_desc G (set_nodes G S) (ssval x0) (ssval c) (ssval t) d
              Hdag Hw Htd Hnz).
  - (* t in S: contradicts that c has no descendant in S *)
    exfalso; exact: (Hnz _ Htd (in_set_nodes G t S HtS)).
Qed.
 
(* PLAN: v2's [lift_step]; same three edge cases (v -> y, y -> v, common
   child c).  Replace each use of [bad_resolve] by [bad_resolve_sets] and
   carry the (possibly new) start x along.  Hypotheses on the walk now come
   with [x \in X]. *)
Lemma lift_step_sets (X Y : {set Node G}) (v y : Node G) (S : {set Node G}) :
  G_well_formed G = true /\ contains_cycle G = false ->
  moral_adj_avoid G (anc_set G (X :|: (Y :|: S))) S v y ->
  (exists x, x \in X /\ exists d, Wk G (set_nodes G S) (ssval x) (ssval v) d) ->
  (exists x y', x \in X /\ y' \in Y /\
      exists d, Wk G (set_nodes G S) (ssval x) (ssval y') d) \/
  (exists x, x \in X /\ exists d, Wk G (set_nodes G S) (ssval x) (ssval y) d).
Proof.
  move=> Hdag Hvy [x [HxX [d Hw]]].
  move: Hvy; rewrite /moral_adj_avoid => /andP [/andP [Hm HvS] HyS].
  have HvZ : ~ In (ssval v) (set_nodes G S) := nin_Z G v S HvS.
  move: Hm; rewrite /moral_adj => /andP [/andP [/andP [_ HvA] HyA] Hdisj].
  case/orP: Hdisj => [/orP [He1 | He2] | Hex].
  - (* an edge v -> y *)
    right; exists x; split; first exact: HxX.
    exists true.
    exact: (wk_out G _ _ _ _ d Hdag Hw HvZ He1).
  - (* an edge y -> v *)
    case: d Hw => Hw.
    + case: (boolp.EM (exists e, In e (find_descendants (ssval v) G)
                                /\ In e (set_nodes G S))) => [Hd | Hnd].
      * right; exists x; split; first exact: HxX.
        exists false.
        exact: (wk_in_from_in G _ _ _ _ Hw He2 Hd).
      * case: (bad_resolve_sets X Y v x S true Hdag HvA
                (fun e H1 H2 => Hnd (ex_intro _ e (conj H1 H2))) HxX Hw)
          => [[x1 [y1 [Hx1 [Hy1 [d' Hw']]]]] | [x1 [Hx1 Hw0]]].
        -- left; exists x1, y1; split; first exact: Hx1.
          split; first exact: Hy1.
          by exists d'.
        -- right; exists x1; split; first exact: Hx1.
          exists false.
          exact: (wk_in_from_out G _ _ _ _ Hdag Hw0 HvZ He2).
    + right; exists x; split; first exact: HxX.
      exists false.
      exact: (wk_in_from_out G _ _ _ _ Hdag Hw HvZ He2).
  - (* a common child c of v and y *)
    case/existsP: Hex => c /andP [HcA /andP [Hvc Hyc]].
    have Hwc : Wk G (set_nodes G S) (ssval x) (ssval c) true :=
      wk_out G _ _ _ _ d Hdag Hw HvZ Hvc.
    case: (boolp.EM (exists e, In e (find_descendants (ssval c) G)
                              /\ In e (set_nodes G S))) => [Hd | Hnd].
    + right; exists x; split; first exact: HxX.
      exists false.
      exact: (wk_in_from_in G _ _ _ _ Hwc Hyc Hd).
    + case: (bad_resolve_sets X Y c x S true Hdag HcA
              (fun e H1 H2 => Hnd (ex_intro _ e (conj H1 H2))) HxX Hwc)
        => [[x1 [y1 [Hx1 [Hy1 [d' Hw']]]]] | [x1 [Hx1 Hw0]]].
      * left; exists x1, y1; split; first exact: Hx1.
        split; first exact: Hy1.
        by exists d'.
      * right; exists x1; split; first exact: Hx1.
        exists false.
        have HcZ : ~ In (ssval c) (set_nodes G S).
          move=> HcZ'; apply: Hnd; exists (ssval c); split.
          -- exact: node_is_descendant_of_itself _ _.
          -- exact: HcZ'.
        exact: (wk_in_from_out G _ _ _ _ Hdag Hw0 HcZ Hyc).
Qed.
 
(* PLAN: induction on the moral path, identical to v2's [lift_path] with
   [lift_step_sets]. *)
Lemma lift_path_sets (X Y : {set Node G}) (S : {set Node G}) :
  G_well_formed G = true /\ contains_cycle G = false ->
  forall (p : seq (Node G)) (v : Node G),
    path (moral_adj_avoid G (anc_set G (X :|: (Y :|: S))) S) v p ->
    v \notin S ->
    (exists x, x \in X /\ exists d, Wk G (set_nodes G S) (ssval x) (ssval v) d) ->
    (exists x y, x \in X /\ y \in Y /\
        exists d, Wk G (set_nodes G S) (ssval x) (ssval y) d) \/
    (exists x, x \in X /\
        exists d, Wk G (set_nodes G S) (ssval x) (ssval (last v p)) d).
Proof.
  move=> Hdag p; elim: p => [|y p IH] v; cbn [path last].
  - by move=> _ _ Hv; right.
  - move=> /andP [Hvy Hp] HvS Hv.
    case: (lift_step_sets X Y v y S Hdag Hvy Hv) => [Hg | Hy].
    + by left.
    + have HyS : y \notin S.
        by move: Hvy; rewrite /moral_adj_avoid => /andP [_ HyS]; exact: HyS.
      exact: (IH y Hp HyS Hy).
Qed.

(* PLAN.  Contrapositive, as in v2's [dsep_implies_moral_sep].
   Take x0 in X, y0 in Y and a moral path p from x0 to y0 avoiding S.
   Start state: x := x0, [Wk ... x0 x0 true] ([left]).  Run [lift_path_sets].
   Either outcome yields x in X, y in Y (in the second case y := y0 =
   last x0 p) with an open walk x ~> y.  Feed it to v2's [end_case], which
   needs only  x <> y  (from [disjoint X & Y]) and the d-separation of that
   particular pair (from [d_separated_sets]). *)
Lemma dsep_implies_moral_sep_sets (X Y S : {set Node G}) :
  G_well_formed G = true /\ contains_cycle G = false ->
  [disjoint X & Y] -> [disjoint X & S] -> [disjoint Y & S] ->
  d_separated_sets X Y S ->
  moral_sep_sets (anc_set G (X :|: (Y :|: S))) S X Y.
Proof.
  move=> Hdag HXY HXS HYS Hd x y Hx Hy.
  have Hne : forall a b : Node G, a \in X -> b \in Y -> a != b.
    move=> a b Ha Hb; apply/negP => /eqP E.
    assert (a \notin Y) as Hay.
      pose proof (disjointFr HXY Ha).
      apply/negP.
      rewrite H.
      exact not_false_is_true.
    by move: Hay; rewrite E Hb.
  assert (x \notin S) as HxS.
    pose proof (disjointFr HXS Hx).
    apply/negP.
    rewrite H.
    exact not_false_is_true.
  (* have HxS : x \notin S := disjointFr HXS Hx. *)
  rewrite /moral_sep. apply/negP => Hconn.
  case/connectP: Hconn => p Hp Hlast.
  have HX0 : exists x0, x0 \in X /\
      exists d, Wk G (set_nodes G S) (ssval x0) (ssval x) d.
    by exists x; split; first exact: Hx; exists true; left.
  case: (lift_path_sets X Y S Hdag p x Hp HxS HX0)
    => [[x1 [y1 [Hx1 [Hy1 [d Hg]]]]] | [x1 [Hx1 [d Hl]]]].
  - exact: (end_case G x1 y1 S d Hdag (Hne x1 y1 Hx1 Hy1) (Hd x1 y1 Hx1 Hy1) Hg).
  - rewrite -Hlast in Hl.
    exact: (end_case G x1 y S d Hdag (Hne x1 y Hx1 Hy) (Hd x1 y Hx1 Hy) Hl).
Qed.

(* ------------------------------------------------------------------ *)
(* Main lemma, sets version                                            *)
(* ------------------------------------------------------------------ *)

(* If every pair x in X, y in Y is d-separated by Z (X, Y, Z pairwise
   disjoint) in a well-formed acyclic G, then the bundle of solved values
   of X is independent of the bundle of solved values of Y given the
   bundle of solved values of Z. *)
Lemma dsep_implies_cond_indep_sets (X Y Z : {set Node G}) :
  G_well_formed G = true /\ contains_cycle G = false ->
  [disjoint X & Y] -> [disjoint X & Z] -> [disjoint Y & Z] ->
  d_separated_sets X Y Z ->
  Pc |= setRV X _|_ setRV Y | setRV Z.
Proof using encK.
  move=> Hdag HXY HXZ HYZ Hd.
  have Hm := dsep_implies_moral_sep_sets X Y Z Hdag HXY HXZ HYZ Hd.
  exact: (cinde_of_moral_sep_sets X Y Z Hdag HXZ HYZ Hm).
Qed.

(* Print Assumptions dsep_implies_cond_indep_sets. *)

End DSepImpliesCondIndepSets.
From mathcomp Require Import all_ssreflect all_algebra all_field.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory UnityRootTheory.
Open Scope ring_scope.

Section PreliminaryLemmas.

Locate "%:R".
Locate "morph".
About morphism_2.

Lemma Cnat_add_eq1 : {in Cnat &, forall x y,
   (x + y == 1) = ((x == 1) && (y == 0))
               || ((x == 0) && (y == 1))}.
Proof.
  move=> x y /CnatP [n ->] /CnatP [m ->].
  rewrite (eqC_nat n 1) (eqC_nat n 0) (eqC_nat m 1) (eqC_nat m 0) -natrD (eqC_nat _ 1).
  case:m; case:n => //; case => //.
Qed.

About mulrDr.
About mulrDl.
About ReMl.
Search ((_ * _) * _).

About Re_rect.

Lemma algReM (x y : algC) :
  'Re (x * y) = 'Re x * 'Re y - 'Im x * 'Im y.
Proof.
  rewrite [in LHS](Crect x) [in LHS](Crect y) mulrDr mulrDl mulrDl raddfD.
  rewrite raddfD raddfD /=.
  rewrite (ReMl (Creal_Re _)) (ReMl (Creal_Re _))
    (ReMr (Creal_Im _)) mulrA (ReMr (Creal_Re _))
    (ReMr (Creal_Im _)) (mulrA _ 'i) (ReMr (Creal_Im _))
    (mulrC _ 'i) (mulrA 'i) (ReMr (Creal_Im _)).
  rewrite ['i * 'i]sqrCi.
  rewrite  raddfN /= Re_i (Creal_ReP _ (Creal_Re _)) (Creal_ReP _ Creal1).

  rewrite mulr0 mul0r mul0r
    mul0r add0r addr0  mulNr mulNr mul1r.
  reflexivity.
Qed.

Lemma algImM (x y : algC) :
  'Im (x * y) = 'Re x * 'Im y + 'Re y * 'Im x.
Proof.
  rewrite [in LHS](Crect x) [in LHS](Crect y) mulrDr mulrDl mulrDl raddfD.
  rewrite raddfD raddfD /=.
Admitted.

Section GaussianIntegers.

Definition gaussInteger :=
  [qualify a x | ('Re x \in Cint) && ('Im x \in Cint)].

Locate "qualify".

Lemma Cint_GI (x : algC) : x \in Cint -> x \is a gaussInteger.
Proof.
  move=> /CintP [m ->].
  apply /andP.
  apply: andP.
  have h: (m%:~R : algC) \is Num.real.
    apply: Creal_Cint. apply: Cint_int.
  rewrite (Creal_ReP _ h) (Creal_ImP _ h) Cint_int //.
Qed.

Print Re_rect.

Lemma GI_subring : subring_closed gaussInteger.
Proof.
  split.
    apply: Cint_GI. done.

  move=> x y /andP [hx1 hx2] /andP [hy1 hy2].
  rewrite qualifE !(raddfB, rpredB) //.

  move=> x y /andP [hx1 hx2] /andP [hy1 hy2].
  rewrite qualifE algReM algImM !(rpredB, rpredD) // rpredM //.
Qed.

Print pred_key.

Fact GI_key : pred_key gaussInteger. Proof. by []. Qed.
Canonical GI_keyed := KeyedQualifier GI_key.
Canonical GI_opprPred := OpprPred GI_subring.
Canonical GI_addrPred := AddrPred GI_subring.
Canonical GI_mulrPred := MulrPred GI_subring.
Canonical GI_zmodPred := ZmodPred GI_subring.
Canonical GI_semiringPred := SemiringPred GI_subring.
Canonical GI_smulrPred := SmulrPred GI_subring.
Canonical GI_subringPred := SubringPred GI_subring.

Print KeyedQualifier.

Record GI := GIof {
  algGI : algC;
  algGIP : algGI \is a gaussInteger }.
Hint Resolve algGIP.

Canonical GI_subType := [subType for algGI].

Lemma GIRe (x : GI) : 'Re (val x) \in Cint.
Proof. by have /andP [] := algGIP x. Qed.
Lemma GIIm (x : GI) : 'Im (val x) \in Cint.
Proof. by have /andP [] := algGIP x. Qed.
Hint Resolve GIRe GIIm.

Canonical ReGI x := GIof (Cint_GI (GIRe x)).
Canonical ImGI x := GIof (Cint_GI (GIIm x)).

Definition GI_eqMixin := [eqMixin of GI by <:].
Canonical GI_eqType := EqType GI GI_eqMixin.
Definition GI_choiceMixin := [choiceMixin of GI by <:].
Canonical GI_choiceType := ChoiceType GI GI_choiceMixin.
Definition GI_countMixin := [countMixin of GI by <:].
Canonical GI_countType := CountType GI GI_countMixin.
Definition GI_zmodMixin := [zmodMixin of GI by <:].
Canonical GI_zmodType := ZmodType GI GI_zmodMixin.
Definition GI_ringMixin := [ringMixin of GI by <:].
Canonical GI_ringType := RingType GI GI_ringMixin.
Definition GI_comRingMixin := [comRingMixin of GI by <:].
Canonical GI_comRingType := ComRingType GI GI_comRingMixin.
(* Definition GI_unitRingMixin := <tt>unitRingMixin</tt> <tt>of</tt> <tt>GI</tt> <tt>by</tt> <tt><:</tt>. *)
(* Canonical GI_unitRingType := UnitRingType *)

Definition invGI (x : GI) := insubd x (val x)^-1.
Definition unitGI := [pred x : GI | (x != 0)
          && ((val x)^-1 \is a gaussInteger)].

Fact mulGIr : {in unitGI, left_inverse 1 invGI *%R}.
Proof.
  move=> x /andP [hx0 hx].
  apply:val_inj.
  rewrite /invGI /= val_insubd hx mulVf //.
Qed.

Lemma conjGIE x : (x^* \is a gaussInteger) = (x \is a gaussInteger).
Proof.
  have: ('Re x^* \in Cint) && ('Im x^* \in Cint) =
    ('Re x \in Cint) && ('Im x \in Cint).
    rewrite Re_conj Im_conj rpredN //.
  done.
Qed.

Fact conjGI_subproof (x : GI) : (val x)^* \is a gaussInteger.
Proof. by rewrite conjGIE. Qed.

Canonical conjGI x := GIof (conjGI_subproof x).

Definition gaussNorm (x : algC) := x * x^*.
Lemma gaussNorm_val (x : GI) : gaussNorm (val x) = val (x * conjGI x).
Proof. by []. Qed.

Lemma gaussNormE x : gaussNorm x = `|x| ^+ 2.
Proof.
  rewrite normCK //.
Qed.

Lemma gaussNormCnat (x : GI) : gaussNorm (val x) \in Cnat.
Proof.
  have h1: 'Re (val x) \is Num.real := (Creal_Re _).
  have h2: 'Im (val x) \is Num.real := (Creal_Im _).
  rewrite gaussNormE (algCrect (val x)) normC2_rect // rpredD // CnatEint
    rpredX.
  rewrite -realEsqr Creal_Re //.
  case: x h1 h2 => //.
  rewrite -realEsqr Creal_Im //.
  case: x h1 h2 => //.
Qed.

Lemma gaussNorm1 : gaussNorm 1 = 1.
Proof. rewrite /gaussNorm mul1r conjC1 //. Qed.

Lemma gaussNormM : {morph gaussNorm : x y / x * y}.
Proof.
  move=> x y.
  rewrite /gaussNorm /gaussNorm /gaussNorm rmorphM mulrA
    -(mulrA x x^*) (mulrC x^* y) mulrA mulrA //.
Qed.

Lemma rev_unitrPr (R : comUnitRingType) (x y : R) :
   x * y = 1 -> x \is a GRing.unit.
Proof. by move=> ?; apply/unitrPr; exists y. Qed.

Lemma eq_algC a b :
  (a == b :> algC) = ('Re a == 'Re b) && ('Im a == 'Im b).
Proof.
rewrite -subr_eq0 [a - b]algCrect -normr_eq0 -sqrf_eq0.
rewrite normC2_rect ?paddr_eq0 ?sqr_ge0 -?realEsqr ?Creal_Re ?Creal_Im //.
by rewrite !sqrf_eq0 !raddfB ?subr_eq0.
Qed.

Lemma primitive_root_i : 4.-primitive_root 'i.
Proof.

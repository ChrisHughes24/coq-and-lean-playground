
From mathcomp Require Import all_algebra all_ssreflect.
Import GRing.Theory.

Print mulf_eq0.

(* Incantation for configuration of implicit arguments inference. *)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.

Lemma even_add_of_even_sq_add_sq (n m : int) : (2 %| n ^+ 2 + m ^+ 2)%Z = (2 %| n + m)%Z.
Proof.
rewrite !(sameP dvdz_mod0P eqP). (* exposes explicit remainders *)
rewrite -[in LHS]modzDm -[in RHS]modzDm -(modzXm _ n) -(modzXm _ m). (* congruences *)
set x := (n %% 2)%Z; set y := (m %% 2)%Z.
have : 0 <= x < 2 by rewrite ltz_pmod ?modz_ge0.
have : 0 <= y < 2 by rewrite ltz_pmod ?modz_ge0.
case: x => // x; case: y => // y. (* x and y are now nats *)
(* 2 nested case analysis on x and y to deploy the 4 cases and close the others *)
case: x => [| [|x]]; case: y => [| [|y]] //.
Qed.

Theorem sq_add_sq_of_two_mul_sq_add_sq (m x y : int) (h : (2 : int) * m = x ^+ 2 + y ^+ 2) :
  m = ((x - y)%/ 2)%Z ^+ 2 + ((x + y) %/ 2)%Z ^+ 2.
Proof.
  have h1 : (2 %| (x ^+ 2 + y ^+ 2))%Z.
    rewrite -h.
    apply dvdz_mulr.
    apply dvdzz.
  have h2 : (2 %| (x + y))%Z.
    rewrite -even_add_of_even_sq_add_sq.
    exact h1.
  have h3 : (2 %| (x - y))%Z.
    rewrite -even_add_of_even_sq_add_sq sqrrN.
    exact h1.
  have h20 : (2 : int) * 2 != 0.
    move => //=.
  apply (mulIf h20).
  have h4 : m * ((2 : int) * 2) = (x - y) ^+ 2 + (x + y) ^+ 2.
    rewrite mulrA mulrC mulrA h !expr2 mulz2 !mulrDl !mulrDr !addrA
      !mulrN !mulNr !opprK !(mulrC y) !(addrAC _ _ (x * y))
      (addrC (x * x) (x * y)) !(addrAC _ _ (x * y))
      !(addrAC _ _ (-(x*y))) addrN sub0r addNr add0r.
    reflexivity.
  have h5 : (x - y) ^+ 2 + (x + y) ^+ 2 =
      ((2 : int) * ((x - y) %/ 2)%Z)^+2 + ((2 : int) * ((x + y) %/ 2)%Z)^+2.
    rewrite (mulz_divA _ h3) (mulz_divA _ h2) !(mulKz) //.
  have h6 : ((2 : int) * ((x - y) %/ 2)%Z)^+2 + ((2 : int) * ((x + y) %/ 2)%Z)^+2 =
      (2 : int) * 2 * (((x - y) %/ 2)%Z ^+ 2 + ((x + y) %/ 2)%Z ^+ 2).
    rewrite exprMn_comm.
    rewrite exprMn_comm.
    rewrite mulrDr //.
    apply mulrC.
    apply mulrC.
  rewrite h4 h5 h6 mulrC //.
Qed.

Search (_ - _ == 0).

Theorem eq_or_eq_of_sq_eq_sq (p : nat) (x y : 'F_p) (h : x^+2 = y^+2) : 
  x = y \/ x = -y.
Proof.
  have h1 : (x - y) * (x + y) == 0.
    rewrite mulrDl !mulrDr -expr2 h expr2 mulNr (mulrC y x) addrA
      -(addrA (y * y)) subrr addr0 mulNr subrr //.
  rewrite mulf_eq0 subr_eq0 addr_eq0 in h1.
  move : h1 => /orP [/eqP <- //= |/eqP <- //=].
  left => //. right => //.
Qed.

Theorem exists_sq_add_sq_eq_one_mod_p (p : nat) (hp : prime p) :
  exists a b : 'F_p, a^+2 + b^+2 = 1.
Proof.
  case (even_prime hp).
    move => ->.
    exists 0, 1 => //.

    move => hop.
    Print sameP.
    have hpa : partition [set [set y | y^+2 == x^+2] | x : 'F_p] setT.
      apply /andP.
      split.
      apply /eqP => //=.
      rewrite -setP.
      move => x.
      rewrite in_setT /cover.
      apply /bigcupP => /=.
      exists [set y | y^+2 == x^+2].
      apply /imsetP.
      exists x => //=.
      rewrite in_set //.
      apply /andP.
      split.
      apply /trivIsetP =>/=.
      move => s t /imsetP .
      case => x hx -> /imsetP.
      case => y hy -> h.
      rewrite -setI_eq0 -subset0.
      apply /subsetP => z.
      rewrite in_setI in_set in_set.
      move => /andP [/eqP hz1 /eqP hz2].
      rewrite -hz1 -hz2 eq_refl // in h.
      apply /imsetP.
      move => [x hx1 /eqP hx2].
      rewrite eq_sym -subset0 in hx2.
      move : hx2.
      move => /subsetP hx2.
      have hx0 : x \in set0.
        apply hx2.
        rewrite in_set //.
      rewrite in_set0 // in hx0.
  have h2 : (#|'F_p| <= \sum_(A in [set [set y | y ^+ 2 == x ^+ 2] | x : 'F_p]) 2)%N.
    rewrite -cardsT (card_partition hpa).
    apply leq_sum => x // /imsetP [y hx1 ->].
    have hset_eq: [set y0 | y0 ^+ 2 == y ^+ 2] = y |: [set (-y)].
    apply /setP => z.
    rewrite !in_set.
    apply /idP /idP.
    move => /eqP h.
    case : (eq_or_eq_of_sq_eq_sq h) => -> //.
    rewrite eq_refl //=.
    rewrite eq_refl orbT //.
    move => /orP [/eqP -> // | /eqP ->].
    rewrite !expr2 mulrN mulNr opprK //.
    rewrite hset_eq cardsU cards1 cards1.
    apply leq_subr.
  rewrite sum_nat_const in h2.
  have h4 : #|[set [set y | y ^+ 2 == x ^+ 2] | x : 'F_p]| = 
    #|[set x^+2 | x : 'F_p]|.
    About imset_injP.
Qed.

From mathcomp Require Import all_ssreflect all_algebra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Module DefinitionMatrices.

Reserved Notation "''M[' R ]_ n"
  (at level 8, n at level 2, format "''M[' R ]_ n").
Reserved Notation "''M[' R ]_ ( m , n )"
  (at level 8, format "''M[' R ]_ ( m ,  n )").

Reserved Notation "\matrix_ ( i , j ) E"
  (at level 36, E at level 36, i, j at level 50,
   format "\matrix_ ( i ,  j )  E").

Reserved Notation "x %:M"   (at level 8, format "x %:M").
Reserved Notation "A *m B" (at level 40, left associativity, format "A  *m  B").
Reserved Notation "A ^T"    (at level 8, format "A ^T").
Reserved Notation "\tr A"   (at level 10, A at level 8, format "\tr  A").

Inductive matrix (R : Type) (m n : nat) : Type :=
  Matrix of {ffun 'I_m * 'I_n -> R}.

Notation "''M[' R ]_ ( m , n )" := (matrix R m n) : type_scope.
Notation "''M[' R ]_ n" := 'M[R]_(n, n) : type_scope.

(* Test *)
Check 'M[nat]_(2,3).
Check 'M[nat]_2.

Definition mx_val R m n (A : 'M[R]_(m,n)) : {ffun 'I_m * 'I_n -> R} :=
  let: Matrix g := A in g.

Canonical matrix_subType R m n :=
  Eval hnf in [newType for @mx_val R m n].

Definition matrix_eqMixin (R : eqType) m n :=
  Eval hnf in [eqMixin of 'M[R]_(m, n) by <:].
Canonical matrix_eqType (R : eqType) m n:=
  Eval hnf in EqType 'M[R]_(m, n) (matrix_eqMixin R m n).
Definition matrix_choiceMixin (R : choiceType) m n :=
  [choiceMixin of 'M[R]_(m, n) by <:].
Canonical matrix_choiceType (R : choiceType) m n :=
  Eval hnf in ChoiceType 'M[R]_(m, n) (matrix_choiceMixin R m n).
Definition matrix_countMixin (R : countType) m n :=
  [countMixin of 'M[R]_(m, n) by <:].
Canonical matrix_countType (R : countType) m n :=
  Eval hnf in CountType 'M[R]_(m, n) (matrix_countMixin R m n).
Canonical matrix_subCountType (R : countType) m n :=
  Eval hnf in [subCountType of 'M[R]_(m, n)].
Definition matrix_finMixin (R : finType) m n :=
  [finMixin of 'M[R]_(m, n) by <:].
Canonical matrix_finType (R : finType) m n :=
  Eval hnf in FinType 'M[R]_(m, n) (matrix_finMixin R m n).

Check [eqType of 'M[nat]_2].
Check forall A : 'M[nat]_2, A == A.

Check forall AA : 'M[ 'M[nat]_3 ]_2, AA == AA.

Locate ":&:".
Locate "(_ :=: _)%MS".
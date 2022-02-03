From Param Require Import Param.

Inductive nat : Set :=
| zero : nat
| succ : nat -> nat.

Inductive T (X Y : Type) : Type := 
| Tmk (f : (Y -> Type) -> (X -> Type)) (hf : forall s t, (forall y, s y -> t y) -> forall x, f s x -> f t x) : T X Y.


Inductive S : Type :=
| mk : forall (A : Type) (R : A -> A -> Type), S.

Definition R (X Y : Type) : Type := X -> Y -> Type.

Definition P (F : Type -> Type) (Z : Type) := 
  forall (X : Type), (X -> Z) -> (F X -> F Z).

Definition O :=
  forall (X : Type), ((X -> False) -> X) -> X.

Inductive N : Type :=
Nmk (X : Type) (x : X) (f : X -> X) : N.

Definition J (X : Type) : Type := (X -> bool -> X) -> X.

Definition I (F G : Type -> Type) (Y : Type) := 
  forall X, (X -> Y) -> (F X -> G Y).

Parametricity eq as eq_param arity 1.
Parametricity eq as eq_param2 arity 2.
Parametricity bool as boolp arity 2.
Parametricity N as N_param arity 1.
Parametricity T as T_param arity 2.

Print T_param.
Parametricity S as S_param arity 2.
Print S_param.
Parametricity R as R_param arity 2.
Print R_param.
Parametricity R_param as R_param_param arity 2.
Print R_param_param.
Parametricity P as P_param arity 2.
Print P_param.
Parametricity O as O_param arity 2.
Print O_param.
Parametricity option as option_param arity 2.
Parametricity N as N_param arity 2.
Print N_param.
Parametricity N_param as N_pparam arity 2.
Print N_pparam.

(* Inductive Q : Type :=
| Qmk : forall (A : Type) (f : A -> A), Q. *)

Inductive Q : Type :=
| Qmk : forall (A : Type) (zero : A) (succ : A -> A), Q.

Parametricity Q as Q_param arity 2.
Print eq_param.
Print Q_param.

Definition funextl : Type := 
forall (A B : Type) 
(f g : A -> B), (forall a : A, f a = g a) -> f = g.

Parametricity funextl as funext_param arity 2. 

Print funext_param.


Check T_param.
Print T_param.
Print T'_param.

Parametricity nat as nat_param arity 1.
Parametricity Coq.Init.Logic.eq as eqparam arity 2.
Parametricity bool as bool1 arity 1.
Parametricity bool as bool2 arity 2.
Parametricity sigT as sigma2 arity 2.
Parametricity 

Print sigma2.

Param

Print bool1.
Print bool2.

Parametricity T as T2 arity 2.
Print T2.
Parametricity T' as T'2 arity 2.
Print eqparam.
Print T'2.

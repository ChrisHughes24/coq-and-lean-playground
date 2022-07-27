import category_theory.adjunction

open category_theory

structure System : Type 1 :=
{ι κ : Type} (C : ι → Type)
[inst : Π i, category.{0} (C i)]
(Func : ι → ι → Type) (F : Π {i j}, Func i j → C i ⥤ C j)
(Adjs : Π {i j} (left : Func i j) (right : Func j i), Prop)
(isAdj : Π {i j} (left : Func i j) (right : Func j i),
  Adjs left right → (F left ⊣ F right))
(newRAdj : Π {i j}, Func i j → Prop)

attribute [instance] System.inst

variable {Γ : System}

inductive Free : bool → Γ.ι → Type
| ofOld {i : Γ.ι} : Γ.C i → Free ff i
| newAdj {i j : Γ.ι} {b : bool} (F : Γ.Func i j) (hF : Γ.newRAdj F) :
    Free b j → Free tt i
| func {i j : Γ.ι} (F : Γ.Func i j) : Free tt i → Free tt j

inductive HomAux : Π {i : Γ.ι} {bX bY : bool} (X : Free bX i) (Y : Free bY i), Type
| ofOld {i : Γ.ι} {X Y : Γ.C i} (f : X ⟶ Y) : HomAux (Free.ofOld X) (Free.ofOld Y)
| funcMap {i j : Γ.ι} {X Y : Free tt i} (F : Γ.Func i j) (f : HomAux X Y) :
    HomAux (Free.func F X) (Free.func F Y)
| rAdjMap {i j : Γ.ι} {bX bY : bool} {X : Free bX j} {Y : Free bY j}
  (F : Γ.Func i j) (hF : Γ.newRAdj F)
  (f : HomAux X Y) : HomAux (Free.newAdj F hF X) (Free.newAdj F hF Y)
| oldCounit {i j : Γ.ι} {X : Free tt j} (F : Γ.Func i j) (G : Γ.Func j i)
  (h : Γ.Adjs F G) : HomAux (Free.func F (Free.func G X)) X
| newCounit {i j : Γ.ι} {b : bool} (X : Free b j) (F : Γ.Func i j) (hF : Γ.newRAdj F) :
  HomAux (Free.func F (Free.newAdj F hF X)) X
| oldRestrict {i j : Γ.ι} {X : Free tt j} {b : bool} {Y : Free b j} 
  (F : Γ.Func i j) (G : Γ.Func j i) (h : Γ.Adjs F G) (f : HomAux ): 

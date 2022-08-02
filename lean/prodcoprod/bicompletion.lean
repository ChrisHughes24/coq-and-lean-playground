import category_theory.limits.has_limits

open category_theory

variables (C : Type) [category.{0} C]

inductive prod_coprod_completion : Type 1
| of_cat : C → prod_coprod_completion
| prod {D : Type} (F : D → prod_coprod_completion) : prod_coprod_completion
| coprod {D : Type} (F : D → prod_coprod_completion) : prod_coprod_completion

open prod_coprod_completion

notation `PCC` := prod_coprod_completion

inductive hom_aux : Π (X Y : PCC C), Type 1
| id (X : PCC C) : hom_aux X X
| comp {X Y Z : PCC C} : hom_aux X Y → hom_aux Y Z → hom_aux X Z
| of_cat {X Y : C} : (X ⟶ Y) → hom_aux (of_cat X) (of_cat Y)
| prod_cone {D : Type} (obj : D → PCC C) {X : D} :
  hom_aux (prod obj) (obj X)
| coprod_cone {D : Type} (obj : D → PCC C) {X : D} :
  hom_aux (obj X) (coprod obj)
| prod_mk {D : Type} (obj : D → PCC C) {X : PCC C}
  (f : ∀ d : D, hom_aux X (obj d)) :
  hom_aux X (prod obj)
| coprod_mk {D : Type} (obj : D → PCC C) {X : PCC C}
  (f : ∀ d : D, hom_aux (obj d) X) : hom_aux (prod obj) X

def bicompletion_aux (C : Type) [category.{0} C] : Type 1 :=
Σ (α : Type) (a : α), PCC C

notation `BCA` := bicompletion_aux

inductive hom_aux : BCA C → BCA C → Type
| id (X : BCA C) : hom_aux X X
| comp {X Y Z : BCA C} : hom_aux X Y → hom_aux Y Z → hom_aux X Z
| of_cat {X Y : C} : (X ⟶ Y) → hom_aux _ _

inductive rel :
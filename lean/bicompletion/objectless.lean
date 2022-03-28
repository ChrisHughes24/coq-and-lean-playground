import category_theory.adjunction.basic
import category_theory.limits.has_limits
import data.pfun

open category_theory category_theory.functor category_theory.limits
universes u v
variables (𝒞 : Type) [category.{0} 𝒞]
#print limit


inductive bicompletion_hom : Type 1
| of_cat_hom : Π {X Y : 𝒞}, (X ⟶ Y) → bicompletion_hom
| limit : Π (𝒟 : Type), 

inductive bicompletion_aux : bool → Type 1
| of_cat_obj : 𝒞 → bicompletion_aux ff
| limit_obj {𝒟 : Type} [category.{0} 𝒟] (F_obj : 𝒟 → bicompletion_aux ff) 
  (F_hom : Π {X Y : 𝒟}, (X ⟶ Y) → bicompletion_aux tt) : bicompletion_aux ff
| colimit_obj {𝒟 : Type} [category.{0} 𝒟] (F_obj : 𝒟 → bicompletion_aux ff) 
  (F_hom : Π {X Y : 𝒟}, (X ⟶ Y) → bicompletion_aux tt) : bicompletion_aux ff
| of_cat_hom : Π {X Y : 𝒞}, (X ⟶ Y) → bicompletion_aux tt -- of_cat_obj X ⟶ of_cat_obj Y
| limit_cone_comp {𝒟 : Type} [category.{0} 𝒟] (F_obj : 𝒟 → bicompletion_aux ff)
  (F_hom : Π {X Y : 𝒟}, (X ⟶ Y) → bicompletion_aux tt)
  (X : 𝒟) (Y : bicompletion_aux ff) (f : bicompletion_aux tt) : -- F_obj X ⟶ Y
  bicompletion_aux tt -- limit_obj F_obj F_hom ⟶ Y
| colimit_cocone_comp {𝒟 : Type} [category.{0} 𝒟] (F_obj : 𝒟 → bicompletion_aux ff) 
  (F_hom : Π {X Y : 𝒟}, (X ⟶ Y) → bicompletion_aux tt) 
  (X : 𝒟) (Y : bicompletion_aux ff) (f : bicompletion_aux tt) : -- Y ⟶ F_obj X
  bicompletion_aux tt -- Y ⟶ colimit_obj F_obj F_hom
| is_limit {𝒟 : Type} [category.{0} 𝒟] (F_obj : 𝒟 → bicompletion_aux ff) 
  (F_hom : Π {X Y : 𝒟}, (X ⟶ Y) → bicompletion_aux tt)
  (cone_obj : bicompletion_aux ff)
  (cone : Π (X : 𝒟), bicompletion_aux tt) : -- cone_obj ⟶ F_obj X
  bicompletion_aux tt -- cone_obj → limit_obj F_obj F_hom
| is_colimit {𝒟 : Type} [category.{0} 𝒟] (F_obj : 𝒟 → bicompletion_aux ff) 
  (F_hom : Π {X Y : 𝒟}, (X ⟶ Y) → bicompletion_aux tt) 
  (cocone_obj : bicompletion_aux ff)
  (cocone : Π (X : 𝒟), bicompletion_aux tt) : -- F_obj X ⟶ cocone_obj
  bicompletion_aux tt -- colimit_obj F_obj F_hom ⟶ cocone_obj
| id (X : bicompletion_aux ff) : bicompletion_aux tt -- X ⟶ X
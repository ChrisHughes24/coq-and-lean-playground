import category_theory.adjunction.basic
import category_theory.limits.has_limits
import data.pfun

open category_theory category_theory.functor category_theory.limits
universes u v
variables (𝒞 : Type) [category.{0} 𝒞]
#print is_limit
inductive bicompletion_aux : bool → Type 1
| of_cat_obj : 𝒞 → bicompletion_aux ff
| limit_obj {𝒟 : Type} [category.{0} 𝒟] (F_obj : 𝒟 → bicompletion_aux ff) 
  (F_hom : Π {X Y : 𝒟}, (X ⟶ Y) → bicompletion_aux tt) : bicompletion_aux ff
| colimit_obj {𝒟 : Type} [category.{0} 𝒟] (F_obj : 𝒟 → bicompletion_aux ff) 
  (F_hom : Π {X Y : 𝒟}, (X ⟶ Y) → bicompletion_aux tt) : bicompletion_aux ff
| of_cat_hom : Π {X Y : 𝒞}, (X ⟶ Y) → bicompletion_aux tt -- of_cat_obj X ⟶ of_cat_obj Y
| limit_cone {𝒟 : Type} [category.{0} 𝒟] (F_obj : 𝒟 → bicompletion_aux ff)
  (F_hom : Π {X Y : 𝒟}, (X ⟶ Y) → bicompletion_aux tt)
  (X : 𝒟) : bicompletion_aux tt -- limit_obj F_obj F_hom ⟶ F_obj X
| colimit_cocone {𝒟 : Type} [category.{0} 𝒟] (F_obj : 𝒟 → bicompletion_aux ff) 
  (F_hom : Π {X Y : 𝒟}, (X ⟶ Y) → bicompletion_aux tt) 
  (X : 𝒟) : bicompletion_aux tt -- F_obj X ⟶ colimit_obj F_obj F_hom
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
| comp (X Y Z : bicompletion_aux ff) (f : bicompletion_aux tt) -- X ⟶ Y
  (g : bicompletion_aux tt) : -- Y ⟶ Z 
  bicompletion_aux tt -- X ⟶ Z

namespace bicompletion_aux

variable {𝒞}

@[simp] def dom : Π (X : bicompletion_aux 𝒞 tt), bicompletion_aux 𝒞 ff
| (@of_cat_hom _ _ X Y f) := of_cat_obj X 
| (@limit_cone _ _ 𝒟 _ F_obj F_hom X) := by exactI limit_obj F_obj @F_hom
| (@is_limit _ _ 𝒟 _ F_obj F_hom cone_obj cone) := cone_obj
| (@colimit_cocone _ _ 𝒟 _ F_obj F_hom X) := F_obj X
| (@is_colimit _ _ 𝒟 _ F_obj F_hom cocone_obj cocone) := by exactI colimit_obj F_obj @F_hom
| (id X) := X
| (@comp _ _ X _ _ _ _) := X

@[simp] def cod : Π (X : bicompletion_aux 𝒞 tt), bicompletion_aux 𝒞 ff
| (@of_cat_hom _ _ X Y f) := of_cat_obj Y 
| (@colimit_cocone _ _ 𝒟 _ F_obj F_hom X) := by exactI colimit_obj F_obj @F_hom
| (@is_colimit _ _ 𝒟 _ F_obj F_hom cocone_obj cocone) := cocone_obj
| (@limit_cone _ _ 𝒟 _ F_obj F_hom X) := F_obj X
| (@is_limit _ _ 𝒟 _ F_obj F_hom cone_obj cone) := by exactI limit_obj F_obj @F_hom
| (id X) := X
| (@comp _ _ _ _ Z _ _) := Z

variable (𝒞)

inductive thing : Type 1
| obj : bicompletion_aux 𝒞 ff → thing
| hom : bicompletion_aux 𝒞 tt → thing
| pair : bicompletion_aux 𝒞 tt → bicompletion_aux 𝒞 tt → thing

variable {𝒞}

open bicompletion_aux thing
#print is_limit
inductive sub_rel : thing 𝒞 → Prop
| of_cat_obj : Π (X : 𝒞), sub_rel (obj (of_cat_obj X))
| limit_obj {𝒟 : Type} [category.{0} 𝒟] 
  (F_obj : 𝒟 → bicompletion_aux 𝒞 ff) 
  (F_hom : Π {X Y : 𝒟}, (X ⟶ Y) → bicompletion_aux 𝒞 tt)
  (F_type : ∀ {X Y : 𝒟} (f : X ⟶ Y), (F_hom f).dom = F_obj X ∧ (F_hom f).cod = F_obj Y)
  (hF_obj : ∀ X : 𝒟, sub_rel (obj (F_obj X)))
  (hF_hom : ∀ {X Y : 𝒟} (f : X ⟶ Y), sub_rel (hom (F_hom f)))
  (hF_rel : ∀ {X Y Z : 𝒟} (f : X ⟶ Y) (g : Y ⟶ Z), 
    sub_rel (pair (F_hom (f ≫ g)) (comp (F_obj X) (F_obj Y) (F_obj Z) (F_hom f) (F_hom g)))) :
  sub_rel (obj (limit_obj F_obj @F_hom))
| colimit_obj {𝒟 : Type} [category.{0} 𝒟] 
  (F_obj : 𝒟 → bicompletion_aux 𝒞 ff) 
  (F_hom : Π {X Y : 𝒟}, (X ⟶ Y) → bicompletion_aux 𝒞 tt)
  (F_type : ∀ {X Y : 𝒟} (f : X ⟶ Y), (F_hom f).dom = F_obj X ∧ (F_hom f).cod = F_obj Y)
  (hF_obj : ∀ X : 𝒟, sub_rel (obj (F_obj X)))
  (hF_hom : ∀ {X Y : 𝒟} (f : X ⟶ Y), sub_rel (hom (F_hom f)))
  (hF_rel : ∀ {X Y Z : 𝒟} (f : X ⟶ Y) (g : Y ⟶ Z), 
    sub_rel (pair (F_hom (f ≫ g)) (comp (F_obj X) (F_obj Y) (F_obj Z) (F_hom f) (F_hom g)))) :
  sub_rel (obj (colimit_obj F_obj @F_hom))
| of_cat_hom : ∀ {X Y : 𝒞} (f : X ⟶ Y), sub_rel (hom (of_cat_hom f))
| limit_cone {𝒟 : Type} [category.{0} 𝒟] 
  (F_obj : 𝒟 → bicompletion_aux 𝒞 ff)
  (F_hom : Π {X Y : 𝒟}, (X ⟶ Y) → bicompletion_aux 𝒞 tt)
  (F_type : ∀ {X Y : 𝒟} (f : X ⟶ Y), (F_hom f).dom = F_obj X ∧ (F_hom f).cod = F_obj Y)
  (X : 𝒟) 
  (hF_obj : ∀ X : 𝒟, sub_rel (obj (F_obj X)))
  (hF_hom : ∀ {X Y : 𝒟} (f : X ⟶ Y), sub_rel (hom (F_hom f)))
  (hF_rel : ∀ {X Y Z : 𝒟} (f : X ⟶ Y) (g : Y ⟶ Z), 
    sub_rel (pair (F_hom (f ≫ g)) (comp (F_obj X) (F_obj Y) (F_obj Z) (F_hom f) (F_hom g)))) :
  sub_rel (hom (limit_cone F_obj @F_hom X))
| colimit_cone {𝒟 : Type} [category.{0} 𝒟] 
  (F_obj : 𝒟 → bicompletion_aux 𝒞 ff)
  (F_hom : Π {X Y : 𝒟}, (X ⟶ Y) → bicompletion_aux 𝒞 tt)
  (F_type : ∀ {X Y : 𝒟} (f : X ⟶ Y), (F_hom f).dom = F_obj X ∧ (F_hom f).cod = F_obj Y)
  (X : 𝒟)
  (hF_obj : ∀ X : 𝒟, sub_rel (obj (F_obj X)))
  (hF_hom : ∀ {X Y : 𝒟} (f : X ⟶ Y), sub_rel (hom (F_hom f)))
  (hF_rel : ∀ {X Y Z : 𝒟} (f : X ⟶ Y) (g : Y ⟶ Z), 
    sub_rel (pair (F_hom (f ≫ g)) (comp (F_obj X) (F_obj Y) (F_obj Z) (F_hom f) (F_hom g)))) :
  sub_rel (hom (colimit_cocone F_obj @F_hom X))
| is_limit {𝒟 : Type} [category.{0} 𝒟] (F_obj : 𝒟 → bicompletion_aux 𝒞 ff)
  (F_hom : Π {X Y : 𝒟}, (X ⟶ Y) → bicompletion_aux 𝒞 tt)
  (F_type : ∀ {X Y : 𝒟} (f : X ⟶ Y), (F_hom f).dom = F_obj X ∧ (F_hom f).cod = F_obj Y)
  (cone_obj : bicompletion_aux 𝒞 ff)
  (cone : Π (X : 𝒟), bicompletion_aux 𝒞 tt)
  (cone_type : ∀ (X : 𝒟), (cone X).dom = cone_obj ∧ (cone X).cod = F_obj X)
  (hF_obj : ∀ X : 𝒟, sub_rel (obj (F_obj X)))
  (hF_hom : ∀ {X Y : 𝒟} (f : X ⟶ Y), sub_rel (hom (F_hom f)))
  (hF_rel : ∀ {X Y Z : 𝒟} (f : X ⟶ Y) (g : Y ⟶ Z), 
    sub_rel (pair (F_hom (f ≫ g)) (comp (F_obj X) (F_obj Y) (F_obj Z) (F_hom f) (F_hom g))))
  (hcone_obj : sub_rel (obj cone_obj))
  (hcone : ∀ (X : 𝒟), sub_rel (hom (cone X))) 
  (cone_rel : ∀ (X Y : 𝒟) (f : X ⟶ Y), 
    sub_rel (pair (cone Y) (comp cone_obj (F_obj X) (F_obj Y) (cone X) (F_hom f)))) : 
  sub_rel (hom (is_limit F_obj @F_hom cone_obj cone))
| is_colimit {𝒟 : Type} [category.{0} 𝒟] (F_obj : 𝒟 → bicompletion_aux 𝒞 ff)
  (F_hom : Π {X Y : 𝒟}, (X ⟶ Y) → bicompletion_aux 𝒞 tt)
  (F_type : ∀ {X Y : 𝒟} (f : X ⟶ Y), (F_hom f).dom = F_obj X ∧ (F_hom f).cod = F_obj Y)
  (cocone_obj : bicompletion_aux 𝒞 ff)
  (cocone : Π (X : 𝒟), bicompletion_aux 𝒞 tt)
  (cocone_type : ∀ (X : 𝒟), (cocone X).dom = F_obj X ∧ (cocone X).cod = cocone_obj)
  (hF_obj : ∀ X : 𝒟, sub_rel (obj (F_obj X)))
  (hF_hom : ∀ {X Y : 𝒟} (f : X ⟶ Y), sub_rel (hom (F_hom f)))
  (hF_rel : ∀ {X Y Z : 𝒟} (f : X ⟶ Y) (g : Y ⟶ Z), 
    sub_rel (pair (F_hom (f ≫ g)) (comp (F_obj X) (F_obj Y) (F_obj Z) (F_hom f) (F_hom g))))
  (hcocone_obj : sub_rel (obj cocone_obj))
  (hcocone : ∀ (X : 𝒟), sub_rel (hom (cocone X)))
  (cocone_rel : ∀ (X Y : 𝒟) (f : X ⟶ Y), 
    sub_rel (pair (cocone X) (comp (F_obj X) (F_obj Y) cocone_obj (F_hom f) (cocone Y)))) : 
  sub_rel (hom (is_colimit F_obj @F_hom cocone_obj cocone))
| id : Π (X : bicompletion_aux 𝒞 ff), sub_rel (obj X) → sub_rel (hom (id X))
| comp : Π {X Y Z : bicompletion_aux 𝒞 ff} (f g : bicompletion_aux 𝒞 tt)
  (f_type : f.dom = X ∧ f.cod = Y) (g_type : g.dom = X ∧ g.cod = Y)
  (hf : sub_rel (hom f)) (hg : sub_rel (hom g)),
  sub_rel (hom (comp X Y Z f g))
| of_cat_hom_rel_id : ∀ {X : 𝒞}, sub_rel (pair (of_cat_hom (𝟙 X)) (id (of_cat_obj X)))
| of_cat_hom_rel_comp : ∀ {X Y Z : 𝒞} (f : X ⟶ Y) (g : Y ⟶ Z), 
    sub_rel (pair (of_cat_hom (f ≫ g)) 
      (comp (of_cat_obj X) (of_cat_obj Y) (of_cat_obj Z) (of_cat_hom f) (of_cat_hom g)))
| limit_cone_rel {𝒟 : Type} [category.{0} 𝒟] 
  (F_obj : 𝒟 → bicompletion_aux 𝒞 ff)
  (F_hom : Π {X Y : 𝒟}, (X ⟶ Y) → bicompletion_aux 𝒞 tt)
  (F_type : ∀ {X Y : 𝒟} (f : X ⟶ Y), (F_hom f).dom = F_obj X ∧ (F_hom f).cod = F_obj Y)
  (X Y : 𝒟) (f : X ⟶ Y) 
  (hF_obj : ∀ X : 𝒟, sub_rel (obj (F_obj X)))
  (hF_hom : ∀ {X Y : 𝒟} (f : X ⟶ Y), sub_rel (hom (F_hom f)))
  (hF_rel : ∀ {X Y Z : 𝒟} (f : X ⟶ Y) (g : Y ⟶ Z), 
    sub_rel (pair (F_hom (f ≫ g)) (comp (F_obj X) (F_obj Y) (F_obj Z) (F_hom f) (F_hom g)))) :
  sub_rel (pair (limit_cone F_obj @F_hom Y) 
    (comp (limit_obj F_obj @F_hom) (F_obj X) (F_obj Y) (limit_cone F_obj @F_hom X) (F_hom f)))
| colimit_cocone_rel {𝒟 : Type} [category.{0} 𝒟] 
  (F_obj : 𝒟 → bicompletion_aux 𝒞 ff)
  (F_hom : Π {X Y : 𝒟}, (X ⟶ Y) → bicompletion_aux 𝒞 tt)
  (F_type : ∀ {X Y : 𝒟} (f : X ⟶ Y), (F_hom f).dom = F_obj X ∧ (F_hom f).cod = F_obj Y)
  (X Y : 𝒟) (f : X ⟶ Y) 
  (hF_obj : ∀ X : 𝒟, sub_rel (obj (F_obj X)))
  (hF_hom : ∀ {X Y : 𝒟} (f : X ⟶ Y), sub_rel (hom (F_hom f)))
  (hF_rel : ∀ {X Y Z : 𝒟} (f : X ⟶ Y) (g : Y ⟶ Z), 
    sub_rel (pair (F_hom (f ≫ g)) (comp (F_obj X) (F_obj Y) (F_obj Z) (F_hom f) (F_hom g)))) :
  sub_rel (pair  
    (comp (F_obj X) (F_obj Y) (colimit_obj F_obj @F_hom) (F_hom f) (colimit_cocone F_obj @F_hom Y))
    (colimit_cocone F_obj @F_hom X))

end bicompletion_aux

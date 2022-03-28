import category_theory.limits.preserves.basic

/- 
  Take category of small categories with chosen limits and colimits,
  and a fully faithful morphism from starting category. 
  There is a functor from here to the category of large locally small categories.
  Take colimit of this. 

  This colimit is filtered. Why?
  Therefore for any diagram
-/

open category_theory category_theory.limits

variables {𝒞 : Type} [category.{0} 𝒞]

inductive in_biclosure {𝒟 : Type} [category.{0} 𝒟] (F : 𝒞 ⥤ 𝒟) : Π {X Y : 𝒟}, (X ⟶ Y) → Type 1
| of_cat : Π {X Y: 𝒞} (f : X ⟶ Y), in_biclosure (F.map f)
| limit (ℰ : Type) [category.{0} ℰ] (D : ℰ ⥤ 𝒟) 
  (L : limit_cone D) (C : cone D)
  (hD : ∀ {X Y : ℰ} (f : X ⟶ Y), in_biclosure (D.map f))
  (hC : ∀ X : ℰ, in_biclosure (C.π.app X)) : 
  in_biclosure (L.is_limit.lift C)
| colimit (ℰ : Type) [category.{0} ℰ] (D : ℰ ⥤ 𝒟) 
  (L : colimit_cocone D) (C : cocone D)
  (hD : ∀ {X Y : ℰ} (f : X ⟶ Y), in_biclosure (D.map f))
  (hC : ∀ X : ℰ, in_biclosure (C.ι.app X)) :
  in_biclosure (L.is_colimit.desc C)

variable (𝒞)

@[protect_proj] structure thing : Type 1 :=
(𝒟 : Type)
[𝒟_cat : category.{0} 𝒟]
(of_cat : 𝒞 ⥤ 𝒟)
(full : full of_cat)
(faithful : faithful of_cat)
(ι : Type)
(limit_diag : ι → Type )
[limit_cat : Π (i : ι), category.{0} (limit_diag i)]
(limit_functor : Π (i : ι), limit_diag i ⥤ 𝒟)
(has_limit : Π (i : ι), has_limit (limit_functor i))
(κ : Type)
(colimit_diag : κ → Type)
[colimit_cat : Π (i : κ), category.{0} (colimit_diag i)]
(colimit_functor : Π (i : κ), colimit_diag i ⥤ 𝒟)
(has_colimit : Π (i : κ), has_colimit (colimit_functor i))
(in_biclosure : ∀ {X Y : 𝒟} (f : X ⟶ Y), in_biclosure of_cat f)

namespace thing

attribute [instance] thing.𝒟_cat thing.limit_cat thing.colimit_cat

variable {𝒞}

-- inductive coproduct_hom {ι : Type} (D : ι → thing 𝒞) : Π {i j : ι} (X : (D i).𝒟) (Y : (D j).𝒟), Type
-- | basic : Π {i : ι} {X Y : (D i).𝒟} (f : X ⟶ Y), coproduct_hom X Y
-- | is_limit {i j : ι} (lim : (D i).ι) (cone : (D j).𝒟) 
--     (is_cone : Π (x : (D i).limit_diag lim), coproduct_hom cone (((D i).limit_functor lim).obj x)) 
--     (commutes : Π (x y : (D i).limit_diag lim) (f : x ⟶ y), 
--       is_cone x ≫ ((D i).limit_functor lim).map f = is_cone y): 

def coproduct {ι : Type} (D : ι → thing 𝒞) : thing 𝒞 :=
{ 𝒟 := Σ i : ι, (D i).𝒟 }

structure hom (X Y : thing 𝒞) : Type :=
( functor : X.𝒟 ⥤ Y.𝒟 )
( full : full functor )
( faithful : faithful functor )
( commutes : X.of_cat ⋙ functor ≅ Y.of_cat )
( preserves_limits : Π (i : X.ι), preserves_limit (X.limit_functor i) functor )
( preserves_colimits : Π (i : X.κ), preserves_colimit (X.colimit_functor i) functor )
 


end thing

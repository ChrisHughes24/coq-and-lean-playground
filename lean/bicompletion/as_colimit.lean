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

variables {đ : Type} [category.{0} đ]

inductive in_biclosure {đ : Type} [category.{0} đ] (F : đ â„€ đ) : Î  {X Y : đ}, (X â¶ Y) â Type 1
| of_cat : Î  {X Y: đ} (f : X â¶ Y), in_biclosure (F.map f)
| limit (â° : Type) [category.{0} â°] (D : â° â„€ đ) 
  (L : limit_cone D) (C : cone D)
  (hD : â {X Y : â°} (f : X â¶ Y), in_biclosure (D.map f))
  (hC : â X : â°, in_biclosure (C.Ï.app X)) : 
  in_biclosure (L.is_limit.lift C)
| colimit (â° : Type) [category.{0} â°] (D : â° â„€ đ) 
  (L : colimit_cocone D) (C : cocone D)
  (hD : â {X Y : â°} (f : X â¶ Y), in_biclosure (D.map f))
  (hC : â X : â°, in_biclosure (C.Îč.app X)) :
  in_biclosure (L.is_colimit.desc C)

variable (đ)

@[protect_proj] structure thing : Type 1 :=
(đ : Type)
[đ_cat : category.{0} đ]
(of_cat : đ â„€ đ)
(full : full of_cat)
(faithful : faithful of_cat)
(Îč : Type)
(limit_diag : Îč â Type )
[limit_cat : Î  (i : Îč), category.{0} (limit_diag i)]
(limit_functor : Î  (i : Îč), limit_diag i â„€ đ)
(has_limit : Î  (i : Îč), has_limit (limit_functor i))
(Îș : Type)
(colimit_diag : Îș â Type)
[colimit_cat : Î  (i : Îș), category.{0} (colimit_diag i)]
(colimit_functor : Î  (i : Îș), colimit_diag i â„€ đ)
(has_colimit : Î  (i : Îș), has_colimit (colimit_functor i))
(in_biclosure : â {X Y : đ} (f : X â¶ Y), in_biclosure of_cat f)

namespace thing

attribute [instance] thing.đ_cat thing.limit_cat thing.colimit_cat

variable {đ}

-- inductive coproduct_hom {Îč : Type} (D : Îč â thing đ) : Î  {i j : Îč} (X : (D i).đ) (Y : (D j).đ), Type
-- | basic : Î  {i : Îč} {X Y : (D i).đ} (f : X â¶ Y), coproduct_hom X Y
-- | is_limit {i j : Îč} (lim : (D i).Îč) (cone : (D j).đ) 
--     (is_cone : Î  (x : (D i).limit_diag lim), coproduct_hom cone (((D i).limit_functor lim).obj x)) 
--     (commutes : Î  (x y : (D i).limit_diag lim) (f : x â¶ y), 
--       is_cone x â« ((D i).limit_functor lim).map f = is_cone y): 

def coproduct {Îč : Type} (D : Îč â thing đ) : thing đ :=
{ đ := ÎŁ i : Îč, (D i).đ }

structure hom (X Y : thing đ) : Type :=
( functor : X.đ â„€ Y.đ )
( full : full functor )
( faithful : faithful functor )
( commutes : X.of_cat â functor â Y.of_cat )
( preserves_limits : Î  (i : X.Îč), preserves_limit (X.limit_functor i) functor )
( preserves_colimits : Î  (i : X.Îș), preserves_colimit (X.colimit_functor i) functor )
 


end thing

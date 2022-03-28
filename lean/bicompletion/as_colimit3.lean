import category_theory.limits.preserves.basic

open category_theory category_theory.limits

variables (𝓒 : Type) [category.{0} 𝓒]

section adjoin_limit

structure limits :=
(ι : Type)
(diag : ι → Type)
[cat : Π (i : ι), category.{0} (diag i)]
(F : Π (i : ι), diag i ⥤ 𝓒)
(cones : Π (i : ι), cone (F i))
(is_limit : Π (i : ι), is_limit (cones i))

structure colimits :=
(ι : Type)
(diag : ι → Type)
[cat : Π (i : ι), category.{0} (diag i)]
(F : Π (i : ι), diag i ⥤ 𝓒)
(cocones : Π (i : ι), cocone (F i))
(is_colimit : Π (i : ι), is_colimit (cocones i))

attribute [instance] colimits.cat limits.cat

variable {𝓒}

def adjoin_limit {𝓓 : Type} [category.{0} 𝓓] (F : 𝓓 ⥤ 𝓒)
  (l : limits 𝓒) (c : colimits 𝓒) : Type :=
option 𝓒

namespace adjoin_limit

variables {𝓓 : Type} [category.{0} 𝓓] {F : 𝓓 ⥤ 𝓒}
  {l : limits 𝓒} {cl : colimits 𝓒}

inductive hom : adjoin_limit F l cl → adjoin_limit F l cl → Type
| functor_end : Π (f : F ⟶ F), hom none none
| cone : Π (X : 𝓓), hom none (some (F.obj X))
| is_limit : Π (c : cone F), hom (some c.X) none

def comp : Π {X Y Z : adjoin_limit F l cl} (f : hom X Y) (g : hom Y Z), hom X Z
| _ _ _ hom.id_none g := g
| _ _ _ f hom.id_none := f
| _ _ none (hom.is_limit c) g := _

end adjoin_limit

end adjoin_limit
import category_theory.limits.preserves.basic

open category_theory category_theory.limits

variables {C ι : Type} {D : ι → Type} [category.{0} C] [Π i, category.{0} (D i)]
  (F : Π i, C ⥤ (D i))

include F
def pushout : Type := Σ i, D i

open sum
variable{F}
inductive hom : Π (A B : pushout F), Type
| inl : Π {i} {A B : D i}, (A ⟶ B) → hom ⟨i, A⟩ ⟨i, B⟩
| comp : Π {i j} {X : D i} {Y : C} {Z : D j},
  (X ⟶ (F i).obj Y) → ((F j).obj Y ⟶ Z) → 
  hom ⟨i, X⟩ ⟨j, Z⟩ 

def comp : Π {X Y Z : pushout F}, hom X Y → hom Y Z → hom X Z
| _ _ _ (@hom.inl _ _ _ _ _ _ i X Y f) 
        (@hom.inl _ _ _ _ _ _ j _ Z g) := hom.inl (f ≫ g)
| _ _ _ (@hom.inl _ _ _ _ _ _ i X Y f) 
        (@hom.comp _ _ _ _ _ _ j _ _ _ _ g h) := 
  hom.comp (f ≫ g) h
| _ _ _ (@hom.comp _ _ _ _ _ _ j _ _ _ _ g h)
        (@hom.inl _ _ _ _ _ _ i X Y f) := 
  hom.comp g (h ≫ f)
| _ _ _ (@hom.comp _ _ _ _ _ _ _ _ _ _ _ f g)
        (@hom.comp _ _ _ _ _ _ _ _ _ _ _ h i) :=
 begin
   have := g ≫ h ≫ i,
 end
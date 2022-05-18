import category_theory.abelian.basic

open category_theory

variables {ι : Type} {κ : ι → ι → Type} 
        (cat : ι → Type) [Π i, category.{0} (cat i)]
        (func : Π i j : ι, κ i j → cat i ⥤ cat j)
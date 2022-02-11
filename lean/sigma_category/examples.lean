import .struc3
open category_theory

def Magma2 : Type 1 :=
Σ (G : Type), G → G → G

def Magma_struc : struc Type :=
 struc.sigma_arrow Type (𝟭 Type) 
    (struc.sigma_arrow Type (𝟭 Type) (struc.of_functor (𝟭 Type)))


example (A B : sigma Magma_struc) : (A ⟶ B) ≃ 
  { f : A.1 → B.1 // ∀ x y, f (A.2 x y) = B.2 (f x) (f y) } :=
{ to_fun := λ f, ⟨f.1, λ x y, begin 
    cases f with f₁ f₂,

    cases A with A₁ A₂,
    cases B with B₁ B₂,
    dsimp at *,
    specialize f₂ x _ rfl,
    cases f₂ with f₂ f₃,
    dunfold quiver.hom at *,
    dsimp at *,
    have f₄ := f₃ y _ rfl,
    cases f₄,
    dsimp at *,
    
    
    
    
     end⟩  }
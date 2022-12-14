import .struc3
open category_theory

def Magma2 : Type 1 :=
Î£ (G : Type), G â G â G

def Magma_struc : struc Type :=
 struc.sigma_arrow Type (ð­ Type) 
    (struc.sigma_arrow Type (ð­ Type) (struc.of_functor (ð­ Type)))


example (A B : sigma Magma_struc) : (A â¶ B) â 
  { f : A.1 â B.1 // â x y, f (A.2 x y) = B.2 (f x) (f y) } :=
{ to_fun := Î» f, â¨f.1, Î» x y, begin 
    cases f with fâ fâ,

    cases A with Aâ Aâ,
    cases B with Bâ Bâ,
    dsimp at *,
    specialize fâ x _ rfl,
    cases fâ with fâ fâ,
    dunfold quiver.hom at *,
    dsimp at *,
    have fâ := fâ y _ rfl,
    cases fâ,
    dsimp at *,
    
    
    
    
     endâ©  }
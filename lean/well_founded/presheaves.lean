import category_theory.yoneda
open category_theory

variables (C : Type) [category.{0} C]

def thing : ((Cᵒᵖ ⥤ Type)ᵒᵖ ⥤ Type) ⥤ Cᵒᵖ ⥤ Type :=
functor.flip (functor.op yoneda ⋙ functor.flip (𝟭 ((Cᵒᵖ ⥤ Type)ᵒᵖ ⥤ Type)))

example : faithful (thing C) :=
{ map_injective' := begin
    intros X Y f g h,
    dsimp [thing] at h, 
    ext F x,
    injection h with h,
    simp [function.funext_iff] at h,
    clear h,
    tidy,
    simp [function.funext_iff] at h_1,
    
end }
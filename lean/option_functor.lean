import category_theory.functor_category

namespace category_theory

open nat_trans category category_theory.functor

structure Function : Type 1 :=
( to_fun : Type → Type )
( R : Π {X₁ X₂} (R : X₁ → X₂ → Prop), to_fun X₁ → to_fun X₂ → Prop )

instance : has_coe_to_fun Function (λ _, Type → Type) :=
{ coe := Function.to_fun }

instance : category_struct Function :=
{ hom := λ F G, { n : Π {X}, F X → G X // 
    ∀ {X₁ X₂} {R : X₁ → X₂ → Prop} {x₁ : F X₁} {x₂ : F X₂}, F.R R x₁ x₂ → G.R R (n x₁) (n x₂) },
  id := λ F, ⟨λ _, id, λ _ _ _ _ _, id⟩,
  comp := λ X Y Z n₁ n₂, ⟨λ X x, n₂.1 (n₁.1 x), λ X₁ X₂ R x₁ x₂ h, n₂.2 (n₁.2 h)⟩ } 

instance (F G : Function) : has_coe_to_fun (F ⟶ G) (λ _, Π {X}, F X → G X) :=
{ coe := subtype.val }

instance : category Function := {}



end category_theory
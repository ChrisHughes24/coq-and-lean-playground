import tactic

def square {A B : Type*} (R : A → B → Prop) : Prop :=
∀ x₁ x₂ y₁ y₂, R x₁ y₁ → R x₂ y₁ → R x₂ y₂ → R x₁ y₂

structure edge (X Y : Type) : Type :=
( R : X → Y → Prop )
( square : square R )

namespace edge

variables {X Y : Type}

def le : edge X Y → edge X Y → Prop :=
λ e₁ e₂, ∃ (f : X → X) (g : Y → Y), ∀ x y, e₁.R (f x) y ↔ e₂.R x (g y)

instance : preorder (edge X Y) :=
{ le := le,
  le_refl := λ _, ⟨id, id, λ _ _, iff.rfl⟩,
  le_trans := λ a b c ⟨f₁, g₁, h₁⟩ ⟨f₂, g₂, h₂⟩, 
    ⟨f₁ ∘ f₂, g₂ ∘ g₁, λ x y, (h₁ _ _).trans $ h₂ _ _⟩ }

def of_fun (f : X → Y) : edge X Y := 
{ R := λ x y, f x = y,
  square := λ _ _ _ _, by cc }

lemma maximal_of_fun (f : X → Y) (E : edge X Y) (h : of_fun f ≤ E) : 
  E ≤ of_fun f :=
begin
  rcases h with ⟨a, b, h⟩,
  
  refine ⟨a, b, _⟩,
  dsimp [of_fun] at *,

end 


end edge
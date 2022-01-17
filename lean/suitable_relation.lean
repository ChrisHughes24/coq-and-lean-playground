import tactic
import .scratch

open function

structure suitable (F : Type → Type) 
  (ρ : Π {X Y}, (X → Y → Prop) → (F X → F Y → Prop)) : Prop :=
(symm : Π {X Y : Type} (R : X → Y → Prop) (x : F X) (y : F Y), 
  ρ R x y → ρ (swap R) y x)
(trans : Π {X Y Z : Type} (R : X → Y → Prop) (R' : Y → Z → Prop) x y z,
  ρ R x y → ρ R' y z → ρ (λ x z, ∃ y, R x y ∧ R' y z) x z)
(desc : Π {X : Type} (R : setoid X) (s) (h : ρ R.r s s),
  ∃! (s' : F (quotient R)), ρ (λ (x : X) (y : quotient R), quotient.mk x = y) s s')

example (F ρ) (hsuit : suitable F ρ) {X Y : Type} (R : X → Y → Prop) (h : square R) :
  square (ρ R) :=
begin
  intros x₁ x₂ y₁ y₂ h₁ h₂ h₃,
  have := hsuit.trans R (swap R) _ _ _ h₁ (hsuit.symm _ _ _ h₂), 
  have := hsuit.trans _ _ _ _ _ this h₃,
  convert this,
  ext x y,
  split,
  { intros,
    use x,
    split,
    { use y,
      split, assumption, assumption },
    { assumption } },
  { rintros ⟨x', ⟨y', hy⟩, hx'y⟩,
    exact h _ _ _ _ hy.1 hy.2 hx'y }
end 

-- structure positive (F : Type → Type)
--   (ρ : Π {X Y}, (X → Y → Prop) → (F X → F Y → Prop)) : Prop :=
-- (refl : Π {X : Type}, ρ (@eq X) = eq)
-- (rev_trans : Π {X Y Z} (R : X → Y → Prop) (R' : Y → Z → Prop),
--   ρ R x z → ρ (λ x z, ∃ y, R x y ∧ R' y z) x z)

example : suitable (λ X : Type, X → X) (λ X Y R f g, ∀ x y, R x y → R (f x) (g y)) :=
{ symm := λ X Y R x y h y x, h x y,
  trans := λ X Y Z R R' a b c h₁ h₂ x z, 
    begin
      rintros ⟨y, hxy, hyz⟩,
      use b y,
      split,
      { exact h₁ _ _ hxy },
      { exact h₂ _ _ hyz }
    end,
  desc := λ X R a h, 
    ⟨@quotient.map _ _ R R a h, begin
      dsimp,
      split,
      { rintros x y rfl,
        refl },
      { intros b h,
        funext x,
        resetI,
        refine quotient.induction_on x _,
        intro x,
        rw ← h x _ rfl,
        refl } 
    end⟩ }

import tactic


-- freely adjoining a unary function to a group
inductive adjoin_fun' (G : Type) [group G] : Type
| of_group (g : G) : adjoin_fun'
| u (g : adjoin_fun') : adjoin_fun'
| mul (g h : adjoin_fun') : adjoin_fun'
| inv (g : adjoin_fun') : adjoin_fun'

variables {G : Type} [group G]

section

local notation x `*` y := adjoin_fun'.mul x y
local notation x`⁻¹` := adjoin_fun'.inv x
local notation `o` := adjoin_fun'.of_group 1

open adjoin_fun'

inductive rel : adjoin_fun' G → adjoin_fun' G → Prop
| mul_assoc (x y z) : rel (x * y * z) (x * (y * z))
| mul_inv (x) : rel (x * x⁻¹) o
| inv_mul (x) : rel (x⁻¹ * x) o
| mul_one (x) : rel (x * o) x
| one_mul (x) : rel (o * x) x
| is_hom (x y : G) : rel (of_group (has_mul.mul x y)) (of_group x * of_group y)
| mul {a₁ a₂ b₁ b₂} : rel a₁ b₁ → rel a₂ b₂ → rel (a₁ * a₂) (b₁ * b₂)
| u {a b} : rel a b → rel (u a) (u b)
| inv {a b} : rel a b → rel (a⁻¹) (b⁻¹)
| refl (x) : rel x x
| symm (x y) : rel x y → rel y x
| trans (x y z) : rel x y → rel y z → rel x z


variable (G)

instance rel_setoid : setoid (adjoin_fun' G) :=
{ r := rel, iseqv := ⟨rel.refl, rel.symm, rel.trans⟩ } 

def adjoin_fun : Type := quotient (rel_setoid G)

instance : group (adjoin_fun G) :=
{ mul := λ x y, quotient.lift_on₂ x y (λ x y, quotient.mk (x * y)) 
      (λ a₁ a₂ b₁ b₂ h₁ h₂, quotient.sound (rel.mul h₁ h₂)),
  one := quotient.mk o,
  inv := λ x, quotient.lift_on x (λ x, quotient.mk (x⁻¹)) 
    (λ a b h, quotient.sound (rel.inv h)),
  mul_assoc := λ x y z, quotient.induction_on₃ x y z
    (λ x y z, quotient.sound (rel.mul_assoc _ _ _)),
  mul_one := λ x, quotient.induction_on x 
    (λ x, quotient.sound (rel.mul_one _)),
  one_mul := λ x, quotient.induction_on x
    (λ x, quotient.sound (rel.one_mul x)),
  mul_left_inv := λ x, @quotient.induction_on (adjoin_fun' G)
    (rel_setoid G) (λ x : adjoin_fun G, 
      quotient.lift_on₂ (quotient.lift_on x (λ x, quotient.mk (x⁻¹))
      (λ a b h, quotient.sound (rel.inv h))) (x) (λ x y, quotient.mk (x * y))
      (λ a₁ a₂ b₁ b₂ h₁ h₂, quotient.sound (rel.mul h₁ h₂)) = ⟦o⟧) _ 
      (λ x, quotient.sound (rel.inv_mul _)) }

variable {G}

def of_group : G →* adjoin_fun G :=
monoid_hom.mk' 
  (λ x, ⟦of_group x⟧)
  (λ x y, quotient.sound (rel.is_hom _ _))

def u : adjoin_fun G → adjoin_fun G :=
λ x, quotient.lift_on' x (λ x, ⟦adjoin_fun'.u x⟧) 
  (λ a b h, quotient.sound (rel.u h))

end

def UMP {H : Type} [group H] (f : G →* H) 
  (u : adjoin_fun G → H → H) : adjoin_fun G →* H :=
monoid_hom.mk' 
  (λ g, quotient.lift_on g 
    (λ g, show H, from adjoin_fun'.rec_on g 
      f
      (λ g h, u ⟦g⟧ h)
      (λ _ _, (*))
      (λ _ h, h⁻¹)) 
    (λ x y hxy, begin 
      induction hxy; simp [*, mul_assoc] at *,
      rw [show ⟦hxy_a⟧ = ⟦hxy_b⟧, from quotient.sound hxy_ᾰ],
    end))
  (λ x y, quotient.induction_on₂ x y (λ x y, rfl))

example {A : Type} : (ℕ → A) ≃ (A × (ℕ → A → A)) :=
{ to_fun := λ f, (f 0, λ n _, f n.succ),
  inv_fun := λ x n, nat.rec_on n x.1 x.2,
  left_inv := λ f, begin
    dsimp,
    ext n,
    cases n,
    { refl },
    { refl },
  end,
  right_inv := begin
    rintros ⟨a, f⟩,
    ext1,
    { refl },
    { ext n,
      dsimp, }
    
  end }

def UMP' {H : Type} [group H] (f : adjoin_fun G →* H) : (G →* H) × (adjoin_fun G → H → H) :=
⟨f.comp of_group, λ g h, f (u g)⟩
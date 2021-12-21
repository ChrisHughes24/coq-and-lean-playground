import tactic

def R {A B X Y : Type}
  (a : X → A)
  (b : Y → A)
  (c : X → B)
  (d : Y → B) : X → Y → Prop :=
  λ x y, a x = b y → c x = d y

def F : Type → Type → Type :=
λ X Y, (Y → X) → X → Y

def map1 {X Y : Type} (Z : Type) (f : X → Y) : F Y Z → F X Z :=
λ g h x, g (λ z, f (h z)) (f x)

def map1_id {X : Type} (Y : Type) : map1 Y (id : X → X) = id := rfl

def map1_comp {W X Y : Type} (Z : Type) (f : W → X) (g : X → Y) :
  map1 Z (g ∘ f) = map1 Z f ∘ map1 Z g := rfl

def map2 (X : Type) {Y Z : Type} (f : Y → Z) : F X Y → F X Z :=
λ g h, (∘) f (g (h ∘ f))

def map2_id (X : Type) {Y : Type} : map1 X (id : Y → Y) = id := rfl

def map2_comp (W : Type) {X Y Z : Type} (f : X → Y) (g : Y → Z) :
  map2 X (g ∘ f) = map2 X g ∘ map2 X f := rfl

section

variables {X Y : Type} (R : X → Y → Prop)

open function sum

-- def rel : X ⊕ Y → X ⊕ Y → Prop :=
-- λ a b, ∃ x y, a = inl x ∧ b = inr y ∧ R x y

inductive rel : X ⊕ Y → X ⊕ Y → Prop
| lr : ∀ {x y}, R x y → rel (inl x) (inr y)
| rl : ∀ {x y}, R x y → rel (inr y) (inl x)
| transl : ∀ {x₁ x₂ y}, R x₁ y → R x₂ y → rel (inl x₁) (inl x₂)
| transr : ∀ {x y₁ y₂}, R x y₁ → R x y₂ → rel (inr y₁) (inr y₂)
| refll : ∀ x, rel (inl x) (inl x)
| refly : ∀ y, rel (inr y) (inr y)

example (a b c : X ⊕ Y)
  (h₁ : ∀ x₁ x₂ y₁ y₂, R x₁ y₁ → R x₂ y₁ → R x₂ y₂ → R x₁ y₂) 
  : 
  rel R a b → rel R b c → rel R a c :=
begin
  intros hab hbc,
  induction hab with x₁ y₁ hxy₁ _ _ _ x₁ x₂ y₁ hxy₁ hxy₂,
  { generalize hb : (inr y₁ : X ⊕ Y) = b,
    rw hb at hbc,
    induction hbc with _ _ _ x₂ y₂ hxy₂ _ _ _ _ _ x₂ y₂ y₃ hxy₂ hxy₃
    _ y₂,
    { injection hb },
    { injection hb,
      subst y₂,
      exact rel.transl hxy₁ hxy₂ },
    { injection hb },
    { injection hb,
      subst y₂,
      exact rel.lr (h₁ x₁ x₂ y₁ y₃ hxy₁ hxy₂ hxy₃) },
    { injection hb },
    { injection hb,
      subst y₂,
      exact rel.lr hxy₁ } },
  { admit },
  { generalize hb : (inl x₂ : X ⊕ Y) = b,
    rw hb at hbc,
    induction hbc with x₃ y₂ hxy₃,
    { injection hb,
      subst x₃,
      exact rel.lr (h₁ _ _ _ _ hxy₁ hxy₂ hxy₃) },
    {  } }

end

#print eqv_gen

example 
  (hX : is_equiv _ (λ x₁ x₂, R x₁ = R x₂))
  (hY : is_equiv _ (λ y₁ y₂, swap R y₁ = swap R y₂)) :
  ∃ (Z : Type) (f₁ : X → Z) (f₂ : Y → Z), (∀ x y, R x y ↔ f₁ x = f₂ y) :=
begin
  refine ⟨quotient (eqv_gen.setoid (rel R)), 
    quotient.mk' ∘ inl, quotient.mk' ∘ inr, _⟩,
  intros x y,
  simp only [quotient.eq'],
  split,
  { intro h,
    refine eqv_gen.rel _ _ _,
    exact ⟨x, y, rfl, rfl, h⟩ },
  { show eqv_gen (rel R) (inl x) (inr y) → _,
    intro h,
    generalize ha : (inl x : X ⊕ Y) = a,
    generalize hb : (inr y : X ⊕ Y) = b,
    rw [ha, hb] at h,
    induction h with a b hab h _ _ _ _,
    { rcases hab with ⟨hab_w, hab_h_w, rfl, rfl, hab_h_h_right_right⟩,
      simp * at * },
    { subst h,
      simp * at * },
    { substs ha hb,
      simp * at *, }
     }

end

end

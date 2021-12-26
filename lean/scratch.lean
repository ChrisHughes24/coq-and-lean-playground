import tactic

def R {A B X Y : Type}
  (a : X → A)
  (b : Y → A)
  (c : X → B)
  (d : Y → B) : X → Y → Prop :=
  λ x y, a x = b y → c x = d y

def F : Type → Type → Type :=
λ X Y, (Y → X × X) → X → Y

def map1 {X Y : Type} (Z : Type) (f : X → Y) : F Y Z → F X Z :=
λ g h x, g (λ z, (h z).map f f) (f x)

def map1_id {X : Type} (Y : Type) : map1 Y (id : X → X) = id :=
by delta id; simp [map1]

def map1_comp {W X Y : Type} (Z : Type) (f : W → X) (g : X → Y) :
  map1 Z (g ∘ f) = map1 Z f ∘ map1 Z g := rfl

def map2 (X : Type) {Y Z : Type} (f : Y → Z) : F X Y → F X Z :=
λ g h, (∘) f (g (h ∘ f))

def map2_id (X : Type) {Y : Type} : map2 X (id : Y → Y) = id := 
by funext; simp [map2]

def map2_comp (W : Type) {X Y Z : Type} (f : X → Y) (g : Y → Z) :
  map2 X (g ∘ f) = map2 X g ∘ map2 X f := rfl

section

variables {X Y : Type} (R : X → Y → Prop)

open function sum

inductive rel : X ⊕ Y → X ⊕ Y → Prop
| lr : ∀ {x y}, R x y → rel (inl x) (inr y)
| rl : ∀ {x y}, R x y → rel (inr y) (inl x)
| refl : ∀ a, rel a a
| transl : ∀ {x₁ x₂ y}, R x₁ y → R x₂ y → rel (inl x₁) (inl x₂)
| transr : ∀ {x y₁ y₂}, R x y₁ → R x y₂ → rel (inr y₁) (inr y₂)

lemma rel.symm : ∀ {a b : X ⊕ Y}, rel R a b → rel R b a
| _ _ (rel.lr h)         := rel.rl h
| _ _ (rel.rl h)         := rel.lr h
| _ _ (rel.refl _)       := rel.refl _
| _ _ (rel.transl h₁ h₂) := rel.transl h₂ h₁
| _ _ (rel.transr h₁ h₂) := rel.transr h₂ h₁

lemma rel.trans 
  (hR : ∀ {x₁ x₂ y₁ y₂}, R x₁ y₁ → R x₂ y₁ → R x₂ y₂ → R x₁ y₂) :
  ∀ {a b c : X ⊕ Y}, rel R a b → rel R b c → rel R a c
| _ _ _ (rel.refl _)       h                  := h
| _ _ _ (rel.lr h₁)        (rel.rl h₂)        := rel.transl h₁ h₂
| _ _ _ (rel.rl h₁)        (rel.lr h₂)        := rel.transr h₁ h₂
| _ _ _ (rel.lr h₁)        (rel.transr h₂ h₃) := rel.lr (hR h₁ h₂ h₃)
| _ _ _ (rel.rl h₁)        (rel.transl h₂ h₃) := rel.rl (hR h₃ h₂ h₁)
| _ _ _ (rel.transl h₁ h₂) (rel.lr h₃)        := rel.lr (hR h₁ h₂ h₃)
| _ _ _ (rel.transr h₁ h₂) (rel.rl h₃)        := rel.rl (hR h₃ h₂ h₁)
| _ _ _ (rel.transr h₁ h₂) (rel.transr h₃ h₄) := rel.transr h₁ (hR h₂ h₃ h₄)
| _ _ _ (rel.transl h₁ h₂) (rel.transl h₃ h₄) := rel.transl h₁ (hR h₄ h₃ h₂)
-- Cases below shouldn't be necessary
| _ _ _ (rel.lr h)         (rel.refl _)       := rel.lr h
| _ _ _ (rel.rl h)         (rel.refl _)       := rel.rl h
| _ _ _ (rel.transl h₁ h₂) (rel.refl _)       := rel.transl h₁ h₂
| _ _ _ (rel.transr h₁ h₂) (rel.refl _)       := rel.transr h₁ h₂

lemma R_of_rel {x : X} {y : Y} : rel R (inl x) (inr y) → R x y 
| (rel.lr h) := h

def rel_setoid (hR : ∀ x₁ x₂ y₁ y₂, R x₁ y₁ → R x₂ y₁ → R x₂ y₂ → R x₁ y₂) :
  setoid (X ⊕ Y) :=
{ r := rel R,
  iseqv := ⟨rel.refl, @rel.symm _ _ _, @rel.trans _ _ _ hR⟩ }

def square {A B : Type} (R : A → B → Prop) : Prop :=
∀ x₁ x₂ y₁ y₂, R x₁ y₁ → R x₂ y₁ → R x₂ y₂ → R x₁ y₂


example {X Y : Type} {R : X → Y → Prop} : 
  (∀ x₁ x₂ y₁ y₂, R x₁ y₁ → R x₂ y₁ → R x₂ y₂ → R x₁ y₂) ↔
  ∃ (Z : Type) (f₁ : X → Z) (f₂ : Y → Z), (∀ x y, R x y ↔ f₁ x = f₂ y) :=
begin
  split,
  { intro hR,
    refine ⟨quotient (rel_setoid R hR), 
      quotient.mk' ∘ inl, quotient.mk' ∘ inr, _⟩,
    intros x y,
    simp only [quotient.eq'],
    split,
    { exact rel.lr },
    { exact R_of_rel R } },
  { rintros ⟨Z, f₁, f₂, h⟩,
    simp only [h], cc },
end

example {X Y Z : Type} (f p : X → Y) (q g : Y → Z) : 
  g ∘ p = q ∘ f ↔ ∃ b : Y → Y, p = b ∘ f ∧ q = g ∘ b :=
begin
  split,
  { intro h,
    let P : Y → Y → Prop := (λ y y', q y = g y' ∧ ∀ x, f x = y → y' = p x),
    have h : ∀ y, ∃ y', P y y',
    { intro y, dsimp [P], },
    { refine ⟨λ y : Y, @classical.epsilon _ ⟨y⟩ (P y), _⟩,
      split,
      { funext,
        dsimp,
        have := @classical.epsilon_spec _ (P (f x)) (h (f x)),
        exact (this.2 x rfl).symm },
      { funext y,
        dsimp,
        have := @classical.epsilon_spec _ (P y) (h y),
        exact this.1 } },
    { push_neg at h, }
     },
  { rintro ⟨b, rfl, rfl⟩,
    refl }
end 

def funny_comp {W X Y Z : Type} (r₁ : W → X → Prop) (r₂ : X → Y → Prop) (r₃ : Y → Z → Prop) : W → Z → Prop := 
λ w z, ∃ x y, r₂ x y ∧ r₁ w x ∧ r₃ y z

lemma square_funny_comp {W X Y Z : Type} (r₁ : W → X → Prop) (r₂ : X → Y → Prop) (r₃ : Y → Z → Prop) :
  square r₁ → square r₂ → square r₃ → square (funny_comp r₁ r₂ r₃) :=
begin
  dunfold square funny_comp,
  rintros h₁ h₂ h₃ w₁ w₂ z₁ z₂ ⟨x₁, y₁, hxy₁⟩ ⟨x₂, y₂, hxy₂⟩ ⟨x₃, y₃, hxy₃⟩,
  use [x₁, y₃],

end

example {X Y Z : Type} (f : X → Y) (g : Y → Z) : 
  square (λ (a : X → X) (c : Z → Z), 
    ∃ b, f ∘ a = b ∘ f ∧ g ∘ b = c ∘ g ) :=
begin
  rintro a₁ a₂ c₁ c₂ ⟨b₁, hab₁, hbc₁⟩ ⟨b₂, hab₂, hbc₂⟩ ⟨b₃, hab₃,hbc₃⟩,
end

example {X Y Z : Type} (f : X → Y) (g : Y → Z) (a : X → X) (c : Z → Z)  : 
  g ∘ f ∘ a = c ∘ g ∘ f ↔ ∃ b, f ∘ a = b ∘ f ∧ g ∘ b = c ∘ g :=
begin
  split,
  { intro h,
    let P : Y → Y → Prop := (λ y y', g y' = c (g y) ∧ ∀ x, y = f x → f (a x) = y'),
    refine ⟨λ y : Y, @classical.epsilon _ ⟨y⟩ (P y), _⟩,
    split,
    funext,
    { dsimp,
      let y : Y := sorry,
      have := @classical.epsilon_spec _ (P (f x)) ⟨f (a x), _⟩,
      exact (this.2 x rfl), 
      simp [P, function.funext_iff, *] at *,
      rw h, simp,
      have hg : injective g := sorry,
      assume x' hx',
      apply hg,
      rw h, rw ← hx',
       } }


end


example {A A' : Type} {B : A → Type} {B' : A' → Type} (Ra : A → A' → Prop)
  (hRa : square Ra) 
  (Rb : Π (a₁ : A) (a₂ : A') (h : Ra a₁ a₂), 
    {R : B a₁ → B' a₂ → Prop // square R}) :
  square (λ (f : Π a, B a) (g : Π a, B' a), 
    ∀ a a' (h : Ra a a'), (Rb a a' h).1 (f a) (g a')) :=
begin
  intros f₁ f₂ g₁ g₂,
  dsimp,
  intros h₁ h₂ h₃ a a' h,
  exact (Rb a a' h).2 _ _ _ _  (h₁ a a' h) (h₂ a a' h) (h₃ a a' h)
end

end

import tactic

def F : Type → Type :=
λ X, (X → X × X) → X → X

def F2 : Type → Type → Type :=
λ X Y, (Y → X × X) → X → Y

def g₁ {X Y : Type} (f : X → Y) : F2 X X → F2 X Y := sorry

def g₂ {X Y : Type} (f : X → Y) : F2 Y Y → F2 X Y := sorry

def R {X Y : Type} (f : X → Y) : F2 X X → F2 Y Y → Prop :=
λ x y, g₁ f x = g₂ f y



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

inductive square_closure {A B : Type} (R : A → B → Prop) : A → B → Prop 
| of_rel {a b} : R a b → square_closure a b
| closure {a₁ a₂ b₁ b₂} : square_closure a₁ b₁ → square_closure a₁ b₂ → 
  square_closure a₂ b₁ → square_closure a₂ b₂ 

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

example {A₁ A₂ : Type} {B₁ : A₁ → Type} {B₂ : A₂ → Type} 
  (Ra : Type) (f₁ : A₁ → Ra) (f₂ : A₂ → Ra)
  (Rb : Π {a₁ : A₁} {a₂ : A₂} (h : f₁ a₁ = f₂ a₂), Type) 
  (g₁ : Π {a₁ : A₁} {a₂ : A₂} (h : f₁ a₁ = f₂ a₂), B₁ a₁ → Rb h)
  (g₂ : Π {a₁ : A₁} {a₂ : A₂} (h : f₁ a₁ = f₂ a₂), B₂ a₂ → Rb h) :
  Σ' (R : Type) (i₁ : (Π a₁ : A₁, B₁ a₁) → R) (i₂ : (Π a₂ : A₂, B₂ a₂) → R),
    ∀ (p₁ : (Π a₁ : A₁, B₁ a₁)) (p₂ : (Π a₂ : A₂, B₂ a₂)),
      (∀ a₁ a₂ (h : f₁ a₁ = f₂ a₂), g₁ h (p₁ a₁) = g₂ h (p₂ a₂)) ↔
    i₁ p₁ = i₂ p₂ :=
⟨Π (a₁ : A₁) (a₂ : A₂) (h : f₁ a₁ = f₂ a₂), Rb h,
  λ p₁ a₁ a₂ h, g₁ h (p₁ a₁),
  λ p₂ a₁ a₂ h, g₂ h (p₂ a₂),
  by simp [function.funext_iff]⟩
#print nat.rec
section funny_cat


end funny_cat

end

def preimage (F₁ F₂ G₁ G₂ : Type → Type) 
  (R : Π {A₁ A₂ : Type} (R : A₁ → A₂ → Type), G₁ A₁ → G₂ A₂ → Type)
  ( hom₁ : Π {A : Type}, F₁ A → G₁ A)
  ( hom₂ : Π {A₁ A₂ : Type}, (F₂ A₁ → G₂ A₂) ) : 
  Π {A₁ A₂ : Type} (Ra : A₁ → A₂ → Type), F₁ A₁ → F₂ A₂ → Type :=
λ A₁ A₂ Ra a₁ a₂, R Ra (@hom₁ A₁ a₁) _

def preimage (F₁ F₂ G₁ G₂ : Type → Type) 
  (R : Π {A₁ A₂ : Type}, (A₁ → A₂ → Type) → G₁ A₁ → G₂ A₂ → Type)
  (hom₁ : Π {A₁ A₂ : Type}, (A₁ → A₂) → (F₁ A₁ → G₁ A₂))
  (hom₂ : Π {A₁ A₂ : Type}, (A₁ → A₂) → (F₂ A₁ → G₂ A₂)) : 
  Π {A₁ A₂ : Type}, (A₁ → A₂ → Type) → F₁ A₁ → F₂ A₂ → Type :=
λ A₁ A₂ Ra a₁ a₂, R Ra (hom₁ id a₁) _

def natural (F : Type → Type) (G : Type → Type) 
  (mapF : Π {X Y}, (X → Y) → (F X → F Y))
  (mapG : Π {X Y}, (X → Y) → (G X → G Y))
  (n : Π X, F X → G X) :=
  ∀ (X Y) (f : X → Y), n Y ∘ mapF f = mapG f ∘ n X

example (F : Type → Type) (G : Type → Type) 
  (mapF : Π {X Y}, (X → Y) → (F X → F Y))
  (mapG : Π {X Y}, (X → Y) → (G X → G Y)) 
  (hom₁ : Π {A : Type}, F A → G A) :
  Π {A₁ A₂ : Type}, (A₁ → A₂) → (F A₁ → G A₂) :=
  λ A₁ A₂ f a, hom₁ (mapF f a)

def parametric (F : Type → Type) (G : Type → Type)
  (mapF : Π {X Y}, (X → Y → Prop) → (F X → F Y → Prop))
  (mapG : Π {X Y}, (X → Y → Prop) → (G X → G Y → Prop))
  (n : Π X, F X → G X) :=
∀ (X Y) (R : X → Y → Prop) (x : F X) (y : F Y),
  mapF R x y → mapG R (n X x) (n Y y)
  -- ∀ (X Y) (R : X → Y → Prop) 
  -- mapF R ≤ (n X, n Y) ⁻¹ mapG R

def cyril_hom (F G : Type → Type) :=
  Π {{X Y}}, (X → Y) → (F X → G Y)

def comp {F G H : Type → Type} : cyril_hom G H → cyril_hom F G → cyril_hom F H :=
λ f g X Y i x, begin
  dsimp [cyril_hom] at *,
  apply f,
  apply i,
  apply g,
  apply id,
  apply x,
end

def comp_assoc (W X Y Z : Type → Type) 
  (f : cyril_hom Y Z) (g : cyril_hom X Y) (h : cyril_hom W X) :
  comp f (comp g h) = comp (comp f g) h :=
begin
  funext,
  simp [comp],

end 
 
def identity (F : Type → Type) : cyril_hom F F :=
λ _ _ _, id

def chris_hom (F G : (Type → Type) → Type) : Type 1 :=
Π {A B : Type → Type}, (f : )

example chris_comp (F G : (Type → Type) → Type) 
  (f : Π ): 

example : Π (X : Type), (X → X) → (X → X) := sorry
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

inductive rel : X ⊕ Y → X ⊕ Y → Prop
| lr : ∀ {x y}, R x y → rel (inl x) (inr y)
| rl : ∀ {x y}, R x y → rel (inr y) (inl x)
| refll : ∀ x, rel (inl x) (inl x)
| refly : ∀ y, rel (inr y) (inr y)
| transl : ∀ {x₁ x₂ y}, R x₁ y → R x₂ y → rel (inl x₁) (inl x₂)
| transr : ∀ {x y₁ y₂}, R x y₁ → R x y₂ → rel (inr y₁) (inr y₂)

lemma rel_refl (a : X ⊕ Y) : rel R a a :=
by cases a; constructor

lemma rel_symm {a b : X ⊕ Y} : rel R a b → rel R b a :=
begin
  intro h,
  induction h,
  { apply rel.rl; assumption },
  { apply rel.lr; assumption },
  { exact rel_refl _ _ },
  { exact rel_refl _ _ },
  { apply rel.transl; assumption },
  { apply rel.transr; assumption }
end

lemma rel_trans 
  (hR : ∀ {x₁ x₂ y₁ y₂}, R x₁ y₁ → R x₂ y₁ → R x₂ y₂ → R x₁ y₂)
  {a b c : X ⊕ Y} : 
  rel R a b → rel R b c → rel R a c :=
begin
  intros hab hbc,
  induction hab with x₁ y₁ hxy₁ x₁ y₁ hxy₁ _ _ x₁ x₂ y₁ hxy₁ hxy₂
    x₁ y₁ y₂ hxy₁ hxy₂,
  { generalize hb : (inr y₁ : X ⊕ Y) = b,
    rw hb at hbc,
    induction hbc with _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hxy₂ hxy₃;
    injection hb with hb; subst hb; constructor; try {assumption},
    { exact hR hxy₁ hxy₂ hxy₃ } },
  { generalize hb : (inl x₁ : X ⊕ Y) = b,
    rw hb at hbc,
    induction hbc with _ _ _ _ _ _ _ _ _ _ _ hxy₂ hxy₃;
    injection hb with hb; subst hb; constructor; try {assumption},
    { exact hR hxy₃ hxy₂ hxy₁ } },
  { exact hbc },
  { exact hbc },
  { generalize hb : (inl x₂ : X ⊕ Y) = b,
    rw hb at hbc,
    induction hbc with _ _ hxy₃ _ _ _ _ _ _ x₃ y₂ hxy₃ hxy₄;
    injection hb with hb; subst hb; constructor; try {assumption},
    { exact hR hxy₁ hxy₂ hxy₃ },
    { exact hR hxy₄ hxy₃ hxy₂ } },
  { generalize hb : (inr y₂ : X ⊕ Y) = b,
    rw hb at hbc,
    induction hbc with _ _ _ _ _ hxy₃ _ _ _ _ _ _ _ _ hxy₃
      _ hxy₃ hxy₄;
    injection hb with hb; subst hb; constructor; try {assumption},
    { exact hR hxy₃ hxy₂ hxy₁ },
    { exact hR hxy₁ (hR hxy₃ hxy₂ hxy₁) hxy₄ } } 
end

def rel_setoid (hR : ∀ x₁ x₂ y₁ y₂, R x₁ y₁ → R x₂ y₁ → R x₂ y₂ → R x₁ y₂) :
  setoid (X ⊕ Y) :=
{ r := rel R,
  iseqv := ⟨rel_refl _, @rel_symm _ _ _, @rel_trans _ _ _ hR⟩ }

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
    { exact rel.lr},
    { generalize ha : (inl x : X ⊕ Y) = a,
      generalize hb : (inr y : X ⊕ Y) = b,
      intro h,
      induction h; simp * at * } },
  { rintros ⟨Z, f₁, f₂, h⟩,
    simp only [h], cc }
end

end

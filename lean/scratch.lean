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

section funny_cat

structure edge : Type 1 :=
( op_type : Type )
( type : Type )
( R : op_type → type → Prop )

namespace edge

def op (E : edge) : edge :=
{ op_type := E.type,
  type := E.op_type,
  R := λ x y, E.R y x }

structure hom (X Y : edge) : Type :=
( op_hom : Y.op_type → X.op_type )
( hom : X.type → Y.type )
( adj : ∀ (x : X.type) (y : Y.op_type), X.R (op_hom y) x ↔ Y.R y (hom x) )

def functional (E : edge) : Prop :=
∃ f : E.op_type → E.type, ∀ x y, E.R x y ↔ f x = y

example (E : edge) (hf : functional E) (F : edge) (h : hom E F) : 
  false  :=
begin
  cases E, cases hf, cases F, cases h,
  dsimp at *,
  simp [hf_h] at *,

end

def id (X : edge) : hom X X :=
{ op_hom := id,
  hom := id,
  adj := λ _ _, iff.rfl }

def comp {X Y Z : edge} (f : hom Y Z) (g : hom X Y) : hom X Z :=
{ op_hom := g.op_hom ∘ f.op_hom,
  hom := f.hom ∘ g.hom,
  adj := λ x y, by simp [f.adj, g.adj] }

def pullback (E : edge) : Type := { x : E.op_type × E.type // E.R x.1 x.2 }

def id_edge (X : Type) : edge :=
{ op_type := X,
  type := X,
  R := eq }

def of_fun {X Y : Type} (f : X → Y) : edge :=
{ op_type := X,
  type := Y,
  R := λ x y, f x = y }

def id_to_of_fun {X Y : Type} (f : X → Y) : hom (id_edge Y) (of_fun f) :=
{ op_hom := f,
  hom := _root_.id,
  adj := begin
    intros, refl,
  end }

example {X₁ X₂ Y₁ Y₂ : Type} (f₁ : X₁ → Y₁) (f₂ : X₂ → Y₂) (o : X₂ → X₁) 
  (h : Y₁ → Y₂) : hom ⟨X₁, Y₁, λ x y, f₁ x = y⟩ ⟨X₂, Y₂, λ x y, f₂ x = y⟩ :=
{ op_hom := o,
  hom := h,
  adj := begin
    dsimp,
    
  end }

def thing (X : Type) : Type :=
Π (f : Π x : X, {l : list X // x ∈ l}) (x : X), {l : list (list X) // (f x).1 ∈ l}

inductive list.rel_lift {A B : Type} (R : A → B → Prop) : list A → list B → Prop
| nil : list.rel_lift [] []
| cons : ∀ a b l₁ l₂, list.rel_lift l₁ l₂ → R a b → list.rel_lift (a :: l₁) (b::l₂)

def thing' (E : edge) : Type := 
Π (f : Π x : E.type, { l : list E.op_type // ∃ (y : E.op_type) (h : E.R y x), y ∈ l }) (x : E.op_type),
  {l : list (list E.type) // ∃ (y : E.type) (h : E.R x y) 
    (l' : list E.type) (h : list.rel_lift E.R (f y).1 l'), l' ∈ l  }

def thing'_map {X Y : edge} (f : hom X Y) (t : thing' X) : thing' Y :=
λ g y, begin
  dsimp only [thing', thing] at t,
  let g' : Π (x : X.type), { l : list X.op_type // ∃ (y : X.op_type) (h : X.R y x ), y ∈ l },
    from λ x, ⟨(g (f.hom x)).1.map f.op_hom, begin
      rcases (g (f.hom x)).2 with ⟨y, hy₁, hy₂⟩,
      existsi f.op_hom y,
      rw [f.adj],
      use hy₁,
      rw [list.mem_map],
      use y,
      simpa using hy₂,
    end⟩,
  let l := t g' (f.op_hom y),
  fsplit,
  exact l.1.map (list.map f.hom),
  rcases l.2 with ⟨x, hxy, l', hl', hll⟩,
  use f.hom x,
  rw ← f.adj,
  use hxy,
  use l'.map f.hom,
  split,
  intros,
  clear_except hl' ,
  dsimp [g'] at hl',
  simp,
  generalize hk : (↑(g (f.hom x)) : list _) = k,
  rw hk at hl',
  clear_except hl',
  generalize hm : list.map f.op_hom k = m,
  rw hm at hl', 
  induction hl' generalizing k,
  { simp * at *, constructor },
  { cases k,
    simp * at *,
    simp at hm,
    cases hm with hm1 hm2,
    subst hm1,
    constructor,
    apply hl'_ih,
    assumption,
    rwa ← f.adj },
  simp,
  use l',
  simp * at *
end

@[simp] lemma list.map_id {A : Type} : list.map (_root_.id : A → A) = _root_.id := 
by funext; simp

lemma list.map_comp {A B C : Type} (f : A → B) (g : B → C) : 
  list.map (g ∘ f) = list.map g ∘ list.map f := 
by funext; simp

lemma thing'_map_id (X : edge) : thing'_map (edge.id X) = _root_.id :=
begin
  cases X, funext, simp [thing'_map],
  refine subtype.ext _,
  dsimp [id] at *,
  rw [list.map_id, list.map_id],
  simp,
  congr,
  simp,
  simp,
  simp,
  simp,
  simp,
end

lemma thing'_map_comp  (X Y Z : edge) (f : hom X Y) (g : hom Y Z) : 
  thing'_map (comp g f) =  thing'_map g ∘ thing'_map f :=
begin
  cases X, cases Y, cases Z, cases f, cases g, funext, simp [thing'_map, comp],
  congr,
  simp,
  simp,
  simp,
  simp,
  simp,
end

def id2 (E : edge) : Type := E.type

def id2_map {E₁ E₂ : edge} (f : hom E₁ E₂) : id2 E₁ → id2 E₂ := f.hom

lemma id2_map_id (E : edge) : id2_map (id E) = _root_.id := rfl

lemma id2_map_comp (E₁ E₂ E₃ : edge) (f : hom E₁ E₂) (g : hom E₂ E₃) : 
  id2_map (comp g f) = id2_map g ∘ id2_map f := rfl

def set2 (E : edge) : Type := E.op_type → Prop

def set2_map {E₁ E₂ : edge} (f : hom E₁ E₂) : set2 E₁ → set2 E₂ := (∘ f.op_hom)

lemma set2_map_id (E : edge) : set2_map (id E) = _root_.id := rfl

lemma set2_map_comp (E₁ E₂ E₃ : edge) (f : hom E₁ E₂) (g : hom E₂ E₃) : 
  set2_map (comp g f) = set2_map g ∘ set2_map f := rfl

structure group2 (E : edge) : Type :=
( one : E.type )
( inv : E.op_type → E.type )
( mul : E.op_type → E.op_type → E.type )
( one_mul : ∀ (x : E.op_type) (one' : E.op_type) (h1 : E.R one' one), mul one' x = one  )
(inv_mul : ∀ (x : E.op_type), ∀ (inv_y : E.op_type) (hi : E.R inv_y (inv x)), mul inv_y x = one )
( mul_assoc : ∀ (x y z : E.op_type),
    ∀ (mul_y_z : E.op_type) (mul_x_y : E.op_type) (hyz : E.R mul_y_z (mul y z))
      (hxy : E.R mul_x_y (mul x y)),
    mul x mul_y_z = mul mul_x_y z )

def group2_map {X Y : edge} (f : hom X Y) (G : group2 X) : group2 Y :=
{ one := f.hom G.one,
  inv := λ x, f.hom (G.inv (f.op_hom x)),
  mul := λ x y, f.hom (G.mul (f.op_hom x) (f.op_hom y)),
  one_mul := λ x one' h1,
    by rw G.one_mul (f.op_hom x) (f.op_hom one') ((f.adj _ _).2 h1),
  inv_mul := λ x y hxy, 
    by rw (G.inv_mul (f.op_hom x) (f.op_hom y)) ((f.adj _ _).2 hxy),
  mul_assoc := λ x y z mul_y_z mul_x_y h1 h2, begin 
    rw G.mul_assoc,
    apply (f.adj _ _).2,
    assumption,
    apply (f.adj _ _).2,
    assumption
  end, }

lemma group2_map_id {X : edge} : group2_map (id X) = _root_.id :=
begin
  funext,
  cases G,
  refl,
end

lemma group2_map_comp {X Y Z : edge} (f : hom X Y) (g : hom Y Z ) : 
   group2_map (comp g f) = group2_map g ∘ group2_map f :=
begin
  funext,
  cases G,
  refl,
end


end edge

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
  (hom₁ : Π {A₁ A₂ : Type}, (A₁ → A₂) → (F₁ A₁ → G₁ A₂) )
  (hom₂ : Π {A₁ A₂ : Type}, (A₁ → A₂) → (F₂ A₁ → G₂ A₂) ) : 
  Π {A₁ A₂ : Type}, (A₁ → A₂ → Type) → F₁ A₁ → F₂ A₂ → Type :=
λ A₁ A₂ Ra a₁ a₂, R Ra (hom₁ id a₁) _
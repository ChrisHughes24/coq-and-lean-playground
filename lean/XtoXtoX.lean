import tactic

class myclass (X : Type) :=
(op : (X → X) → X)

variables (X Y Z : Type) [myclass X] [myclass Y] [myclass Z]

namespace myclass

structure hom :=
(f : X → Y)
(map' : ∀ (a : X → X) (b : Y → Y), (∀ x, f (a x) = b (f x)) → f (op a) = op b)

structure edge :=
(R : X → Y → Prop)
(h : ∀ (a : X → X) (b : Y → Y), (∀ x y, R x y → R (a x) (b y)) → R (op a) (op b))

def diag : edge X X :=
{ R := eq,
  h := begin
    intros a b h,
    congr,
    ext,
    apply h,
    refl,
  end }

example (e : edge X Y) : myclass (Σ' x y, e.R x y) :=
⟨λ a, begin
  cases e, dsimp at *,
end⟩

structure hom2 :=
(f : X → Y)
(f2 : (X → X) → (Y → Y))
(hf2 : ∀ (a : X → X) (b : Y → Y), (∀ x, f (a x) = b (f x)) ↔ f2 a = b)
(map : ∀ (a : X → X), f (op a) = op (f2 a))

def preimage {Z : Type} [myclass Z] ()

example {X Y : Type} (f : X → Y)
  (f2 : (X → X) → (Y → Y))
  (hf2 : ∀ (a : X → X) (b : Y → Y), (∀ x, f (a x) = b (f x)) ↔ f2 a = b) :
  function.bijective f ∨ (∀ x y : Y, x = y) :=
begin
  rw [or_iff_not_imp_right],
  intro h,
  push_neg at h,
  rcases h with ⟨y₁, y₂, hy⟩,
  classical,
  split,
  intros x₁ x₂ h,
  have := hf2 id (equiv.swap y₁ y₂),
  dsimp at this, 
end


lemma lemma1 {X Y : Type} (f : X → Y) 
  (hf : function.has_right_inverse f) :
  ∃ f2 : (X → X) → (Y → Y),
  (∀ (a : X → X) (b : Y → Y), (∀ x, f (a x) = b (f x)) ↔ f2 a = b) :=
begin
  cases hf with g hg,
  refine ⟨λ a, f ∘ a ∘ g, _⟩,
  intros a b,
  simp only [function.funext_iff, function.comp_app],
  split,
  { assume h y,
    rw [← hg y, h, hg y, hg y] },
  { assume h x,
    rw [← h],
    delta function.right_inverse function.left_inverse at hg,
    

     }
end

-- example : false := begin 
--    have := h (@empty.elim unit) (λ _, id) _ (),
--    cases this,
--    cases this_w,
--    intros,simp,
-- end

def hom2_to_edge (f : hom2 X Y) : edge X Y :=
{ R := λ x y, f.f x = y,
  h := λ a b h, begin
    rw [f.map],

    
  end }

def comp2 (f : hom2 X Y) (g : hom2 Y Z) : hom2 X Z :=
{ f := λ x, g.f (f.f x),
  f2 := λ a, g.f2 (f.f2 a),
  hf2 := λ a c, begin
    split,
    { have hg2 := g.hf2,
      have hf2 := f.hf2,
      intros h,
      rw [(hg2 _ _).1],
      clear hg2,
      intro y,
      have := f.hf2 a (λ _, f.f2 a y),
      simp only [function.funext_iff] at this,
      rw ← this.2,
      rw h,
      
       },
    { intros h x,
      have := (f.hf2 a _).2 rfl,
      rw [this, (g.hf2 _ _).2],
      rw h }
  end,
  map := λ a, by rw [f.map, g.map] }

instance : has_coe_to_fun (hom X Y) (λ _, X → Y) :=
{ coe := hom.f }

def id : hom X X :=
{ f := id,
  map' := λ a b h, have h : a = b, from funext h, by rw h; refl }

variables {X Y Z}

lemma hom.map (f : hom X Y) : 
  ∀ (a : X → X) (b : Y → Y), (∀ x, f (a x) = b (f x)) → f (op a) = op b := f.map'

def comp (f : hom X Y) (g : hom Y Z) : hom X Z :=
{ f := λ x, g (f x),
  map' := λ a c h, begin
    cases f with f hf, cases g with g hg,
    unfold_coes at *,
    dsimp at *,
    
  end }

end myclass
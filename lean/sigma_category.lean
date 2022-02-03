import tactic
import category_theory.functor
import data.W.basic
import category_theory.closed.types
import algebra.category.CommRing.basic
import algebra.category.Module.basic

universes u v w x

open category_theory

variables {𝒞 : Type u} [category.{v} 𝒞]

@[protect_proj] class gen_structure (F : 𝒞 → Type w) :=
( hom : Π {A B : 𝒞} (f : A ⟶ B) (a : F A) (b : F B), Type x )
( id : Π {A : 𝒞} (a : F A), hom (𝟙 A) a a )
( comp : Π {A B C : 𝒞} {a : F A} {b : F B} {c : F C}
  {f : A ⟶ B} {g : B ⟶ C} (f' : hom f a b) (g' : hom g b c), 
  hom (f ≫ g) a c )
( id_comp : Π {A B : 𝒞} {f : A ⟶ B}
    {a : F A} {b : F B}
    (f' : hom f a b), comp (id a) f' == f' )
( comp_id : Π {A B : 𝒞} {f : A ⟶ B}
    {a : F A} {b : F B}
    (f' : hom f a b), comp f' (id b) == f' )
( assoc : Π {A B C D : 𝒞} {f : A ⟶ B} {g : B ⟶ C} {h : C ⟶ D}
    {a : F A} {b : F B} {c : F C} {d : F D}
    (f' : hom f a b) (g' : hom g b c) (h' : hom h c d),
    comp (comp f' g') h' == comp f' (comp g' h') )

-- @[protect_proj] class GS (F : 𝒞 → Type w) :=
-- ( hom : Π {A B : 𝒞} (f : A ⟶ B) (a : F A) (b : F B), Type x )
-- ( id : Π {A : 𝒞} (a b : F A) (h : a = b) (f : A ⟶ A) (hf : f = 𝟙 A), hom f a b )

namespace gen_structure

variables (F : 𝒞 → Type w) [gen_structure F]

instance : category_struct (sigma F) :=
{ hom := λ A B, Σ (f : A.1 ⟶ B.1), gen_structure.hom f A.2 B.2,
  id := λ A, ⟨𝟙 A.1, gen_structure.id A.2⟩,
  comp := λ A B C f g, ⟨f.1 ≫ g.1, gen_structure.comp f.2 g.2⟩ }

instance : category (sigma F) :=
{ id_comp' := λ A B f, sigma.ext (category.id_comp _) (gen_structure.id_comp _),
  comp_id' := λ A B f, sigma.ext (category.comp_id _) (gen_structure.comp_id _),
  assoc' := λ A B C D f g h, sigma.ext (category.assoc _ _ _) (gen_structure.assoc _ _ _) }

instance (X : 𝒞) : category_struct (F X) :=
{ hom := λ A B, gen_structure.hom (𝟙 X) A B,
  id := λ A, gen_structure.id A,
  comp := λ A B C f g, cast (by simp) (gen_structure.comp f g) }

lemma assoc2 {A B C D : 𝒞} {f : A ⟶ B} {g : B ⟶ C} {h : C ⟶ D}
  {a : F A} {b : F B} {c : F C} {d : F D}
  (f' : gen_structure.hom f a b) (g' : gen_structure.hom g b c) (h' : gen_structure.hom h c d) 
  (i : A ⟶ C) (hi : gen_structure.hom (f ≫ g) a c = gen_structure.hom i a c) (hi2 : i = f ≫ g)
  (j : B ⟶ D) (hj : gen_structure.hom (g ≫ h) b d = gen_structure.hom j b d) (hj2 : j = g ≫ h) :
  gen_structure.comp (cast hi (gen_structure.comp f' g')) h' ==
    gen_structure.comp f' (cast hj (gen_structure.comp g' h')) :=
begin
  substs i j,
  simp,
  exact gen_structure.assoc _ _ _,
end

instance (X : 𝒞) : category (F X) :=
{ id_comp' := λ A B f, cast_eq_iff_heq.2 (gen_structure.id_comp f),
  comp_id' := λ A B f, cast_eq_iff_heq.2 (gen_structure.comp_id f),
  assoc' := λ A B C D f g h,
    begin
      dsimp [category_struct.comp],
      simp,
      apply eq_of_heq,
      exact assoc2 F f g h _ _ (by simp) _ _ (by simp)
    end }

def forget : sigma F ⥤ 𝒞 :=
{ obj := sigma.fst,
  map := λ _ _, sigma.fst }

def thing (X : 𝒞) : F X ⥤ sigma F :=
{ obj := λ A, ⟨X, A⟩,
  map := λ A B f, ⟨𝟙 X, f⟩,
  map_id' := λ A, rfl,
  map_comp' := λ A B C f g, sigma.ext (category.comp_id _).symm (cast_heq _ _) }

instance inst1 (F : 𝒞 ⥤ Type) : gen_structure F.obj :=
{ hom := λ A B f a b, plift (F.map f a = b),
  id := λ A a, ⟨by simp⟩,
  comp := λ A B C a b c f g h₁ h₂, ⟨by simp [F.map_comp, h₁.down, h₂.down]⟩,
  assoc := λ _ _ _ _ _ _ _ _ _ _ _ h₁ h₂ h₃, 
    begin refine heq_of_cast_eq _ _;
      simp [h₁.down, h₂.down, h₃.down] end,
  id_comp := λ _ _ _ _ _ h, 
    begin refine heq_of_cast_eq _ _; simp [h.down] end,
  comp_id := λ _ _ _ _ _ h, 
    begin refine heq_of_cast_eq _ _; simp [h.down] end }

-- instance inst2 (F : 𝒞 ⥤ Typeᵒᵖ) : gen_structure (λ x, (F.obj x).unop) :=
-- { hom := λ A B f a b, plift ((F.map f).unop b = a),
--   id := λ A a, ⟨by simp⟩,
--   comp := λ A B C a b c f g h₁ h₂, ⟨by simp [F.map_comp, h₁.down, h₂.down]⟩,
--   assoc := λ _ _ _ _ _ _ _ _ _ _ _ h₁ h₂ h₃, 
--     begin refine heq_of_cast_eq _ _;
--       simp [h₁.down, h₂.down, h₃.down] end,
--   id_comp := λ _ _ _ _ _ h, 
--     begin refine heq_of_cast_eq _ _; simp [h.down] end,
--   comp_id := λ _ _ _ _ _ h, 
--     begin refine heq_of_cast_eq _ _; simp [h.down] end } 

example : gen_structure (λ R : Ring, Module R) :=
{ hom := λ R S f M₁ M₂, M₁ →ₛₗ[f] M₂,
  id := λ R M, linear_map.id,
  comp := λ R S T M₁ M₂ M₃ f g f' g', 
    @linear_map.comp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (id ⟨rfl⟩) g' f',
  id_comp := λ R S f M₁ M₂ f', begin
      cases f', cases f, refl
    end,
  comp_id := λ R S f M₁ M₂ f', begin
      cases f', cases f, refl,
    end,
  assoc := λ R S T U f g h M₁ M₂ M₃ M₄ f' g' h', 
    begin
      cases f, cases g, cases h, cases f', cases g', cases h',
      refl
    end }

example (F : 𝒞 ⥤ Type) (G : 𝒞 → Type) [gen_structure G] : gen_structure (λ A : 𝒞, F.obj A → G A) :=
{ hom := λ X Y f x y, Π a : F.obj X, gen_structure.hom f (x a) (y (F.map f a)),
  id := λ X x a, cast (by simp) (gen_structure.id (x a)),
  comp := λ X Y Z x y z f g f' g' a, 
    cast (by simp) (gen_structure.comp  (f' a) (g' (F.map f a))),
  id_comp := λ X Y f x y f', begin
      apply function.hfunext,
      { refl },
      { intros a a' h,
        rw [heq_iff_eq] at h,
        subst a',
        refine cast_eq_iff_heq.1 _,
        simp,
        simp, admit }    
    end,
  comp_id := sorry,
  assoc := λ W X Y Z f g h w x y z f' g' h', 
    begin
      apply function.hfunext,
    { refl },
    { intros a a' h,
      rw [heq_iff_eq] at h,
      subst a',
      dsimp,
      admit }
      
    end }

example (F : 𝒞 ⥤ Type) (G : (Σ A : 𝒞, F.obj A) → Type) [gen_structure G] : 
  gen_structure (λ A : 𝒞, Π a : F.obj A, G ⟨A, a⟩) :=
{ hom := λ X Y f x y, Π (a : F.obj X),
    @gen_structure.hom _ _ G _ ⟨X, a⟩ ⟨Y, F.map f a⟩ ⟨f, ⟨rfl⟩⟩ (x a) (y (F.map f a)),
  id := λ X x a, by convert @gen_structure.id _ _ G _ ⟨X, a⟩ (x a); simp,
  
  }

-- Maybe think about W.

end gen_structure
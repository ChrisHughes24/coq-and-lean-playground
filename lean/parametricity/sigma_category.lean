import tactic
import category_theory.functor
import data.W.basic
import category_theory.closed.types
import algebra.category.CommRing.basic
import algebra.category.Module.basic

universes u v w x

open category_theory
--W

variables {𝒞 : Type u} [category.{v} 𝒞]

@[protect_proj] class struc (F : 𝒞 → Type w) :=
( hom : Π {A B : 𝒞} (f : A ⟶ B) (a : F A) (b : F B), Type x )
( id : Π {A : 𝒞} (a : F A), hom (𝟙 A) a a )
( comp : Π {A B C : 𝒞} {a : F A} {b : F B} {c : F C}
    {f : A ⟶ B} {g : B ⟶ C} (f' : hom f a b) (g' : hom g b c) 
    {h : A ⟶ C} (H : f ≫ g = h), hom h a c )
( id_comp : Π {A B : 𝒞} {f : A ⟶ B} {a : F A} {b : F B}
    (f' : hom f a b), comp (id a) f' (category.id_comp f) = f' )
( comp_id : Π {A B : 𝒞} {f : A ⟶ B} {a : F A} {b : F B}
    (f' : hom f a b), comp f' (id b) (category.comp_id f) = f' )
( assoc : Π {A B C D : 𝒞} {f : A ⟶ B} {g : B ⟶ C} {h : C ⟶ D}
    {a : F A} {b : F B} {c : F C} {d : F D}
    (f' : hom f a b) (g' : hom g b c) (h' : hom h c d),
    comp (comp f' g' rfl) h' rfl = comp f' (comp g' h' rfl) 
      (category.assoc _ _ _).symm )

-- @[protect_proj] class GS (F : 𝒞 → Type w) :=
-- ( hom : Π {A B : 𝒞} (f : A ⟶ B) (a : F A) (b : F B), Type x )
-- ( id : Π {A : 𝒞} (a b : F A) (h : a = b) (f : A ⟶ A) (hf : f = 𝟙 A), hom f a b )

attribute [simp] struc.id_comp struc.comp_id

namespace struc

variables (F : 𝒞 → Type w) [struc F]

lemma assoc_left {A B C D : 𝒞} {f : A ⟶ B} {g : B ⟶ C} {h : C ⟶ D}
    {a : F A} {b : F B} {c : F C} {d : F D}
    (f' : struc.hom f a b) (g' : struc.hom g b c) (h' : struc.hom h c d)
    (i : A ⟶ C) (k : A ⟶ D)
    (hi : f ≫ g = i) (hk : i ≫ h = k) :
    struc.comp (struc.comp f' g' hi) h' hk = struc.comp f'
      (struc.comp g' h' rfl) (by rw [← hk, ← hi, category.assoc]) :=
begin
  substs i k,
  rw struc.assoc,
end

lemma comp_eq_cast {A B C : 𝒞} {f : A ⟶ B} {g : B ⟶ C} 
  {a : F A} {b : F B} {c : F C} (f' : struc.hom f a b) (g' : struc.hom g b c)
  (i : A ⟶ C) (hi : f ≫ g = i)
  (j : A ⟶ C) (hj : f ≫ g = j) :
  struc.comp f' g' hi = cast (by substs i j) (struc.comp f' g' hj) :=
begin
  substs i j, refl
end

lemma assoc_left' {A B C D : 𝒞} {f : A ⟶ B} {g : B ⟶ C} {h : C ⟶ D}
    {a : F A} {b : F B} {c : F C} {d : F D}
    (f' : struc.hom f a b) (g' : struc.hom g b c) (h' : struc.hom h c d)
    (i : A ⟶ C) (k : A ⟶ D)
    (hi : f ≫ g = i) (hk : i ≫ h = k) :
    struc.comp (struc.comp f' g' hi) h' hk = cast (by rw [← hk, ← hi, category.assoc]) 
      (struc.comp f' (struc.comp g' h' rfl) rfl)  :=
begin
  rw struc.assoc_left,
  substs i k,
  rw [comp_eq_cast]
end

lemma id_comp' {A B : 𝒞} {f : A ⟶ B} (g : A ⟶ B) {a : F A} {b : F B}
  (h : 𝟙 A ≫ f = g) (f' : struc.hom f a b) : 
  struc.comp (struc.id a) f' h = cast (by rw [← h, category.id_comp]) f' :=
begin
  rw [category.id_comp] at h,
  subst h,
  simp
end

lemma comp_id' {A B : 𝒞} {f : A ⟶ B} (g : A ⟶ B) {a : F A} {b : F B}
  (h : f ≫ 𝟙 B = g) (f' : struc.hom f a b) : 
  struc.comp f' (struc.id b) h = cast (by rw [← h, category.comp_id]) f' :=
begin
  rw [category.comp_id] at h,
  subst h,
  simp
end 

instance  : category_struct (sigma F) :=
{ hom := λ A B, Σ (f : A.1 ⟶ B.1), struc.hom f A.2 B.2,
  id := λ A, ⟨𝟙 A.1, struc.id A.2⟩,
  comp := λ A B C f g, ⟨f.1 ≫ g.1, struc.comp f.2 g.2 rfl⟩ }

@[simp] lemma comp_fst {A B C : sigma F} (f : A ⟶ B) (g : B ⟶ C) :
  (f ≫ g).fst = f.1 ≫ g.1 := rfl

@[simp] lemma comp_snd {A B C : sigma F} (f : A ⟶ B) (g : B ⟶ C) :
  (f ≫ g).snd = struc.comp f.2 g.2 rfl := rfl

@[simp] lemma id_fst {A : sigma F} : sigma.fst (𝟙 A) = 𝟙 A.1 := rfl

@[simp] lemma id_snd {A : sigma F} : sigma.snd (𝟙 A) = struc.id A.2 := rfl

instance sigma.category : category (sigma F) :=
{ id_comp' := λ A B f, sigma.ext (category.id_comp _) $
    by simp [struc.id_comp'],
  comp_id' := λ A B f, sigma.ext (category.comp_id _) $
    by simp [struc.comp_id'],
  assoc' := λ A B C D f g h, sigma.ext (category.assoc _ _ _) $
    by simp [assoc_left'] }

instance (X : 𝒞) : category_struct (F X) :=
{ hom := λ A B, struc.hom (𝟙 X) A B,
  id := λ A, struc.id A,
  comp := λ A B C f g, (struc.comp f g (category.id_comp _)) }


instance (X : 𝒞) : category (F X) :=
{ id_comp' := λ A B f, struc.id_comp _,
  comp_id' := λ A B f, struc.comp_id _,
  assoc' := λ A B C D f g h,
    show (f ≫ g) ≫ h = f ≫ g ≫ h,
      begin
        dsimp [category_struct.comp],
        rw [struc.assoc_left],
        congr' 2; simp
      end }

def forget : sigma F ⥤ 𝒞 :=
{ obj := sigma.fst,
  map := λ _ _, sigma.fst }

def thing (X : 𝒞) : F X ⥤ sigma F :=
{ obj := λ A, ⟨X, A⟩,
  map := λ A B f, ⟨𝟙 X, f⟩,
  map_id' := λ A, rfl,
  map_comp' := λ A B C f g, sigma.ext 
    (by simp) begin simp only [comp_snd],
       rw [struc.comp_eq_cast F f g (𝟙 X ≫ 𝟙 X) rfl (𝟙 X)
         (category.comp_id _)],
       symmetry,
       rw [← cast_eq_iff_heq],
       simp, refl,
       simp,
     end }

instance inst1 (F : 𝒞 ⥤ Type) : struc F.obj :=
{ hom := λ A B f a b, plift (F.map f a = b),
  id := λ A a, ⟨by simp⟩,
  comp := λ A B C a b c f g h₁ h₂ _ h, ⟨by simp [← h, F.map_comp, h₁.down, h₂.down]⟩,
  assoc := λ _ _ _ _ _ _ _ _ _ _ _ h₁ h₂ h₃, 
    begin simp [h₁.down, h₂.down, h₃.down] end,
  id_comp := λ _ _ _ _ _ h, 
    begin simp [h.down] end,
  comp_id := λ _ _ _ _ _ h, 
    begin simp [h.down] end }

-- instance inst2 (F : 𝒞 ⥤ Typeᵒᵖ) : struc (λ x, (F.obj x).unop) :=
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

example : struc (λ R : Ring, Module R) :=
{ hom := λ R S f M₁ M₂, M₁ →ₛₗ[f] M₂,
  id := λ R M, linear_map.id,
  comp := λ R S T M₁ M₂ M₃ f g f' g' _ h, 
    @linear_map.comp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ⟨h⟩ g' f',
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

example (F : 𝒞 ⥤ Type) (G : 𝒞 → Type) [struc G] : struc (λ A : 𝒞, F.obj A → G A) :=
{ hom := λ X Y f x y, Π (a : F.obj X) (b : F.obj Y), struc.hom f (x a) (y (F.map f a)),
  id := λ X x a, cast (by simp) (struc.id (x a)),
  comp := λ X Y Z x y z f g f' g' _ h a, struc.comp (f' a) 
    (g' (F.map f a)) _,
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

def pi.struc (F : 𝒞 ⥤ Type) (G : (Σ A : 𝒞, F.obj A) → Type) [struc G] : 
  struc (λ A : 𝒞, Π a : F.obj A, G ⟨A, a⟩) :=
{ hom := λ X Y f x y, Π (a : F.obj X),
    @struc.hom _ _ G _ ⟨X, a⟩ ⟨Y, F.map f a⟩ ⟨f, ⟨rfl⟩⟩ (x a) (y (F.map f a)),
  id := λ X x a, by convert @struc.id _ _ G _ ⟨X, a⟩ (x a); simp,
  comp := sorry,
  id_comp := sorry,
  comp_id := sorry,
  assoc := sorry }

-- Maybe think about W.

end struc
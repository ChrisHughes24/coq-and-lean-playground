import tactic
import category_theory.functor
import data.W.basic
import category_theory.closed.types
import algebra.category.CommRing.basic
import algebra.category.Module.basic

universes w x u v 

open category_theory

variables (𝒞 : Type u) [category.{v} 𝒞]

@[protect_proj] structure struc : Type (max u v (w+1) (x+1)) :=
( F : 𝒞 → Type w )
( hom : Π (A B : sigma F) (f : A.1 ⟶ B.1), Type x )
( id : Π (A : sigma F), Σ f : A.1 ⟶ A.1, hom A A f )
( id_fst' : Π (A : sigma F), (id A).fst = 𝟙 A.1 )
( comp : Π {A B C : sigma F}
    (f : Σ f : A.1 ⟶ B.1, hom A B f)
    (g : Σ g : B.1 ⟶ C.1, hom B C g),
    Σ h : A.1 ⟶ C.1, hom A C h )
( comp_fst' : Π {A B C : sigma F}
    (f : Σ f : A.1 ⟶ B.1, hom A B f)
    (g : Σ g : B.1 ⟶ C.1, hom B C g),
    (comp f g).fst = f.1 ≫ g.1)
( id_comp' : Π {A B : sigma F} (f : Σ f : A.1 ⟶ B.1, hom A B f), 
    comp (id A) f = f )
( comp_id' : Π {A B : sigma F} (f : Σ f : A.1 ⟶ B.1, hom A B f), 
    comp f (id B) = f )
( assoc' : Π {A B C D : sigma F} 
    (f : Σ f : A.1 ⟶ B.1, hom A B f)
    (g : Σ g : B.1 ⟶ C.1, hom B C g)
    (h : Σ h : C.1 ⟶ D.1, hom C D h), 
    comp (comp f g) h = comp f (comp g h) )

namespace struc

instance : has_coe_to_fun (struc 𝒞) (λ _, 𝒞 → Type w) :=
{ coe := struc.F }

variables {𝒞} {F : struc 𝒞}

@[simp] lemma id_comp {A B : sigma F} (f : Σ (f : A.fst ⟶ B.fst), F.hom A B f) : 
  F.comp (F.id A) f = f := F.id_comp' _

@[simp] lemma comp_id {A B : sigma F} (f : Σ (f : A.fst ⟶ B.fst), F.hom A B f) : 
  F.comp f (F.id B) = f := F.comp_id' _

@[simp] lemma assoc {A B C D : sigma F}
  (f : Σ f : A.1 ⟶ B.1, F.hom A B f)
  (g : Σ g : B.1 ⟶ C.1, F.hom B C g)
  (h : Σ h : C.1 ⟶ D.1, F.hom C D h): 
  F.comp (F.comp f g) h = F.comp f (F.comp g h) :=
F.assoc' _ _ _

@[simp] lemma id_fst₁ (A : sigma F) : (F.id A).fst = 𝟙 A.1 := F.id_fst' _

@[simp] lemma comp_fst₁ {A B C : sigma F}
  (f : Σ f : A.1 ⟶ B.1, F.hom A B f)
  (g : Σ g : B.1 ⟶ C.1, F.hom B C g) :
  (F.comp f g).fst = f.1 ≫ g.1 := F.comp_fst' _ _

instance : category_struct (sigma F) :=
{ hom := λ A B, Σ (f : A.1 ⟶ B.1), F.hom A B f,
  id := F.id,
  comp := F.comp }

variable {F}

def sigma_category : category (sigma F) :=
{ id_comp' := F.id_comp',
  comp_id' := F.comp_id',
  assoc' := F.assoc' }

@[simp] lemma comp_fst {A B C : sigma F} (f : A ⟶ B) (g : B ⟶ C) :
  (f ≫ g).fst = f.1 ≫ g.1 := struc.comp_fst₁ f g

@[simp] lemma id_fst {A : sigma F} : sigma.fst (𝟙 A) = 𝟙 A.1 := struc.id_fst₁ _

instance (X : 𝒞) : category_struct (F X) :=
{ hom := λ A B, F.hom ⟨X, A⟩ ⟨X, B⟩ (𝟙 X),
  id := λ A, (F.id ⟨X, A⟩).snd,
  comp := λ A B C f g, begin
    have := (F.comp ⟨(F.id ⟨X, B⟩).fst, f⟩ _).snd,
  end }

lemma id_def {X : 𝒞} (x : F X) : 𝟙 x = F.id x := rfl 

lemma comp_def (X : 𝒞) (A B C : F X) (f : A ⟶ B) (g : B ⟶ C) :
  f ≫ g = F.hom_iso (𝟙 X ≫ 𝟙 X) A C (𝟙 X) A C (iso.refl X) (iso.refl X) 
    (by simp) (by simp) (by simp) (F.comp f g) := rfl

instance (X : 𝒞) : category (F X) :=
{ id_comp' := λ A B f, begin 
      simp [id_def, comp_def],
      rw [← equiv.trans_apply, F.hom_iso_trans],
      simp
    end,
  comp_id' := λ A B f, begin 
      simp [id_def, comp_def],
      rw [← equiv.trans_apply, F.hom_iso_trans],
      simp
    end,
  assoc' := λ A B C D f g h,
      begin
        simp only [comp_def, ← F.hom_iso_comp],
        erw F.hom_iso_comp,
      end }

def forget : sigma₂ F ⥤ 𝒞 :=
{ obj := sigma.fst,
  map := λ _ _, sigma.fst }

def thing (X : 𝒞) : F X ⥤ sigma₂ F :=
{ obj := λ A, ⟨X, A⟩,
  map := λ A B f, ⟨𝟙 X, f⟩,
  map_id' := λ A, rfl,
  map_comp' := λ A B C f g, sigma.ext 
    (by simp) begin 
      simp only [comp_snd],
      rw [struc.comp_eq_cast F f g (𝟙 X ≫ 𝟙 X) rfl (𝟙 X)
        (category.comp_id _)],
      symmetry,
      rw [← cast_eq_iff_heq],
      simp, refl,
      simp,
    end }

open opposite

protected def op (F : struc 𝒞) : struc 𝒞ᵒᵖ :=
{ F := λ A, F.F (unop A),
  hom := λ A B f a b, F.hom f.unop b a,
  id := λ A a, F.id a,
  comp := λ A B C a b c f g f' g' h hH, 
    F.comp g' f' (by simp [← hH]),
  id_comp := λ A B f a b f', F.comp_id _,
  comp_id := λ A B f a b f', F.id_comp _,
  assoc := λ A B C D f g h a b c d f' g' h', 
    by rw F.assoc_left; refl }

def unop (F : struc 𝒞ᵒᵖ) : struc 𝒞 :=
{ F := λ A, F.F (op A),
  hom := λ A B f a b, F.hom f.op b a,
  id := λ A a, F.id a,
  comp := λ A B C a b c f g f' g' h hH, 
     F.comp g' f' (by simp [← hH]),
  id_comp := λ A B f a b f', F.comp_id _,
  comp_id := λ A B f a b f', F.id_comp _,
  assoc := λ A B C D f g h a b c d f' g' h', 
    by rw F.assoc_left; refl }

def of_functor (F : 𝒞 ⥤ Type w) : struc 𝒞 :=
{ F := F.obj,
  hom := λ A B f a b, plift (F.map f a = b),
  id := λ A a, ⟨by simp⟩,
  comp := λ A B C a b c f g h₁ h₂ _ h, ⟨by simp [← h, F.map_comp, h₁.down, h₂.down]⟩,
  assoc := λ _ _ _ _ _ _ _ _ _ _ _ h₁ h₂ h₃, 
    begin simp [h₁.down, h₂.down, h₃.down] end,
  id_comp := λ _ _ _ _ _ h, 
    begin simp [h.down] end,
  comp_id := λ _ _ _ _ _ h, 
    begin simp [h.down] end }

def Module₂ : struc Ring :=
{ F := λ R, Module R,
  hom := λ R S f M₁ M₂, M₁ →ₛₗ[f] M₂,
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

def pi.struc (F : 𝒞 ⥤ Type) (G : struc (sigma₂ (of_functor F))) : struc 𝒞 :=
{ F := λ X, Π a : F.obj X, G.F ⟨X, a⟩,
  hom := λ X Y f x y, Π (a : F.obj X), 
    @struc.hom _ _ G ⟨X, a⟩ ⟨Y, F.map f a⟩ ⟨f, ⟨rfl⟩⟩ (x a) (y (F.map f a)),
  id := λ X x a, by convert (G.id (x a)); simp,
  comp := λ X Y Z x y z f g f' g' h H a, 
    by convert struc.comp G (f' a) (g' (F.map f a)) rfl; subst H; simp,
  id_comp := λ X a, begin
    intros,
    ext,
    simp,
    
  end }

-- Maybe think about W.

end struc
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
( F_iso : Π {A B : 𝒞}, (A ≅ B) → F A ≃ F B )
( F_iso_refl : Π {A : 𝒞}, F_iso (iso.refl A) = equiv.refl (F A) )
( F_iso_trans : Π {A B C : 𝒞} (e₁ : A ≅ B) (e₂ : B ≅ C), 
    equiv.trans (F_iso e₁) (F_iso e₂) = F_iso (iso.trans e₁ e₂) )
( hom : Π {A B : 𝒞} (f : A ⟶ B) (a : F A) (b : F B), Type x )
( hom_iso : Π {A₁ A₂ B₁ B₂ : 𝒞} 
    (f₁ : A₁ ⟶ B₁) (a₁ : F A₁) (b₁ : F B₁)
    (f₂ : A₂ ⟶ B₂) (a₂ : F A₂) (b₂ : F B₂)
    (eA : A₁ ≅ A₂) (eB : B₁ ≅ B₂)
    (hf : f₁ ≫ eB.hom = eA.hom ≫ f₂)
    (ha : a₂ = F_iso eA a₁)
    (hb : b₂ = F_iso eB b₁),
    hom f₁ a₁ b₁ ≃ hom f₂ a₂ b₂ )
( hom_iso_refl : Π {A B : 𝒞} 
    (f : A ⟶ B) (a : F A) (b : F B)
    (hf : f ≫ (iso.refl B).hom = (iso.refl A).hom ≫ f)
    (ha : a = F_iso (iso.refl A) a)
    (hb : b = F_iso (iso.refl B) b),
    hom_iso f a b f a b (iso.refl A) (iso.refl B) hf ha hb = equiv.refl (hom f a b) )
( hom_iso_trans : Π {A₁ A₂ A₃ B₁ B₂ B₃ : 𝒞}
    (f₁ : A₁ ⟶ B₁) (a₁ : F A₁) (b₁ : F B₁)
    (f₂ : A₂ ⟶ B₂) (a₂ : F A₂) (b₂ : F B₂)
    (f₃ : A₃ ⟶ B₃) (a₃ : F A₃) (b₃ : F B₃) 
    (eA₁₂ : A₁ ≅ A₂) (eB₁₂ : B₁ ≅ B₂)
    (eA₂₃ : A₂ ≅ A₃) (eB₂₃ : B₂ ≅ B₃)
    (hf₁₂ : f₁ ≫ eB₁₂.hom = eA₁₂.hom ≫ f₂)
    (hf₂₃ : f₂ ≫ eB₂₃.hom = eA₂₃.hom ≫ f₃)
    (ha₁₂ : a₂ = F_iso eA₁₂ a₁)
    (ha₂₃ : a₃ = F_iso eA₂₃ a₂)
    (hb₁₂ : b₂ = F_iso eB₁₂ b₁)
    (hb₂₃ : b₃ = F_iso eB₂₃ b₂),
    (hom_iso f₁ a₁ b₁ f₂ a₂ b₂ eA₁₂ eB₁₂ hf₁₂ ha₁₂ hb₁₂).trans
    (hom_iso f₂ a₂ b₂ f₃ a₃ b₃ eA₂₃ eB₂₃ hf₂₃ ha₂₃ hb₂₃) =
    hom_iso f₁ a₁ b₁ f₃ a₃ b₃ (eA₁₂.trans eA₂₃) (eB₁₂.trans eB₂₃) 
      (by simp [← hf₁₂, ← hf₂₃, category.assoc]) 
      (by simp [ha₂₃, ha₁₂, ← F_iso_trans]) 
      (by simp [hb₂₃, hb₁₂, ← F_iso_trans]) )
( id : Π {A : 𝒞} (a : F A), hom (𝟙 A) a a )
( hom_iso_id : Π {A₁ A₂ : 𝒞}
    (a₁ : F A₁) (a₂ : F A₂)
    (eA : A₁ ≅ A₂)
    (hf : 𝟙 A₁ ≫ eA.hom = eA.hom ≫ 𝟙 A₂)
    (ha : a₂ = F_iso eA a₁),
    hom_iso (𝟙 A₁) a₁ a₁ (𝟙 A₂) a₂ a₂ eA eA hf ha ha (id a₁) = id a₂ )
( comp : Π {A B C : 𝒞} {a : F A} {b : F B} {c : F C}
    {f : A ⟶ B} {g : B ⟶ C} (f' : hom f a b) (g' : hom g b c), 
    hom (f ≫ g) a c )
( hom_iso_comp : Π {A₁ A₂ B₁ B₂ C₁ C₂}
    (f₁ : A₁ ⟶ B₁) (g₁ : B₁ ⟶ C₁) (a₁ : F A₁) (b₁ : F B₁) (c₁ : F C₁)
    (f₂ : A₂ ⟶ B₂) (g₂ : B₂ ⟶ C₂) (a₂ : F A₂) (b₂ : F B₂) (c₂ : F C₂)
    (eA : A₁ ≅ A₂) (eB : B₁ ≅ B₂) (eC : C₁ ≅ C₂)
    (hf : f₁ ≫ eB.hom = eA.hom ≫ f₂)
    (hg : g₁ ≫ eC.hom = eB.hom ≫ g₂)
    (hfg : (f₁ ≫ g₁) ≫ eC.hom = eA.hom ≫ (f₂ ≫ g₂))
    (ha : a₂ = F_iso eA a₁)
    (hb : b₂ = F_iso eB b₁)
    (hc : c₂ = F_iso eC c₁)
    (f₁' : hom f₁ a₁ b₁)
    (g₁' : hom g₁ b₁ c₁),
    hom_iso (f₁ ≫ g₁) a₁ c₁ (f₂ ≫ g₂) a₂ c₂ eA eC hfg
       ha hc (comp f₁' g₁') = 
      comp (hom_iso f₁ a₁ b₁ f₂ a₂ b₂ eA eB hf ha hb f₁') 
        (hom_iso g₁ b₁ c₁ g₂ b₂ c₂ eB eC  hg hb hc g₁') )
( id_comp : Π {A B : 𝒞} {f : A ⟶ B} {a : F A} {b : F B}
    (f' : hom f a b), comp (id a) f' = hom_iso f a b (𝟙 A ≫ f) a b (iso.refl A) (iso.refl B) 
      (by simp) (by rw F_iso_refl; refl) (by rw F_iso_refl; refl) f' )
( comp_id : Π {A B : 𝒞} {f : A ⟶ B} {a : F A} {b : F B}
    (f' : hom f a b), comp f' (id b) = hom_iso f a b (f ≫ 𝟙 B) a b (iso.refl A) (iso.refl B) 
      (by simp) (by rw F_iso_refl; refl) (by rw F_iso_refl; refl) f' )
( assoc : Π {A B C D : 𝒞} {f : A ⟶ B} {g : B ⟶ C} {h : C ⟶ D}
    {a : F A} {b : F B} {c : F C} {d : F D}
    (f' : hom f a b) (g' : hom g b c) (h' : hom h c d),
    comp (comp f' g') h' = hom_iso (f ≫ (g ≫ h)) a d ((f ≫ g) ≫ h) a d 
      (iso.refl A) (iso.refl D) (by simp) (by rw F_iso_refl; refl) (by rw F_iso_refl; refl)
      (comp f' (comp g' h')) )

namespace struc

instance : has_coe_to_fun (struc 𝒞) (λ _, 𝒞 → Type w) :=
{ coe := struc.F }

variables {𝒞}

-- @[protect_proj] class GS (F : 𝒞 → Type w) :=
-- ( hom : Π {A B : 𝒞} (f : A ⟶ B) (a : F A) (b : F B), Type x )
-- ( id : Π {A : 𝒞} (a b : F A) (h : a = b) (f : A ⟶ A) (hf : f = 𝟙 A), hom f a b )

attribute [simp] struc.id_comp struc.comp_id struc.hom_iso_refl struc.F_iso_refl struc.F_iso_trans
  struc.hom_iso_trans

variables (F : struc 𝒞) 

-- lemma assoc_left {A B C D : 𝒞} {f : A ⟶ B} {g : B ⟶ C} {h : C ⟶ D}
--     {a : F A} {b : F B} {c : F C} {d : F D}
--     (f' : F.hom f a b) (g' : F.hom g b c) (h' : F.hom h c d)
--     (i : A ⟶ C) (k : A ⟶ D)
--     (hi : f ≫ g = i) (hk : i ≫ h = k) :
--     F.comp (F.comp f' g' hi) h' hk = F.comp f'
--       (F.comp g' h' rfl) (by rw [← hk, ← hi, category.assoc]) :=
-- begin
--   substs i k,
--   rw struc.assoc,
-- end

-- lemma comp_eq_cast {A B C : 𝒞} {f : A ⟶ B} {g : B ⟶ C} 
--   {a : F A} {b : F B} {c : F C} (f' : F.hom f a b) (g' : F.hom g b c)
--   (i : A ⟶ C) (hi : f ≫ g = i)
--   (j : A ⟶ C) (hj : f ≫ g = j) :
--   F.comp f' g' hi = cast (by substs i j) (F.comp f' g' hj) :=
-- begin
--   substs i j, refl
-- end

-- lemma assoc_left' {A B C D : 𝒞} {f : A ⟶ B} {g : B ⟶ C} {h : C ⟶ D}
--     {a : F A} {b : F B} {c : F C} {d : F D}
--     (f' : F.hom f a b) (g' : F.hom g b c) (h' : F.hom h c d)
--     (i : A ⟶ C) (k : A ⟶ D)
--     (hi : f ≫ g = i) (hk : i ≫ h = k) :
--     F.comp (F.comp f' g' hi) h' hk = cast (by rw [← hk, ← hi, category.assoc]) 
--       (F.comp f' (F.comp g' h' rfl) rfl)  :=
-- begin
--   rw struc.assoc_left,
--   substs i k,
--   rw [comp_eq_cast]
-- end

-- lemma id_comp' {A B : 𝒞} {f : A ⟶ B} (g : A ⟶ B) {a : F A} {b : F B}
--   (h : 𝟙 A ≫ f = g) (f' : F.hom f a b) : 
--   F.comp (F.id a) f' h = cast (by rw [← h, category.id_comp]) f' :=
-- begin
--   rw [category.id_comp] at h,
--   subst h,
--   simp
-- end

-- lemma comp_id' {A B : 𝒞} {f : A ⟶ B} (g : A ⟶ B) {a : F A} {b : F B}
--   (h : f ≫ 𝟙 B = g) (f' : F.hom f a b) : 
--   F.comp f' (F.id b) h = cast (by rw [← h, category.comp_id]) f' :=
-- begin
--   rw [category.comp_id] at h,
--   subst h,
--   simp
-- end 

def sigma₂ (F : struc 𝒞) : Type* := sigma F

instance : category_struct (sigma₂ F) :=
{ hom := λ A B, Σ (f : A.1 ⟶ B.1), F.hom f A.2 B.2,
  id := λ A, ⟨𝟙 A.1, F.id A.2⟩,
  comp := λ A B C f g, ⟨f.1 ≫ g.1, F.comp f.2 g.2⟩ }

variable {F}

lemma sigma₂.hom_ext {A B : sigma₂ F} {f g : A ⟶ B} 
  (h₁ : f.1 = g.1) (h₂ : F.hom_iso f.1 A.2 B.2 g.1 A.2 B.2 
    (iso.refl A.1) (iso.refl B.1) (by simp *) (by simp *) (by simp *) f.2 = g.2) :
  f = g :=
begin
  cases A,
  cases B,
  cases f,
  cases g,
  dsimp at *,
  subst h₁,
  simp at h₂,
  subst h₂
end

def sigma_category : category_struct (sigma F) :=
{ hom := λ A B, Σ (f : A.1 ⟶ B.1), F.hom f A.2 B.2,
  id := λ A, ⟨𝟙 A.1, F.id A.2⟩,
  comp := λ A B C f g, ⟨f.1 ≫ g.1, F.comp f.2 g.2⟩ }

@[simp] lemma comp_fst {A B C : sigma₂ F} (f : A ⟶ B) (g : B ⟶ C) :
  (f ≫ g).fst = f.1 ≫ g.1 := rfl

@[simp] lemma comp_snd {A B C : sigma₂ F} (f : A ⟶ B) (g : B ⟶ C) :
  (f ≫ g).snd = F.comp f.2 g.2 := rfl

@[simp] lemma id_fst {A : sigma₂ F} : sigma.fst (𝟙 A) = 𝟙 A.1 := rfl

@[simp] lemma id_snd {A : sigma₂ F} : sigma.snd (𝟙 A) = F.id A.2 := rfl

section

local attribute [instance] sigma_category

instance sigma.category : category (sigma₂ F) :=
{ id_comp' := λ A B f, begin
      refine sigma₂.hom_ext _ _,
      { simp },
      { simp,
        rw [← equiv.trans_apply], 
        erw F.hom_iso_trans,
        simp }
    end,
  comp_id' := λ A B f, begin
      refine sigma₂.hom_ext _ _,
      { simp },
      { simp,
        rw [← equiv.trans_apply], 
        erw F.hom_iso_trans,
        simp }
    end,
  assoc' := λ A B C D f g h, begin
      refine sigma₂.hom_ext _ _,
      { simp [category.assoc] },
      { simp [struc.assoc],
        rw ← equiv.trans_apply,
        erw F.hom_iso_trans,
        simp,
        erw [F.hom_iso_refl], 
        refl }
    end, }

end

instance (X : 𝒞) : category_struct (F X) :=
{ hom := λ A B, F.hom (𝟙 X) A B,
  id := λ A, F.id A,
  comp := λ A B C f g, F.hom_iso (𝟙 X ≫ 𝟙 X) A C (𝟙 X) A C (iso.refl X) (iso.refl X) 
    (by simp) (by simp) (by simp) (F.comp f g) }

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
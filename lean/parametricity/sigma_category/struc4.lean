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
( id : Π (A : sigma F), hom A A (𝟙 A.1) )
( comp : Π {A B C : sigma F}
    (f : Σ f : A.1 ⟶ B.1, hom A B f)
    (g : Σ g : B.1 ⟶ C.1, hom B C g),
    hom A C (f.1 ≫ g.1) )
( id_comp' : Π {A B : sigma F} (f : Σ f : A.1 ⟶ B.1, hom A B f), 
    sigma.mk (𝟙 A.1 ≫ f.1) (comp ⟨𝟙 A.1, id A⟩ f) = f )
( comp_id' : Π {A B : sigma F} (f : Σ f : A.1 ⟶ B.1, hom A B f), 
    sigma.mk (f.1 ≫ 𝟙 B.1) (comp f ⟨𝟙 B.1, id B⟩) = f )
( assoc' : Π {A B C D : sigma F} 
    (f : Σ f : A.1 ⟶ B.1, hom A B f)
    (g : Σ g : B.1 ⟶ C.1, hom B C g)
    (h : Σ h : C.1 ⟶ D.1, hom C D h), 
    sigma.mk ((f.1 ≫ g.1) ≫ h.1) (comp ⟨f.1 ≫ g.1, comp f g⟩ h) = 
    sigma.mk (f.1 ≫ (g.1 ≫ h.1)) (comp f ⟨g.1 ≫ h.1, comp g h⟩) )

@[protect_proj] structure strucp : Type (max u v (w+1)) :=
( F : 𝒞 → Type w )
( hom : Π (A B : sigma F) (f : A.1 ⟶ B.1), Prop )
( id : Π (A : sigma F), hom A A (𝟙 A.1) )
( comp : Π {A B C : sigma F}
    (f : { f : A.1 ⟶ B.1 // hom A B f } )
    (g : { g : B.1 ⟶ C.1 // hom B C g } ),
    hom A C (f.1 ≫ g.1) )

namespace struc

instance : has_coe_to_fun (struc 𝒞) (λ _, 𝒞 → Type w) :=
{ coe := struc.F }

variables {𝒞} {F : struc 𝒞} {Fp : strucp 𝒞}

instance : category (sigma F) :=
{ hom := λ A B, Σ f : A.1 ⟶ B.1, F.hom A B f,
  id := λ A, ⟨𝟙 A.1, F.id A⟩,
  comp := λ A B C f g, ⟨f.1 ≫ g.1, F.comp f g⟩,
  comp_id' := λ A B f, F.comp_id' f,
  id_comp' := λ A B f, F.id_comp' f,
  assoc' := λ A B C D f g h, F.assoc' f g h }

def fst : sigma F ⥤ 𝒞 :=
{ obj := sigma.fst,
  map := λ _ _, sigma.fst,
  map_id' := λ _, rfl,
  map_comp' := λ _ _ _ _ _, rfl }

instance (X : 𝒞) : category_struct (F X) :=
{ hom := λ A B, F.hom ⟨X, A⟩ ⟨X, B⟩ (𝟙 X),
  id := λ A, F.id ⟨X, A⟩,
  comp := λ A B C f g, cast  
    (show F.hom ⟨X, A⟩ ⟨X, C⟩ (𝟙 X ≫ 𝟙 X) = F.hom ⟨X, A⟩ ⟨X, C⟩ (𝟙 X), by simp)
    (@struc.comp 𝒞 _ F ⟨X, A⟩ ⟨X, B⟩ ⟨X, C⟩ ⟨𝟙 X, f⟩ ⟨𝟙 X, g⟩), }

lemma comp_mk_cast_left {A B C : sigma F}
  {f₁ f₂ : A.fst ⟶ B.fst} (h : f₁ = f₂)
  (f' : F.hom A B f₂)
  {g : Σ (g : B.fst ⟶ C.fst), F.hom B C g} :
  F.comp ⟨f₁, cast (by rw h) f'⟩ g = 
  cast (show F.hom A C (f₂ ≫ g.fst) = F.hom A C (f₁ ≫ g.fst),
    by subst h) (F.comp ⟨f₂, f'⟩ g) :=
by subst h; refl

lemma comp_mk_cast_right {A B C : sigma F}
  {f : Σ (f : A.1 ⟶ B.1), F.hom A B f}
  {g₁ g₂ : B.fst ⟶ C.fst} (h : g₁ = g₂) 
  (g' : F.hom B C g₂) :
  F.comp f ⟨g₁, cast (by rw h) g'⟩ = 
  cast (show F.hom A C (f.1 ≫ g₂) = F.hom A C (f.1 ≫ g₁),
    by subst h) (F.comp f ⟨g₂, g'⟩) :=
by subst h; refl

instance (X : 𝒞) : category (F X) :=
{ comp_id' := λ A B f, cast_eq_iff_heq.2 $
    (sigma.ext_iff.1 (@category.comp_id (sigma F) _ ⟨X, A⟩ ⟨X, B⟩ ⟨𝟙 X, f⟩)).2,
  id_comp' := λ A B f, cast_eq_iff_heq.2 $
    (sigma.ext_iff.1 (@category.id_comp (sigma F) _ ⟨X, A⟩ ⟨X, B⟩ ⟨𝟙 X, f⟩)).2,
  assoc' := λ A B C D f g h, begin
    dunfold category_struct.comp,
    dsimp,
    rw [comp_mk_cast_left, comp_mk_cast_right, cast_cast, cast_cast, cast_eq_iff_heq],
    symmetry,
    rw [← cast_eq_iff_heq, cast_cast, cast_eq_iff_heq],
    exact (sigma.ext_iff.1 (@category.assoc (sigma F) _ ⟨X, A⟩ ⟨X, B⟩ ⟨X, C⟩ ⟨X, D⟩
      ⟨𝟙 X, f⟩ ⟨𝟙 X, g⟩ ⟨𝟙 X, h⟩)).2.symm,
    all_goals { simp; refl }
  end }

open opposite

-- def of_functor (F : 𝒞 ⥤ Type w) : struc 𝒞 :=
-- { F := F.obj,
--   cat := 
--   { hom := λ A B, {f : A.1 ⟶ B.1 // F.map f A.2 = B.2 },
--     id := λ A, ⟨𝟙 A.1, by simp⟩,
--     comp := λ A B C f g, ⟨f.1 ≫ g.1, by simp [f.prop, g.prop]⟩,
--     comp_id' := λ _ _ _, subtype.ext (category.comp_id _),
--     id_comp' := λ _ _ _, subtype.ext (category.id_comp _),
--     assoc' := λ _ _ _ _ _ _ _, subtype.ext (category.assoc _ _ _) },
--   fst_map := λ _ _, subtype.val,
--   fst_map_id := by intros; refl,
--   fst_map_comp := by intros; refl }

-- def Module₂ : struc Ring :=
-- { F := λ R, Module R,
--   cat :=
--   { hom := λ A B, Σ f : A.1 ⟶ B.1, A.2 →ₛₗ[f] B.2,
--     id := λ A, ⟨𝟙 A.1, linear_map.id⟩,
--     comp := λ A B C f g, ⟨f.1 ≫ g.1, 
--       @linear_map.comp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ⟨rfl⟩ g.2 f.2⟩,
--     comp_id' := by { intros, cases f, cases f_fst, cases f_snd, refl },
--     id_comp' := by { intros, cases f, cases f_fst, cases f_snd, refl },
--     assoc' := by { intros, refl } },
--   fst_map := λ _ _ f, f.fst,
--   fst_map_id := by intros; refl,
--   fst_map_comp := by intros; refl }


def of_category (𝒟 : Type*) [category 𝒟] : struc 𝒞 :=
{ F := λ _, 𝒟,
  
  fst_map := λ _ _, prod.fst,
  fst_map_id := λ _, rfl,
  fst_map_comp := by intros; refl }

variable (𝒞)

def type : struc 𝒞 := of_category (Type v)

def prop : struc 𝒞 := of_category Prop

lemma hcongr {α α' : Sort*}
  {β : α → Sort*} {β' : α' → Sort*} {f : Π a, β a}
  {g : Π a, β' a} (hβ : β == β')
  (a a') (h : f == g) (ha : a == a') :
  f a == g a' :=
begin
  have := type_eq_of_heq ha,
  subst this,
  simp at *,
  substs hβ ha,
  simp at *,
  subst h
end


def sigma_pi (F : 𝒞 ⥤ Type) (G : struc (sigma (of_functor F))) : struc 𝒞 :=
{ F := λ X, Π a : F.obj X, G.F ⟨X, a⟩,
  cat := 
  { hom := λ A B, Σ (f : A.1 ⟶ B.1), 
      Π (a : of_functor F A.1) (b : of_functor F B.1) (hab : b = F.map f a), 
      sigma.mk (sigma.mk A.1 a) (A.2 a) ⟶ sigma.mk (sigma.mk B.1 b) (B.2 b),
    id := λ X, ⟨𝟙 X.1, λ x y h, cast (by simp [F.map_id] at h; rw h) 
        (𝟙 (sigma.mk (sigma.mk X.1 x) (X.2 x)))⟩,
    comp := λ X Y Z f g, ⟨f.1 ≫ g.1, 
        λ a b h, cast (by simp) (f.2 a _ rfl ≫ g.2 (F.map f.1 a) b (by simp [h]))⟩,
    comp_id' := λ X Y f, begin 
        cases f with f₁ f₂,
        ext,
        { simp },
        { refl },
        { intros a a' h,
          rw heq_iff_eq at h,
          subst a',
          dsimp,
          apply function.hfunext,
          { refl },
          { intros b b' h,
            rw [heq_iff_eq] at h,
            subst b',
            apply function.hfunext,
            simp,
            intros _ h _,
            subst h,
            simp } }
      end,
    id_comp' := λ X Y f, begin 
        cases f with f₁ f₂,
        ext,
        { simp },
        { refl },
        { intros a a' h,
          dsimp,
          rw heq_iff_eq at h,
          subst a',
          apply function.hfunext,
          { refl },
          { intros b b' h,
            rw heq_iff_eq at h,
            subst b',
            apply function.hfunext,
            { simp * at * },
            { intros,
              simp * at *,
              convert category.id_comp (f₂ a b a'),
              { simp },
              { rw [F.map_id],
                refl },
              { simp },
              { simp } } } }
      end,
    assoc' := λ W X Y Z f g h, begin
        ext, simp [category.assoc],
        intros a a' h,
        rw [heq_iff_eq] at h,
        subst h,
        simp,
        apply function.hfunext,
        { refl },
        { intros b b' h,
          rw heq_iff_eq at h,
          subst b',
          apply function.hfunext,
          { simp [category.assoc] },
          { intros c c' h,
            simp,
            dsimp,
            congr,
            { simp },
            { rw F.map_comp, refl },
            { apply hcongr,
              apply function.hfunext,
              rw F.map_comp; refl,
              intros,
              rw [F.map_comp],
              refl,
              rw [F.map_comp],
              refl,
              exact proof_irrel_heq _ _ },
            { apply hcongr,
              apply function.hfunext,
              rw F.map_comp; refl,
              intros,
              rw [F.map_comp],
              refl,
              rw [F.map_comp],
              refl,
              exact proof_irrel_heq _ _ } } }
      end },
  fst_map := λ _ _ f, f.fst,
  fst_map_id := by intros; refl,
  fst_map_comp := by intros; refl }

example : 1 = 1 := rfl

def sigma_arrow (F : 𝒞 ⥤ Type) (G : struc 𝒞) : struc 𝒞 :=
{ F := λ X, F.obj X → G X,
  cat := 
  { hom := λ A B, Σ (f : A.1 ⟶ B.1), 
      Π (a : of_functor F A.1) (b : of_functor F B.1) (h : b = F.map f a), 
      { g : sigma.mk A.1 (A.2 a) ⟶ sigma.mk B.1 (B.2 b) // fst.map g = f } ,
    id := λ X, ⟨𝟙 X.1, λ x y h, ⟨cast (by simp [h]) (𝟙 (sigma.mk X.1 (X.2 x))), 
      begin simp, end⟩⟩,
    comp := λ X Y Z f g, ⟨f.1 ≫ g.1, 
        λ x z h, cast (by simp [h]) (f.2 x (F.map f.1 x) rfl ≫ g.2 (F.map f.1 x) z (by simp [h]))⟩,
    comp_id' := λ X Y f,  
      begin 
        cases f with f₁ f₂,
        ext,
        { simp },
        { refl },
        { intros a a' h,
          rw heq_iff_eq at h,
          subst a',
          apply function.hfunext,
          { refl },
          { intros b b' h,
            rw heq_iff_eq at h,
            subst b',
            dsimp,
            apply function.hfunext,
            { simp },
            { intros _ h _,
              subst h,
              simp } } }
      end,
    id_comp' := λ X Y f, begin 
        cases f with f₁ f₂,
        ext,
        { simp },
        { refl },
        { intros a a' h,
          dsimp,
          rw heq_iff_eq at h,
          subst a',
          apply function.hfunext,
          { refl },
          { intros b b' h,
            rw heq_iff_eq at h,
            subst b',
            apply function.hfunext,
            { simp * at * },
            { intros,
              simp * at *,
              convert category.id_comp (f₂ a b a'),
              { simp },
              { simp },
              { simp } } } }
      end,
    assoc' := λ W X Y Z f g h, begin
        ext, simp [category.assoc],
        intros a a' h,
        rw [heq_iff_eq] at h,
        subst h,
        simp,
        apply function.hfunext,
        { refl },
        { intros b b' h,
          rw heq_iff_eq at h,
          subst b',
          apply function.hfunext,
          { simp [category.assoc] },
          { intros c c' h,
            simp,
            dsimp,
            congr,
            { simp },
            { apply hcongr,
              apply function.hfunext,
              rw F.map_comp; refl,
              intros,
              rw [F.map_comp],
              refl,
              rw [F.map_comp],
              refl,
              exact proof_irrel_heq _ _ },
            { apply hcongr,
              apply function.hfunext,
              rw F.map_comp; refl,
              intros,
              rw [F.map_comp],
              refl,
              rw [F.map_comp],
              refl,
              exact proof_irrel_heq _ _ } } }
      end },
  fst_map := λ _ _ f, f.fst,
  fst_map_id := by intros; refl,
  fst_map_comp := by intros; refl }

-- def sigma_arrow (F : struc 𝒞) (G : struc 𝒞) : struc 𝒞 :=
-- { F := λ X, Σ (i : F X → G X), 
--     (Π (a b : F X), (sigma.mk X a ⟶ ⟨X, b⟩) → 
--       { f : sigma.mk X (i a) ⟶ ⟨X, i b⟩ // fst.map f = 𝟙 X}),
--   cat := 
--   { hom := λ A B, Σ (f : A.1 ⟶ B.1), Π (a : F A.1) (b : F B.1),
--       (sigma.mk A.1 a ⟶ sigma.mk B.1 b) →
--       { g : (sigma.mk A.1 (A.2.1 a)) ⟶ (sigma.mk B.1 (B.2.1 b)) // fst.map g = f },
--     id := λ A, ⟨𝟙 _, λ a b f, A.2.2 a b f⟩,
--     comp := λ A B C f g, ⟨f.1 ≫ g.1, λ a c h, 
--       begin
--         have := sigma.snd f a,
        
--       end⟩,
--     comp_id' := sorry,
--     id_comp' := sorry,
--     assoc' := sorry },

--   fst_map := λ _ _ f, f.fst,
--   fst_map_id := by intros; refl,
--   fst_map_comp := by intros; refl }


-- def sigma_pi₂ (F : struc 𝒞) (G : struc (sigma F)) : struc 𝒞 :=
-- { F := λ X, Σ (i : Π a : F X, G.F ⟨X, a⟩), 
--     (Π (a b : F X) (f : sigma.mk X a ⟶ sigma.mk X b), 
--       { g : sigma.mk (sigma.mk X a) (i a) ⟶ ⟨⟨X, b⟩, i b⟩ // fst.map g = f }),
--   cat := 
--   { hom := λ A B, Σ (f : A.1 ⟶ B.1), (Π (a : F A.1) (b : F B.1), 
--       (sigma.mk A.1 a ⟶ sigma.mk B.1 b) → 
--         (sigma.mk (sigma.mk A.1 a) (A.2.1 a) ⟶ ⟨⟨B.1, b⟩, B.2.1 b⟩)),
--     id := λ A, ⟨𝟙 _, λ a b f, (A.2.2 a b f).1⟩,
--     comp := λ A B C f g, ⟨f.1 ≫ g.1, λ a c h, 
--       begin
--         have := sigma.snd f a,
        
--       end⟩,
--     comp_id' := sorry,
--     id_comp' := sorry,
--     assoc' := sorry },

--   fst_map := λ _ _ f, f.fst,
--   fst_map_id := by intros; refl,
--   fst_map_comp := by intros; refl }

end struc
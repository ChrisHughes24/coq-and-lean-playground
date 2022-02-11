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
[ cat : category.{x} (sigma F) ]
( fst_map : Π {A B : sigma F} (f : A ⟶ B), A.1 ⟶ B.1 )
( fst_map_id : ∀ (A : sigma F), fst_map (𝟙 A) = 𝟙 A.1 )
( fst_map_comp : ∀ {A B C : sigma F} (f : A ⟶ B) (g : B ⟶ C),
    fst_map (f ≫ g) = fst_map f ≫ fst_map g )

namespace struc

instance : has_coe_to_fun (struc 𝒞) (λ _, 𝒞 → Type w) :=
{ coe := struc.F }

variables {𝒞} {F : struc 𝒞}

instance : category (sigma F) := F.cat

def fst : sigma F ⥤ 𝒞 :=
{ obj := sigma.fst,
  map := F.fst_map,
  map_id' := F.fst_map_id,
  map_comp' := F.fst_map_comp }

instance (X : 𝒞) : category_struct (F X) :=
{ hom := λ A B, { f : sigma.mk X A ⟶ ⟨X, B⟩ // fst.map f = 𝟙 X },
  id := λ A, ⟨𝟙 _, by simp; refl⟩,
  comp := λ A B C f g, ⟨f.1 ≫ g.1, by erw [functor.map_comp, f.2, g.2, category.comp_id]⟩ }

instance (X : 𝒞) : category (F X) :=
{ comp_id' := λ _ _ _, subtype.ext (category.comp_id _),
  id_comp' := λ _ _ _, subtype.ext (category.id_comp _),
  assoc' := λ _ _ _ _ _ _ _, subtype.ext (category.assoc _ _ _) }

open opposite

def of_functor (F : 𝒞 ⥤ Type w) : struc 𝒞 :=
{ F := F.obj,
  cat := 
  { hom := λ A B, {f : A.1 ⟶ B.1 // F.map f A.2 = B.2 },
    id := λ A, ⟨𝟙 A.1, by simp⟩,
    comp := λ A B C f g, ⟨f.1 ≫ g.1, by simp [f.prop, g.prop]⟩,
    comp_id' := λ _ _ _, subtype.ext (category.comp_id _),
    id_comp' := λ _ _ _, subtype.ext (category.id_comp _),
    assoc' := λ _ _ _ _ _ _ _, subtype.ext (category.assoc _ _ _) },
  fst_map := λ _ _, subtype.val,
  fst_map_id := by intros; refl,
  fst_map_comp := by intros; refl }

def Module₂ : struc Ring :=
{ F := λ R, Module R,
  cat :=
  { hom := λ A B, Σ f : A.1 ⟶ B.1, A.2 →ₛₗ[f] B.2,
    id := λ A, ⟨𝟙 A.1, linear_map.id⟩,
    comp := λ A B C f g, ⟨f.1 ≫ g.1, 
      @linear_map.comp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ⟨rfl⟩ g.2 f.2⟩,
    comp_id' := by { intros, cases f, cases f_fst, cases f_snd, refl },
    id_comp' := by { intros, cases f, cases f_fst, cases f_snd, refl },
    assoc' := by { intros, refl } },
  fst_map := λ _ _ f, f.fst,
  fst_map_id := by intros; refl,
  fst_map_comp := by intros; refl }


def of_category (𝒟 : Type*) [category 𝒟] : struc 𝒞 :=
{ F := λ _, 𝒟,
  cat := 
  { hom := λ A B, (A.1 ⟶ B.1) × (A.2 ⟶ B.2),
    id := λ _, (𝟙 _, 𝟙 _),
    comp := λ A B C f g, (f.1 ≫ g.1, f.2 ≫ g.2),
    comp_id' := λ A B f, prod.ext (category.comp_id _) (category.comp_id _),
    id_comp' := λ A B f, prod.ext (category.id_comp _) (category.id_comp _),
    assoc' := λ A B C D f g h, prod.ext (category.assoc _ _ _) (category.assoc _ _ _) },
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
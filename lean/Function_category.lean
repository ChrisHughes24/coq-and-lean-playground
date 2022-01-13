import category_theory.limits.shapes.pullbacks
import category_theory.limits.shapes.types

namespace category_theory

open limits category_theory.limits.types

@[protect_proj] structure Function : Type 1 :=
( to_fun : Type → Type )
( R : Π {X₁ X₂}, (X₁ → X₂ → Prop) → to_fun X₁ → to_fun X₂ → Prop )

namespace Function

instance : has_coe_to_fun Function (λ _, Type → Type) :=
{ coe := Function.to_fun }

@[simp] lemma coe_mk (f h) : ⇑(Function.mk f h) = f := rfl

structure hom (F G : Function) : Type 1 :=
( to_fun : Π {X}, F X → G X )
( parametric : ∀ {X₁ X₂} {R : X₁ → X₂ → Prop} {x₁ : F X₁} {x₂ : F X₂}, 
    F.R R x₁ x₂ → G.R R (to_fun x₁) (to_fun x₂) )

instance : category_struct Function :=
{ hom := λ F G, hom F G,
  id := λ F, ⟨λ _, id, λ _ _ _ _ _, id⟩,
  comp := λ X Y Z n₁ n₂, ⟨λ X x, n₂.1 (n₁.1 x), λ X₁ X₂ R x₁ x₂ h, n₂.2 (n₁.2 h)⟩ } 

instance (F G : Function) : has_coe_to_fun (F ⟶ G) (λ _, Π {X}, F X → G X) :=
{ coe := hom.to_fun }

lemma hom.ext_iff' {F G : Function} {f g : F ⟶ G} :
  f = g ↔ (@coe_fn _ _ _ f : Π {X : Type}, F X → G X) = coe_fn g := 
by cases f; cases g; simp [hom.mk.inj_eq]; refl

lemma hom.ext_iff {F G : Function} {f g : F ⟶ G} :
  f = g ↔ ∀ {X : Type} (x : F X), f x = g x :=
by simp [hom.ext_iff', function.funext_iff]

@[ext] lemma hom.ext {F G : Function} {f g : F ⟶ G}
  (h : ∀ (X : Type) (x : F X), f x = g x) : f = g :=
hom.ext_iff.2 h

@[simp] lemma coe_id (F : Function)  : 
  (coe_fn (𝟙 F) : Π (X : Type), F X → F X) = (λ {X : Type}, @id (F X)) := rfl

@[simp] lemma coe_comp (F G H : Function) (f : F ⟶ G) (g : G ⟶ H) :
  coe_fn (f ≫ g) = (λ {X : Type} (x : F X), g (f x)) := rfl

instance : category Function := {}

def app (X : Type) : Function ⥤ Type :=
{ obj := λ F, F X,
  map := λ F G f a, f a } 

instance : has_pullbacks Function := 
@has_pullbacks_of_has_limit_cospan _ _ 
(λ (F G H : Function) f g, ⟨⟨
{ cone := ⟨{ to_fun := λ X, pullback_obj ((app X).map f) ((app X).map g),
             R := λ X₁ X₂ R x y, F.R R x.1.1 y.1.1 ∧ G.R R x.1.2 y.1.2 },
    ⟨λ X, ⟨λ Y, option.cases_on X (λ x, f x.1.1) 
        (λ X, limits.walking_pair.cases_on X (λ x, x.1.1) (λ x, x.1.2)), 
      begin 
        intros X₁ X₂ R x y,
        cases X,
        { exact λ h, f.2 h.1 },
        { cases X, 
          exact and.left,
          exact and.right }
      end⟩, begin 
        intros X Y f, 
        cases f with f₁ f₂,
        cases X,
        { refl },
        { cases X; refl },
        { cases f₂,
          { refl },
          { ext Z x,
            rcases x with ⟨⟨x₁, x₂⟩, hx⟩,
            exact hx } }     
      end⟩⟩,
  is_limit :=
    ⟨λ s, 
      ⟨λ X x, ⟨⟨s.π.app limits.walking_span.left x, 
                s.π.app limits.walking_span.right x⟩, 
          (congr_fun (congr_fun (hom.ext_iff'.1 (s.2.2 limits.walking_cospan.hom.inl)) X) x).symm.trans 
          (congr_fun (congr_fun (hom.ext_iff'.1 (s.2.2 limits.walking_cospan.hom.inr)) X) x)⟩,
      λ X₁ X₂ R x₁ x₂ h,  ⟨(s.2.1 walking_span.left).2 h,
          (s.2.1 walking_span.right).2 h⟩⟩, 
    begin
      intros s j,
      cases j,
      { have := s.2.2 (limits.walking_cospan.hom.inl),
        dsimp at this,
        rw [category.id_comp] at this,
        refine eq.trans _ this.symm,
        refl },
      { cases j; ext; refl }
    end, 
    begin 
      intros s m hm,
      ext,
      { have := hm limits.walking_span.left,
        simp only [hom.ext_iff] at this,
        exact this _ },
      { have := hm limits.walking_span.right,
        simp only [hom.ext_iff] at this,
        exact this _ }
    end⟩ } ⟩⟩)

end Function

end category_theory
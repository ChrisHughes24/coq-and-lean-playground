import tactic
import category_theory.functor
import data.W.basic

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

namespace gen_structure

variables (F : 𝒞 → Type w) [gen_structure F]

instance : category_struct (sigma F) :=
{ hom := λ A B, Σ (f : A.1 ⟶ B.1), gen_structure.hom f A.2 B.2,
  id := λ A, ⟨𝟙 A.1, gen_structure.id A.2⟩,
  comp := λ A B C f g, ⟨f.1 ≫ g.1, gen_structure.comp f.2 g.2⟩  }

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


def app (A : 𝒞) : 

end gen_structure
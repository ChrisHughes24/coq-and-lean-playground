import category_theory.limits.preserves.basic
import set_theory.ordinal

open category_theory category_theory.limits category_theory.functor

universes v₁ v₂ u₁ u₂ 

structure colimit (𝒞 : Type 1) [category.{0} 𝒞] : Type 1 :=
( diag : Type )
[ category : category.{0} diag ]
( F : diag ⥤ 𝒞 )
( colimit_cocone : colimit_cocone F )

attribute [instance] colimit.category

constant fixing_cocompletion {𝒞 : Type 1} [category.{0} 𝒞] {ι : Type 1} (colimits : ι → colimit 𝒞) : Type 1

namespace fixing_cocompletion

variables {𝒞 : Type 1} [category.{0} 𝒞] {ι : Type 1} (colimits : ι → colimit 𝒞) 

@[instance] protected constant category : category.{0} (fixing_cocompletion colimits)

@[instance] protected constant has_colimits : has_colimits_of_size.{0 0} (fixing_cocompletion colimits)

constant of_cat : 𝒞 ⥤ fixing_cocompletion colimits

constant of_cat_preserves : Π i : ι, preserves_colimit (colimits i).F (of_cat colimits)

variable {colimits}

constant extend {𝒟 : Type 1} [category.{0} 𝒟] (F : 𝒞 ⥤ 𝒟)
  (hF : Π i : ι, preserves_colimit (colimits i).F F) : fixing_cocompletion colimits ⥤ 𝒟

constant extend_preserves {𝒟 : Type 1} [category.{0} 𝒟] (F : 𝒞 ⥤ 𝒟)
  (hF : Π i : ι, preserves_colimit (colimits i).F F) :
  preserves_colimits.{0 0} (extend F hF) 

constant of_cat_extend {𝒟 : Type 1} [category.{0} 𝒟] (F : 𝒞 ⥤ 𝒟)
  (hF : Π i : ι, preserves_colimit (colimits i).F F) :
  of_cat colimits ⋙ extend F hF ≅ F 

constant extend_unique {𝒟 : Type 1} [category.{0} 𝒟] (F : 𝒞 ⥤ 𝒟)
  (hF : Π i : ι, preserves_colimit (colimits i).F F)
  (G : fixing_cocompletion colimits ⥤ 𝒟)
  (hG : preserves_colimits.{0 0} (extend F hF))
  (hG_commutes : of_cat colimits ⋙ G ≅ F) :
  G ≅ extend F hF

end fixing_cocompletion

structure limit (𝒞 : Type 1) [category.{0} 𝒞] : Type 1 :=
( diag : Type )
[ category : category.{0} diag ]
( F : diag ⥤ 𝒞 )
( limit_cone : limit_cone F )

attribute [instance] limit.category

constant fixing_completion {𝒞 : Type 1} [category.{0} 𝒞] {ι : Type 1} (limits : ι → limit 𝒞) : Type 1

namespace fixing_completion

variables {𝒞 : Type 1} [category.{0} 𝒞] {ι : Type 1} (limits : ι → limit 𝒞) 

@[instance] protected constant category : category.{0} (fixing_completion limits)

@[instance] protected constant has_limits : has_limits_of_size.{0 0} (fixing_completion limits)

constant of_cat : 𝒞 ⥤ fixing_completion limits

constant of_cat_preserves : Π i : ι, preserves_limit (limits i).F (of_cat limits)

variable {limits}

constant extend {𝒟 : Type 1} [category.{0} 𝒟] (F : 𝒞 ⥤ 𝒟)
  (hF : Π i : ι, preserves_limit (limits i).F F) : fixing_completion limits ⥤ 𝒟

constant extend_preserves {𝒟 : Type 1} [category.{0} 𝒟] (F : 𝒞 ⥤ 𝒟)
  (hF : Π i : ι, preserves_limit (limits i).F F) :
  preserves_colimits.{0 0} (extend F hF) 

constant of_cat_extend {𝒟 : Type 1} [category.{0} 𝒟] (F : 𝒞 ⥤ 𝒟)
  (hF : Π i : ι, preserves_limit (limits i).F F) :
  of_cat limits ⋙ extend F hF ≅ F 

constant extend_unique {𝒟 : Type 1} [category.{0} 𝒟] (F : 𝒞 ⥤ 𝒟)
  (hF : Π i : ι, preserves_limit (limits i).F F)
  (G : fixing_completion limits ⥤ 𝒟)
  (hG : preserves_colimits.{0 0} (extend F hF))
  (hG_commutes : of_cat limits ⋙ G ≅ F) :
  G ≅ extend F hF

end fixing_completion

namespace totally_ordered_colimit

structure ordinal_seq : Type 2 :=
( α : Type )
[ linear_order : linear_order α ]
( obj : Π i : α, Type 1 )
[ cat : Π i, category.{0} (obj i) ]
( map : Π i j : α, i ≤ j → (obj i ⥤ obj j) )
[ full : Π (i j : α) (hij : i ≤ j), full (map i j hij) ]
[ faithful : Π (i j : α) (hij : i ≤ j), faithful (map i j hij) ]
( map_id : Π i, map i i le_rfl ≅ 𝟭 (obj i) )
( map_comp : Π i j k (hij : i ≤ j) (hjk : j ≤ k), 
    map i k (le_trans hij hjk) ≅ map i j hij ⋙ map j k hjk ) 
-- ( map_comp_comp : Π (i j k l) (hij : i ≤ j) (hjk : j ≤ k) (hkl : k ≤ l),
--     map_comp  )

attribute [instance] ordinal_seq.linear_order ordinal_seq.cat ordinal_seq.full ordinal_seq.faithful

def totally_ordered_colimit (a : ordinal_seq) : Type* :=
Σ i : a.α, a.obj i

namespace totally_ordered_colimit

variables {a : ordinal_seq}

@[ext] protected structure hom (X Y : totally_ordered_colimit a) : Type :=
( le : X.1 ≤ Y.1 )
( hom : (a.map X.1 Y.1 le).obj X.2 ⟶ Y.2 )

protected def comp (X Y Z : totally_ordered_colimit a) (f : X.hom Y) (g : Y.hom Z) : X.hom Z :=
⟨le_trans f.1 g.1, 
  (a.map_comp X.1 Y.1 Z.1 f.1 g.1).hom.app _ ≫ ((a.map _ _ g.1).map f.2 ≫ g.2)⟩

instance : category_struct (totally_ordered_colimit a) :=
{ hom := totally_ordered_colimit.hom,
  id := λ X, ⟨le_refl _, (a.map_id X.1).hom.app _⟩,
  comp := totally_ordered_colimit.comp }

lemma comp_def {X Y Z : totally_ordered_colimit a} (f : X ⟶ Y) (g : Y ⟶ Z) : 
  f ≫ g = X.comp Y Z f g := rfl

lemma id_def (X : totally_ordered_colimit a) : 
  𝟙 X = ⟨le_refl _, (a.map_id X.1).hom.app _⟩ := rfl

instance : category (totally_ordered_colimit a) :=
{ comp_id' := begin 
    intros,
    simp [comp_def, totally_ordered_colimit.comp, id_def],
    ext,
    simp,
    admit
  end,
  id_comp' := begin 
    intros,
    simp [comp_def, totally_ordered_colimit.comp, id_def],
    ext,
    simp,
    admit
  end,
  assoc' := begin
    intros W X Y Z f g h,
    simp [comp_def, totally_ordered_colimit.comp, id_def], 
    ext,
    simp,
    admit
  end }

def UMP

-- def orthogonal {𝒞 : Type u₁} [category.{v₁} 𝒞] {𝒟 : Type u₂} [category.{v₂} 𝒟]
--   (D : 𝒟 ⥤ 𝒞) (c : cone D) (X : 𝒞) : Type* :=
-- Π d : (const 𝒟).obj X ⟶ D, 
--     { f : X ⟶ c.X // ∀ (A : 𝒟), f ≫ c.π.app A = nat_trans.app d A ∧ 
--       ∀ g : X ⟶ c.X, (∀ (A : 𝒟), f ≫ c.π.app A = nat_trans.app d A) → f = g }

-- def fixing_cocompletion {ι : Type} (D : ι → Type)
--   [Π i, category.{0} (D i)] (F : Π i, D i ⥤ 𝒞) : Type* := 
--   Σ X : 𝒞ᵒᵖ ⥤ Type, ∀ (i : ι) (c : limit_cone (F i)),
--     orthogonal (F i ⋙ (@yoneda 𝒞 _)) ((cones.functoriality (F i) yoneda).obj c.cone) X

-- namespace fixing_cocompletion

-- variables {ι : Type} (D : ι → Type)
--   [Π i, category.{0} (D i)] (F : Π i, D i ⥤ 𝒞)

-- instance : category_struct (fixing_cocompletion D F) :=
-- { hom := λ X Y, X.1 ⟶ Y.1,
--   id := λ X, 𝟙 X.fst,
--   comp := λ X Y Z f g, f ≫ g }

-- instance : category (fixing_cocompletion D F) := {}

-- def of_cat : 𝒞 ⥤ fixing_cocompletion D F :=
-- { obj := λ X, ⟨yoneda.obj X, λ i c d, sorry⟩,
--   map := λ X Y f, yoneda.map f }

-- def preserves_limit

end totally_ordered_colimit
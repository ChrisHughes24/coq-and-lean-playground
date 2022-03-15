import category_theory.adjunction.basic
import category_theory.limits.preserves.basic

open category_theory category_theory.functor category_theory.limits

variables (𝒞 : Type) [category.{0} 𝒞]

inductive bicompletion_aux : bool → Type 1
| of_cat_obj : 𝒞 → bicompletion_aux ff
| of_cat_hom : Π {X Y : 𝒞}, (X ⟶ Y) → bicompletion_aux tt -- of_cat_obj X ⟶ of_cat_obj Y
| limit_obj {𝒟 : Type} [category.{0} 𝒟] (F_obj : 𝒟 → bicompletion_aux ff) 
  (F_hom : Π {X Y : 𝒟}, (X ⟶ Y) → bicompletion_aux tt) : bicompletion_aux ff
| limit_cone {𝒟 : Type} [category.{0} 𝒟] (F_obj : 𝒟 → bicompletion_aux ff) 
  (F_hom : Π {X Y : 𝒟}, (X ⟶ Y) → bicompletion_aux tt) 
  (X : 𝒟) : bicompletion_aux tt -- limit_obj F_obj F_hom ⟶ F_obj X
| limit_is_limit {𝒟 : Type} [category.{0} 𝒟] (F_obj : 𝒟 → bicompletion_aux ff) 
  (F_hom : Π {X Y : 𝒟}, (X ⟶ Y) → bicompletion_aux tt) 
  (cone_obj : bicompletion_aux ff)
  (cone : Π {X : 𝒟}, bicompletion_aux tt) : -- cone_obj ⟶ F_obj X
  bicompletion_aux tt -- cone_obj → limit_obj F_obj F_hom
| colimit_obj {𝒟 : Type} [category.{0} 𝒟] (F_obj : 𝒟 → bicompletion_aux ff) 
  (F_hom : Π {X Y : 𝒟}, (X ⟶ Y) → bicompletion_aux tt) : bicompletion_aux ff
| colimit_cocone {𝒟 : Type} [category.{0} 𝒟] (F_obj : 𝒟 → bicompletion_aux ff) 
  (F_hom : Π {X Y : 𝒟}, (X ⟶ Y) → bicompletion_aux tt) 
  (X : 𝒟) : bicompletion_aux tt -- F_obj X ⟶ colimit_obj F_obj F_hom
| colimit_is_colimit {𝒟 : Type} [category.{0} 𝒟] (F_obj : 𝒟 → bicompletion_aux ff) 
  (F_hom : Π {X Y : 𝒟}, (X ⟶ Y) → bicompletion_aux tt) 
  (cocone_obj : bicompletion_aux ff)
  (cocone : Π {X : 𝒟}, bicompletion_aux tt) : -- F_obj X ⟶ cocone_obj
  bicompletion_aux tt -- colimit_obj F_obj F_hom ⟶ cocone_obj

def bicompletion_is_valid : Π (b : bool), bicompletion_aux 𝒞 b ⊕ (bicompletion_aux 𝒞 b × bicompletion_aux 𝒞 b) → Prop
| 

include 𝒞

constant bicompletion_aux : Type 1

namespace bicompletion_aux

constant category : category (bicompletion_aux 𝒞)

omit 𝒞
variable {𝒞}

def extend {}

-- def bicompletion_aux : Type 2 :=
-- Σ (O : Π (𝒟 : Type 1) [category.{0} 𝒟], 
--     by exactI Π [has_limits.{0} 𝒟] [has_colimits.{0} 𝒟] (F : 𝒞 ⥤ 𝒟), 𝒟),
--   ∀ (𝒟 ℰ : Type 1) [category.{0} 𝒟] [category.{0} ℰ], 
--     by exactI ∀ [has_limits 𝒟] [has_colimits 𝒟]
--       [has_limits ℰ] 
--       [has_colimits ℰ]
--       (F : 𝒞 ⥤ 𝒟) (G : 𝒞 ⥤ ℰ) (H : 𝒟 ⥤ ℰ)
--       [preserves_limits.{0} H]
--       [preserves_colimits.{0} H]
--       (hcomm : F ⋙ H ≅ G), 
--       by exactI H.obj (O 𝒟 F) ≅ O ℰ G

-- def hom (X Y : bicompletion_aux 𝒞) : Type 2 :=
-- Σ (f : Π (𝒟 : Type 1) [category.{0} 𝒟], 
--     by exactI Π [has_limits 𝒟] [has_colimits 𝒟] (F : 𝒞 ⥤ 𝒟),
--     by exactI X.1 𝒟 F ⟶ Y.1 𝒟 F),
--   ∀ (𝒟 ℰ : Type 1) [category.{0} 𝒟] [category.{0} ℰ], 
--     by exactI ∀ [has_limits 𝒟] [has_colimits 𝒟]
--       [has_limits ℰ] 
--       [has_colimits ℰ] 
--       (F : 𝒞 ⥤ 𝒟) (G : 𝒞 ⥤ ℰ) (H : 𝒟 ⥤ ℰ) 
--       [preserves_limits.{0} H]
--       [preserves_colimits.{0} H]
--       (hcomm : F ⋙ H ≅ G),
--     begin resetI,
--       have := X.2 𝒟 ℰ F G H hcomm,
--       have := H.map (f 𝒟 F),
--       have := f ℰ G, end
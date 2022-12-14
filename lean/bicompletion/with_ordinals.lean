import category_theory.limits.preserves.basic
import set_theory.ordinal

open category_theory category_theory.limits category_theory.functor

universes vā vā uā uā 

structure colimit (š : Type 1) [category.{0} š] : Type 1 :=
( diag : Type )
[ category : category.{0} diag ]
( F : diag ā„¤ š )
( colimit_cocone : colimit_cocone F )

attribute [instance] colimit.category

constant fixing_cocompletion {š : Type 1} [category.{0} š] {Ī¹ : Type 1} (colimits : Ī¹ ā colimit š) : Type 1

namespace fixing_cocompletion

variables {š : Type 1} [category.{0} š] {Ī¹ : Type 1} (colimits : Ī¹ ā colimit š) 

@[instance] protected constant category : category.{0} (fixing_cocompletion colimits)

@[instance] protected constant has_colimits : has_colimits_of_size.{0 0} (fixing_cocompletion colimits)

constant of_cat : š ā„¤ fixing_cocompletion colimits

constant of_cat_preserves : Ī  i : Ī¹, preserves_colimit (colimits i).F (of_cat colimits)

variable {colimits}

constant extend {š : Type 1} [category.{0} š] (F : š ā„¤ š)
  (hF : Ī  i : Ī¹, preserves_colimit (colimits i).F F) : fixing_cocompletion colimits ā„¤ š

constant extend_preserves {š : Type 1} [category.{0} š] (F : š ā„¤ š)
  (hF : Ī  i : Ī¹, preserves_colimit (colimits i).F F) :
  preserves_colimits.{0 0} (extend F hF) 

constant of_cat_extend {š : Type 1} [category.{0} š] (F : š ā„¤ š)
  (hF : Ī  i : Ī¹, preserves_colimit (colimits i).F F) :
  of_cat colimits ā extend F hF ā F 

constant extend_unique {š : Type 1} [category.{0} š] (F : š ā„¤ š)
  (hF : Ī  i : Ī¹, preserves_colimit (colimits i).F F)
  (G : fixing_cocompletion colimits ā„¤ š)
  (hG : preserves_colimits.{0 0} (extend F hF))
  (hG_commutes : of_cat colimits ā G ā F) :
  G ā extend F hF

end fixing_cocompletion

structure limit (š : Type 1) [category.{0} š] : Type 1 :=
( diag : Type )
[ category : category.{0} diag ]
( F : diag ā„¤ š )
( limit_cone : limit_cone F )

attribute [instance] limit.category

constant fixing_completion {š : Type 1} [category.{0} š] {Ī¹ : Type 1} (limits : Ī¹ ā limit š) : Type 1

namespace fixing_completion

variables {š : Type 1} [category.{0} š] {Ī¹ : Type 1} (limits : Ī¹ ā limit š) 

@[instance] protected constant category : category.{0} (fixing_completion limits)

@[instance] protected constant has_limits : has_limits_of_size.{0 0} (fixing_completion limits)

constant of_cat : š ā„¤ fixing_completion limits

constant of_cat_preserves : Ī  i : Ī¹, preserves_limit (limits i).F (of_cat limits)

variable {limits}

constant extend {š : Type 1} [category.{0} š] (F : š ā„¤ š)
  (hF : Ī  i : Ī¹, preserves_limit (limits i).F F) : fixing_completion limits ā„¤ š

constant extend_preserves {š : Type 1} [category.{0} š] (F : š ā„¤ š)
  (hF : Ī  i : Ī¹, preserves_limit (limits i).F F) :
  preserves_colimits.{0 0} (extend F hF) 

constant of_cat_extend {š : Type 1} [category.{0} š] (F : š ā„¤ š)
  (hF : Ī  i : Ī¹, preserves_limit (limits i).F F) :
  of_cat limits ā extend F hF ā F 

constant extend_unique {š : Type 1} [category.{0} š] (F : š ā„¤ š)
  (hF : Ī  i : Ī¹, preserves_limit (limits i).F F)
  (G : fixing_completion limits ā„¤ š)
  (hG : preserves_colimits.{0 0} (extend F hF))
  (hG_commutes : of_cat limits ā G ā F) :
  G ā extend F hF

end fixing_completion

namespace totally_ordered_colimit

structure ordinal_seq : Type 2 :=
( Ī± : Type )
[ linear_order : linear_order Ī± ]
( obj : Ī  i : Ī±, Type 1 )
[ cat : Ī  i, category.{0} (obj i) ]
( map : Ī  i j : Ī±, i ā¤ j ā (obj i ā„¤ obj j) )
[ full : Ī  (i j : Ī±) (hij : i ā¤ j), full (map i j hij) ]
[ faithful : Ī  (i j : Ī±) (hij : i ā¤ j), faithful (map i j hij) ]
( map_id : Ī  i, map i i le_rfl ā š­ (obj i) )
( map_comp : Ī  i j k (hij : i ā¤ j) (hjk : j ā¤ k), 
    map i k (le_trans hij hjk) ā map i j hij ā map j k hjk ) 
-- ( map_comp_comp : Ī  (i j k l) (hij : i ā¤ j) (hjk : j ā¤ k) (hkl : k ā¤ l),
--     map_comp  )

attribute [instance] ordinal_seq.linear_order ordinal_seq.cat ordinal_seq.full ordinal_seq.faithful

def totally_ordered_colimit (a : ordinal_seq) : Type* :=
Ī£ i : a.Ī±, a.obj i

namespace totally_ordered_colimit

variables {a : ordinal_seq}

@[ext] protected structure hom (X Y : totally_ordered_colimit a) : Type :=
( le : X.1 ā¤ Y.1 )
( hom : (a.map X.1 Y.1 le).obj X.2 ā¶ Y.2 )

protected def comp (X Y Z : totally_ordered_colimit a) (f : X.hom Y) (g : Y.hom Z) : X.hom Z :=
āØle_trans f.1 g.1, 
  (a.map_comp X.1 Y.1 Z.1 f.1 g.1).hom.app _ ā« ((a.map _ _ g.1).map f.2 ā« g.2)ā©

instance : category_struct (totally_ordered_colimit a) :=
{ hom := totally_ordered_colimit.hom,
  id := Ī» X, āØle_refl _, (a.map_id X.1).hom.app _ā©,
  comp := totally_ordered_colimit.comp }

lemma comp_def {X Y Z : totally_ordered_colimit a} (f : X ā¶ Y) (g : Y ā¶ Z) : 
  f ā« g = X.comp Y Z f g := rfl

lemma id_def (X : totally_ordered_colimit a) : 
  š X = āØle_refl _, (a.map_id X.1).hom.app _ā© := rfl

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

-- def orthogonal {š : Type uā} [category.{vā} š] {š : Type uā} [category.{vā} š]
--   (D : š ā„¤ š) (c : cone D) (X : š) : Type* :=
-- Ī  d : (const š).obj X ā¶ D, 
--     { f : X ā¶ c.X // ā (A : š), f ā« c.Ļ.app A = nat_trans.app d A ā§ 
--       ā g : X ā¶ c.X, (ā (A : š), f ā« c.Ļ.app A = nat_trans.app d A) ā f = g }

-- def fixing_cocompletion {Ī¹ : Type} (D : Ī¹ ā Type)
--   [Ī  i, category.{0} (D i)] (F : Ī  i, D i ā„¤ š) : Type* := 
--   Ī£ X : šįµįµ ā„¤ Type, ā (i : Ī¹) (c : limit_cone (F i)),
--     orthogonal (F i ā (@yoneda š _)) ((cones.functoriality (F i) yoneda).obj c.cone) X

-- namespace fixing_cocompletion

-- variables {Ī¹ : Type} (D : Ī¹ ā Type)
--   [Ī  i, category.{0} (D i)] (F : Ī  i, D i ā„¤ š)

-- instance : category_struct (fixing_cocompletion D F) :=
-- { hom := Ī» X Y, X.1 ā¶ Y.1,
--   id := Ī» X, š X.fst,
--   comp := Ī» X Y Z f g, f ā« g }

-- instance : category (fixing_cocompletion D F) := {}

-- def of_cat : š ā„¤ fixing_cocompletion D F :=
-- { obj := Ī» X, āØyoneda.obj X, Ī» i c d, sorryā©,
--   map := Ī» X Y f, yoneda.map f }

-- def preserves_limit

end totally_ordered_colimit
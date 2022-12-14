import category_theory.limits.preserves.basic

open category_theory category_theory.limits

variables (š : Type) [category.{0} š]

@[protect_proj] structure thing' : Type 1 :=
(š : Type)
[š_cat : category.{0} š]
(of_cat : š ā„¤ š)
(full : full of_cat)
(faithful : faithful of_cat)
(rel : š ā š ā Prop)
(well_founded_rel : well_founded rel)
-- (comp_rel : ā {X Y Z A B : š} (i : A ā¶ B) (f : X ā¶ Y) (g : Y ā¶ Z),
--   rel āØX, Y, fā© āØA, B, iā© ā rel āØY, Z, gā© āØA, B, iā© ā 
--   rel āØX, Z, f ā« gā© āØA, B, iā©)

attribute [instance] thing'.š_cat

variable {š}

-- def smaller {š : thing' š} {X Y : š.š} (f : X ā¶ Y) : Type :=
-- { A : š.š // š.rel āØA, A, š Aā© āØX, Y, fā© }

def smaller {š : thing' š} (X : š.š) : Type :=
{ A : š.š // š.rel A X }

-- instance (š : thing' š) {X Y : š.š} (f : X ā¶ Y) : 
--   category_struct (smaller f) :=
-- { hom := Ī» A B, { g : A.1 ā¶ B.1 // š.rel āØA.1, B.1, gā© āØX, Y, fā© },
--   id := Ī» A, āØš A.1, A.2ā©,
--   comp := Ī» A B C i j, āØi.1 ā« j.1, š.comp_rel _ _ j.1 i.2 j.2ā© }

variables {š : thing' š}

instance (š : thing' š) (X : š.š) : category_struct (smaller X) :=
{ hom := Ī» A B, A.1 ā¶ B.1,
  id := Ī» A, š A.1,
  comp := Ī» A B C i j, i ā« j }

instance (š : thing' š) (X : š.š) : category (smaller X) := 
{ id_comp' := Ī» X Y f, @category.id_comp š.š _ _ _ f,
  comp_id' := Ī» X Y f, @category.comp_id š.š _ _ _ f,
  assoc' := Ī» W X Y Z f g h, @category.assoc š.š _ _ _ _ _ f g h }

def of_smaller {š : thing' š} (X : š.š) : 


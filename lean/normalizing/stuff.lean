import category_theory.limits.presheaf

open category_theory


@[protect_proj] structure system : Type 1 :=
(A B C D : Type)
[category_A : category.{0} A]
[category_B : category.{0} B]
[category_C : category.{0} C]
[category_D : category.{0} D]
(AB : A ⥤ B) (BC : B ⥤ C)
(BD : B ⥤ D) (DC : D ⥤ C)
[full : full (AB ⋙ BD)] 

attribute [instance] system.category_A system.category_B 
                     system.category_C system.category_D
                     system.full --system.faithful

namespace system

variables (S : system)

def correct : Prop :=
∀ (X Y : S.A) (f : S.AB.obj X ⟶ S.AB.obj Y),
  (S.AB ⋙ S.BC).map ((S.AB ⋙ S.BD).preimage (S.BD.map f)) = S.BC.map f

variables {S}

lemma correct_of_forall_eq 
  (h : ∀ (X Y : S.A) (f g : S.AB.obj X ⟶ S.AB.obj Y), 
    (S.BD ⋙ S.DC).map f = (S.BD ⋙ S.DC).map g → S.BC.map f = S.BC.map g) : 
  correct S :=
begin
  intros X Y f,
  rw [functor.comp_map],
  apply h,
  rw [← functor.comp_map, ← nat_iso.cancel_nat_iso_hom_left (S.AB.associator S.BD S.DC),
    ← (S.AB.associator S.BD S.DC).hom.naturality, functor.comp_map, functor.image_preimage],
  simp only [functor.associator_hom_app, category.comp_id, functor.comp_map, category.id_comp],
end

lemma forall_eq_of_correct (h : correct S) [faithful S.DC] :
  ∀ (X Y : S.A) (f g : S.AB.obj X ⟶ S.AB.obj Y), 
    (S.BD ⋙ S.DC).map f = (S.BD ⋙ S.DC).map g → S.BC.map f = S.BC.map g :=
begin
  intros X Y f g hfg,
  dsimp [correct] at h, 
  rw [← h, ← h _ _ g, S.DC.map_injective hfg]
end

-- Could be replaced with i : S.BD ⋙ S.DC ⟶ S.BC such that
-- it is always epic
lemma correct_of_iso (i : S.BC ≅ S.BD ⋙ S.DC) : correct S :=
correct_of_forall_eq (λ X Y f g h, 
  by rw [← nat_iso.cancel_nat_iso_inv_left i, ← i.inv.naturality, h, i.inv.naturality])

end system

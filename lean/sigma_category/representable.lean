import tactic
import category_theory.yoneda
import .sigma_category

open category_theory category_theory.functor

universes u v w

instance {𝒞 : Type u} [category 𝒞] (F : 𝒞 ⥤ Type v) : category_struct (sigma F.obj) :=
{ hom := λ X Y, { f : X.1 ⟶ Y.1 // F.map f X.2 = Y.2 },
  id := λ X, ⟨𝟙 X.1, by simp⟩,
  comp := λ X Y Z f g, ⟨f.1 ≫ g.1, by have := f.2; have := g.2; simp * at *⟩ }

instance {𝒞 : Type u} [category 𝒞] (F : 𝒞 ⥤ Type v) : category (sigma F.obj) :=
{ id_comp' := λ _ _ _, subtype.ext (category.id_comp _),
  comp_id' := λ _ _ _, subtype.ext (category.comp_id _),
  assoc' := λ _ _ _ _ _ _ _, subtype.ext (category.assoc _ _ _) }

def sigma.forget {𝒞 : Type u} [category 𝒞] (F : 𝒞 ⥤ Type v) : sigma F.obj ⥤ 𝒞 :=
{ obj := sigma.fst,
  map := λ _ _, subtype.val }

example {𝒞 : Type u} [category 𝒞] (X : 𝒞) :
  limits.is_initial (@sigma.mk 𝒞 (coyoneda.obj (opposite.op X)).obj X (𝟙 X)) :=
@limits.is_initial.of_unique _ _ (@sigma.mk 𝒞 (coyoneda.obj (opposite.op X)).obj X (𝟙 X)) 
  (λ Y, ⟨⟨⟨Y.2, category.id_comp Y.2⟩⟩, λ x, subtype.ext (begin
    have := x.2,
    dsimp at this,
    simp at this,
    simp [this]
  end)⟩)

noncomputable example {𝒞 : Type u} [category 𝒞] (F : 𝒞 ⥤ Type v) [corepresentable F] :
  limits.is_initial (@sigma.mk 𝒞 F.obj F.corepr_X F.corepr_x) :=
@limits.is_initial.of_unique _ _ (@sigma.mk 𝒞 F.obj F.corepr_X
    (F.corepr_w.hom.app F.corepr_X (𝟙 F.corepr_X)))
  (λ Y, ⟨⟨⟨((corepr_w F).app Y.fst).inv Y.snd, begin
    conv_rhs { rw [← (F.corepr_w.app Y.fst).to_equiv.apply_symm_apply Y.snd] },
    dsimp,
    generalize hy : F.corepr_w.inv.app Y.fst Y.snd = y,
    apply (F.corepr_w.app Y.fst).symm.to_equiv.injective,
    have := F.corepr_w.inv.naturality y,
    simp only [coyoneda, function.funext_iff] at this,
    dsimp at *,
    simp [this]
  end⟩⟩, λ x, subtype.ext begin
    have := x.2,
    dsimp at this,
    simp [← this],
    have := F.corepr_w.inv.naturality x.1,
    simp only [coyoneda, function.funext_iff] at this,
    dsimp at *,
    simp [this_1]
  end⟩)

example {𝒞 : Type u} [category 𝒞] (F : 𝒞 ⥤ Type v) 
  (X : sigma F.obj) (h : limits.is_initial X) :
  coyoneda.obj (opposite.op ((sigma.forget F).obj X)) ≅ F :=
{ hom := { app := λ Y f, F.map f X.2 },
  inv := { app := λ Y y, (h.to ⟨Y, y⟩).val,
     naturality' := λ Y Z f, begin
       dsimp,
       funext y,
       dsimp,
       let g : X ⟶ ⟨Z, F.map f y⟩ := h.to ⟨Y, y⟩ ≫ ⟨f, rfl⟩,
       show _ = g.val,
       refine congr_arg subtype.val _,
       exact limits.is_initial.hom_ext h (h.to ⟨Z, F.map f y⟩) g,
     end },
  hom_inv_id' := begin
    dsimp,
    ext Y y,
    dsimp at *,
    let g : X ⟶ ⟨Y, F.map y X.snd⟩ := ⟨y, rfl⟩,
    show subtype.val (h.to ⟨Y, F.map y X.snd⟩) = ↑g,
    refine congr_arg subtype.val _,
    exact limits.is_initial.hom_ext h (h.to ⟨Y, F.map y X.snd⟩) g,
  end,
  inv_hom_id' := begin
    dsimp,
    ext Y y,
    exact (h.to ⟨Y, y⟩).2
  end  }
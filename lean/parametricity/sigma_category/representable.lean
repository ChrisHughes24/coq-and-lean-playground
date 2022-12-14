import tactic
import category_theory.yoneda
import .sigma_category

open category_theory category_theory.functor

universes u v w

instance {π : Type u} [category π] (F : π β₯€ Type v) : category_struct (sigma F.obj) :=
{ hom := Ξ» X Y, { f : X.1 βΆ Y.1 // F.map f X.2 = Y.2 },
  id := Ξ» X, β¨π X.1, by simpβ©,
  comp := Ξ» X Y Z f g, β¨f.1 β« g.1, by have := f.2; have := g.2; simp * at *β© }

instance {π : Type u} [category π] (F : π β₯€ Type v) : category (sigma F.obj) :=
{ id_comp' := Ξ» _ _ _, subtype.ext (category.id_comp _),
  comp_id' := Ξ» _ _ _, subtype.ext (category.comp_id _),
  assoc' := Ξ» _ _ _ _ _ _ _, subtype.ext (category.assoc _ _ _) }

def sigma.forget {π : Type u} [category π] (F : π β₯€ Type v) : sigma F.obj β₯€ π :=
{ obj := sigma.fst,
  map := Ξ» _ _, subtype.val }

example {π : Type u} [category π] (X : π) :
  limits.is_initial (@sigma.mk π (coyoneda.obj (opposite.op X)).obj X (π X)) :=
@limits.is_initial.of_unique _ _ (@sigma.mk π (coyoneda.obj (opposite.op X)).obj X (π X)) 
  (Ξ» Y, β¨β¨β¨Y.2, category.id_comp Y.2β©β©, Ξ» x, subtype.ext (begin
    have := x.2,
    dsimp at this,
    simp at this,
    simp [this]
  end)β©)

noncomputable example {π : Type u} [category π] (F : π β₯€ Type v) [corepresentable F] :
  limits.is_initial (@sigma.mk π F.obj F.corepr_X F.corepr_x) :=
@limits.is_initial.of_unique _ _ (@sigma.mk π F.obj F.corepr_X
    (F.corepr_w.hom.app F.corepr_X (π F.corepr_X)))
  (Ξ» Y, β¨β¨β¨((corepr_w F).app Y.fst).inv Y.snd, begin
    conv_rhs { rw [β (F.corepr_w.app Y.fst).to_equiv.apply_symm_apply Y.snd] },
    dsimp,
    generalize hy : F.corepr_w.inv.app Y.fst Y.snd = y,
    apply (F.corepr_w.app Y.fst).symm.to_equiv.injective,
    have := F.corepr_w.inv.naturality y,
    simp only [coyoneda, function.funext_iff] at this,
    dsimp at *,
    simp [this]
  endβ©β©, Ξ» x, subtype.ext begin
    have := x.2,
    dsimp at this,
    simp [β this],
    have := F.corepr_w.inv.naturality x.1,
    simp only [coyoneda, function.funext_iff] at this,
    dsimp at *,
    simp [this_1]
  endβ©)

example {π : Type u} [category π] (F : π β₯€ Type v) 
  (X : sigma F.obj) (h : limits.is_initial X) :
  coyoneda.obj (opposite.op ((sigma.forget F).obj X)) β F :=
{ hom := { app := Ξ» Y f, F.map f X.2 },
  inv := { app := Ξ» Y y, (h.to β¨Y, yβ©).val,
     naturality' := Ξ» Y Z f, begin
       dsimp,
       funext y,
       dsimp,
       let g : X βΆ β¨Z, F.map f yβ© := h.to β¨Y, yβ© β« β¨f, rflβ©,
       show _ = g.val,
       refine congr_arg subtype.val _,
       exact limits.is_initial.hom_ext h (h.to β¨Z, F.map f yβ©) g,
     end },
  hom_inv_id' := begin
    dsimp,
    ext Y y,
    dsimp at *,
    let g : X βΆ β¨Y, F.map y X.sndβ© := β¨y, rflβ©,
    show subtype.val (h.to β¨Y, F.map y X.sndβ©) = βg,
    refine congr_arg subtype.val _,
    exact limits.is_initial.hom_ext h (h.to β¨Y, F.map y X.sndβ©) g,
  end,
  inv_hom_id' := begin
    dsimp,
    ext Y y,
    exact (h.to β¨Y, yβ©).2
  end  }
import .presheaves

open category_theory

noncomputable theory

variables (C : Type) [category.{0} C]

inductive prod_coprod : Type
| of_cat' : C → prod_coprod
| prod : prod_coprod → prod_coprod → prod_coprod
| coprod : prod_coprod → prod_coprod → prod_coprod

variable {C}

namespace prod_coprod

inductive norm_hom : bool → Π (X Y : prod_coprod C), Type
| of_cat_ff {X Y : C} : (X ⟶ Y) → norm_hom ff (of_cat' X) (of_cat' Y)
| prod_mk_ff {X Y Z : prod_coprod C} : norm_hom tt X Y → norm_hom tt X Z → norm_hom ff X (Y.prod Z)
| fst_ff {X Y : prod_coprod C} : norm_hom ff (X.prod Y) X
| snd_ff {X Y : prod_coprod C} : norm_hom ff (X.prod Y) Y
| coprod_mk_ff {X Y Z : prod_coprod C} : norm_hom tt X Z → norm_hom tt Y Z → norm_hom ff (X.coprod Y) Z
| inl_ff {X Y : prod_coprod C} : norm_hom ff X (X.coprod Y)
| inr_ff {X Y : prod_coprod C} : norm_hom ff Y (X.coprod Y)
| id (X : prod_coprod C) : norm_hom tt X X
| comp_ff {X Y Z : prod_coprod C} : norm_hom tt X Y → norm_hom ff Y Z → norm_hom tt X Z

namespace norm_hom

@[simp] def of_ff {X Y : prod_coprod C} (f : norm_hom ff X Y) : norm_hom tt X Y :=
norm_hom.comp_ff (norm_hom.id _) f

def of_cat {X Y : C} (f : X ⟶ Y) : norm_hom tt (of_cat' X) (of_cat' Y) :=
of_ff (norm_hom.of_cat_ff f)

def prod_mk {X Y Z : prod_coprod C} (f : norm_hom tt X Y) (g : norm_hom tt X Z) : norm_hom tt X (Y.prod Z) :=
of_ff (norm_hom.prod_mk_ff f g)

def fst {X Y : prod_coprod C} : norm_hom tt (X.prod Y) X :=
of_ff norm_hom.fst_ff

def snd {X Y : prod_coprod C} : norm_hom tt (X.prod Y) Y :=
of_ff norm_hom.snd_ff

def coprod_mk {X Y Z : prod_coprod C} (f : norm_hom tt X Z) (g : norm_hom tt Y Z) : norm_hom tt (X.coprod Y) Z :=
of_ff (norm_hom.coprod_mk_ff f g)

def inl {X Y : prod_coprod C} : norm_hom tt X (X.coprod Y) :=
of_ff norm_hom.inl_ff

def inr {X Y : prod_coprod C} : norm_hom tt Y (X.coprod Y) :=
of_ff norm_hom.inr_ff

@[elab_as_eliminator] def rec_on_tt {motive : ∀ X Y : prod_coprod C, norm_hom tt X Y → Sort*}
  {X Y : prod_coprod C} (f : norm_hom tt X Y)
  (h₁ : ∀ X, motive X X (norm_hom.id X))
  (h₂ : ∀ X Y Z (f : norm_hom tt X Y) (g : norm_hom ff Y Z), motive X Y f →
    motive X Z (f.comp_ff g)) :
  motive X Y f :=
have ∀ (b : bool) (f : norm_hom b X Y) (h : b = tt), motive X Y (eq.rec_on h f),
  from λ b f, begin
    induction f; try {dsimp; intros; contradiction},
    { intros, apply h₁ },
    { intros h, apply h₂,
      tauto }
  end,
this tt f rfl

@[simp] lemma norm_hom.rec_on_tt_id  {motive : ∀ X Y : prod_coprod C, norm_hom tt X Y → Sort*}
  {X : prod_coprod C}
  (h₁ : ∀ X, motive X X (norm_hom.id X))
  (h₂ : ∀ X Y Z (f : norm_hom tt X Y) (g : norm_hom ff Y Z), motive X Y f →
    motive X Z (f.comp_ff g)) :
  @norm_hom.rec_on_tt C _ motive X X (norm_hom.id X) h₁ h₂ = h₁ X := rfl

@[simp] lemma norm_hom.rec_on_tt_comp_ff {motive : ∀ X Y : prod_coprod C, norm_hom tt X Y → Sort*}
  {X Y Z : prod_coprod C} (f : norm_hom tt X Y) (g : norm_hom ff Y Z)
  (h₁ : ∀ X, motive X X (norm_hom.id X))
  (h₂ : ∀ X Y Z (f : norm_hom tt X Y) (g : norm_hom ff Y Z), motive X Y f →
    motive X Z (f.comp_ff g)) :
  @norm_hom.rec_on_tt C _ motive X Z (norm_hom.comp_ff f g) h₁ h₂ = h₂ X Y Z f g
    (@norm_hom.rec_on_tt C _ motive X Y f h₁ h₂) := rfl

def comp {X Y Z : prod_coprod C} (f : norm_hom tt X Y) (g : norm_hom tt Y Z) : norm_hom tt X Z :=
norm_hom.rec_on_tt g (λ _ f, f) (λ _ _ _ f f ih g, norm_hom.comp_ff (ih g) f) f

lemma comp_id {X Y : prod_coprod C} (f : norm_hom tt X Y) : f.comp (norm_hom.id _) = f := rfl

lemma id_comp {X Y : prod_coprod C} (f : norm_hom tt X Y) : (norm_hom.id X).comp f = f :=
norm_hom.rec_on_tt f (by intros; simp [comp]; refl) (by intros; simp [comp, *] at *)

lemma comp_comp_ff {W X Y Z : prod_coprod C} (f : norm_hom tt W X) (g : norm_hom tt X Y) (h : norm_hom ff Y Z) :
  f.comp (g.comp_ff h) = (f.comp g).comp_ff h := rfl

lemma comp_assoc {W X Y Z : prod_coprod C} (f : norm_hom tt W X) (g : norm_hom tt X Y) (h : norm_hom tt Y Z) :
  (f.comp g).comp h = f.comp (g.comp h) :=
begin
  revert f g,
  refine norm_hom.rec_on_tt h _ _,
  { intros, refl },
  { intros,
    simp [comp_comp_ff, *] at * }
end

inductive rel : Π {b₁ b₂ : bool} {X Y : prod_coprod C}, norm_hom b₁ X Y → norm_hom b₂ X Y → Prop
| refl {b : bool} {X Y : prod_coprod C} (f : norm_hom b X Y) : rel f f
| symm {b₁ b₂ : bool} {X Y : prod_coprod C} {f : norm_hom b₁ X Y} {g : norm_hom b₂ X Y} : rel f g → rel g f
| trans {b₁ b₂ b₃ : bool} {X Y : prod_coprod C} {f : norm_hom b₁ X Y} {g : norm_hom b₂ X Y} {h : norm_hom b₃ X Y} :
  rel f g → rel g h → rel f h
| comp_ff_congr {X Y Z : prod_coprod C} {f₁ f₂ : norm_hom tt X Y} {g₁ g₂ : norm_hom ff Y Z} :
  rel f₁ f₂ → rel g₁ g₂ → rel (f₁.comp_ff g₁) (f₂.comp_ff g₂)
| prod_mk_ff_congr {X Y Z : prod_coprod C} {f₁ f₂ : norm_hom tt X Y} {g₁ g₂ : norm_hom tt X Z} :
  rel f₁ f₂ → rel g₁ g₂ → rel (f₁.prod_mk_ff g₁) (f₂.prod_mk_ff g₂)
| coprod_mk_ff_congr {X Y Z : prod_coprod C} {f₁ f₂ : norm_hom tt X Z} {g₁ g₂ : norm_hom tt Y Z} :
  rel f₁ f₂ → rel g₁ g₂ → rel (f₁.coprod_mk_ff g₁) (f₂.coprod_mk_ff g₂)
| of_cat_id {X : C} : rel (norm_hom.of_cat (𝟙 X)) (norm_hom.id (of_cat' X))
| of_cat_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
  rel (norm_hom.of_cat (f ≫ g)) (norm_hom.comp (norm_hom.of_cat f) (norm_hom.of_cat g))
| mk_comp_fst {X Y Z : prod_coprod C} (f : norm_hom tt X Y) (g : norm_hom tt X Z) :
  rel (norm_hom.comp (norm_hom.prod_mk f g) norm_hom.fst) f
| mk_comp_snd {X Y Z : prod_coprod C} (f : norm_hom tt X Y) (g : norm_hom tt X Z) :
  rel (norm_hom.comp (norm_hom.prod_mk f g) norm_hom.snd) g
| prod_eta {X Y Z : prod_coprod C} (f : norm_hom tt X (Y.prod Z)) :
  rel (norm_hom.prod_mk (f.comp norm_hom.fst) (f.comp norm_hom.snd)) f
| inl_comp_mk {X Y Z : prod_coprod C} (f : norm_hom tt X Z) (g : norm_hom tt Y Z) :
  rel (norm_hom.comp norm_hom.inl (norm_hom.coprod_mk f g)) f
| inr_comp_mk {X Y Z : prod_coprod C} (f : norm_hom tt X Z) (g : norm_hom tt Y Z) :
  rel (norm_hom.comp norm_hom.inr (norm_hom.coprod_mk f g)) g
| coprod_eta {X Y Z : prod_coprod C} (f : norm_hom tt (X.coprod Y) Z) :
  rel (norm_hom.coprod_mk (norm_hom.inl.comp f) (norm_hom.inr.comp f)) f

attribute [refl] rel.refl
attribute [symm] rel.symm
attribute [trans] rel.trans

infixl ` ♥ `: 50 := rel

lemma rel_prod {X Y Z : prod_coprod C} {f g : norm_hom tt X (Y.prod Z)}
  (h₁ : rel (f.comp norm_hom.fst) (g.comp norm_hom.fst))
  (h₂ : rel (f.comp norm_hom.snd) (g.comp norm_hom.snd)) :
  rel f g :=
calc f ♥ norm_hom.prod_mk (f.comp norm_hom.fst) (f.comp norm_hom.snd) : rel.symm (rel.prod_eta f)
   ... ♥ norm_hom.prod_mk (g.comp norm_hom.fst) (g.comp norm_hom.snd) : rel.prod_mk_congr h₁ h₂
   ... ♥ g : rel.prod_eta g

lemma rel_coprod {X Y Z : prod_coprod C} {f g : norm_hom tt (X.coprod Y) Z}
  (h₁ : rel (norm_hom.inl.comp f) (norm_hom.inl.comp g))
  (h₂ : rel (norm_hom.inr.comp f) (norm_hom.inr.comp g)) :
  rel f g :=
calc f ♥ norm_hom.coprod_mk (norm_hom.inl.comp f) (norm_hom.inr.comp f) : rel.symm (rel.coprod_eta f)
   ... ♥ norm_hom.coprod_mk (norm_hom.inl.comp g) (norm_hom.inr.comp g) : rel.coprod_mk_congr h₁ h₂
   ... ♥ g : rel.coprod_eta g

instance rel_setoid (X Y : prod_coprod C) : setoid (norm_hom tt X Y) :=
{ r := rel,
  iseqv := ⟨rel.refl, λ _ _, rel.symm, λ _ _ _, rel.trans⟩ }

end norm_hom

section norm_hom

open norm_hom

def hom (X Y : prod_coprod C) : Type := quotient (norm_hom.rel_setoid X Y)

instance : category_struct (prod_coprod C) :=
{ hom := hom,
  id := λ X, quotient.mk' (norm_hom.id X),
  comp := λ X Y Z f g, quotient.lift_on₂ f g (λ f g, quotient.mk' (norm_hom.comp f g))
    (λ f₁ g₁ f₂ g₂ hf hg, quotient.sound (rel.comp_congr hf hg)) }

instance : category (prod_coprod C) :=
{ id_comp' := λ X Y f, quotient.induction_on f (λ f, congr_arg quotient.mk (id_comp _)),
  comp_id' := λ X Y f, quotient.induction_on f (λ f, congr_arg quotient.mk (comp_id _)),
  assoc' := λ W X Y Z f g h, quotient.induction_on₃ f g h
    (λ f g h, congr_arg quotient.mk (comp_assoc _ _ _)) }

def of_cat : C ⥤ prod_coprod C :=
{ obj := λ X, of_cat' X,
  map := λ X Y f, ⟦norm_hom.of_cat f⟧,
  map_id' := λ X, quotient.sound rel.of_cat_id,
  map_comp' := λ X Y Z f g, quotient.sound (rel.of_cat_comp f g) }

def to_presheaf_obj (X : prod_coprod C) : (Cᵒᵖ ⥤ Type) :=
prod_coprod.rec_on X
  yoneda.obj
  (λ X Y ih₁ ih₂, Pprod ih₁ ih₂)
  (λ X Y ih₁ ih₂, Pcoprod ih₁ ih₂)

@[simp] lemma to_presheaf_obj_of_cat (X Y : C) : to_presheaf_obj (of_cat' X) = yoneda.obj X := rfl
@[simp] lemma to_presheaf_obj_prod (X Y : prod_coprod C) : to_presheaf_obj (prod X Y) =
  Pprod (to_presheaf_obj X) (to_presheaf_obj Y) := rfl
@[simp] lemma to_presheaf_obj_coprod (X Y : prod_coprod C) : to_presheaf_obj (coprod X Y) =
  Pcoprod (to_presheaf_obj X) (to_presheaf_obj Y) := rfl

@[simp] def to_presheaf_norm_hom : Π {b : bool} {X Y : prod_coprod C}, norm_hom b X Y →
  ((to_presheaf_obj X) ⟶ (to_presheaf_obj Y))
| _ _ _ (norm_hom.of_cat_ff f) := yoneda.map f
| _ _ _ (norm_hom.prod_mk_ff f g) := Pprod_lift (to_presheaf_norm_hom f) (to_presheaf_norm_hom g)
| _ _ _ (norm_hom.fst_ff) := Pprod_fst
| _ _ _ (norm_hom.snd_ff) := Pprod_snd
| _ _ _ (norm_hom.coprod_mk_ff f g) := Pcoprod_lift (to_presheaf_norm_hom f) (to_presheaf_norm_hom g)
| _ _ _ (norm_hom.inl_ff) := Pcoprod_inl
| _ _ _ (norm_hom.inr_ff) := Pcoprod_inr
| _ _ _ (norm_hom.id X) := 𝟙 _
| _ _ _ (norm_hom.comp_ff f g) := to_presheaf_norm_hom f ≫ to_presheaf_norm_hom g

lemma to_presheaf_norm_hom_comp {X Y Z : prod_coprod C} (f : norm_hom tt X Y) (g : norm_hom tt Y Z) :
  to_presheaf_norm_hom (f.comp g) = to_presheaf_norm_hom f ≫ to_presheaf_norm_hom g :=
norm_hom.rec_on_tt g (by intros; simp [norm_hom.comp]) (by intros; simp [norm_hom.comp_comp_ff, *]) f

lemma to_presheaf_norm_hom_rel {X Y : prod_coprod C} (f g : norm_hom tt X Y) (h : rel f g) :
  to_presheaf_norm_hom f = to_presheaf_norm_hom g :=
begin
  induction h,
  { refl },
  { symmetry, assumption },
  { transitivity, assumption, assumption },
  { simp [*, to_presheaf_norm_hom_comp] },
  { simp [*, norm_hom.prod_mk] },
  { simp [*, norm_hom.coprod_mk] },
  { simp [norm_hom.of_cat], refl },
  { simp [norm_hom.of_cat, norm_hom.comp], },
  { ext,
    simp [norm_hom.prod_mk, norm_hom.comp, norm_hom.fst] },
  { ext,
    simp [norm_hom.prod_mk, norm_hom.comp, norm_hom.snd] },
  { ext;
    dsimp [norm_hom.prod_mk, norm_hom.comp, norm_hom.snd, norm_hom.fst];
    refl },
  { tidy },
  { tidy },
  { ext _ y,
    cases y;
    simp [norm_hom.coprod_mk, norm_hom.of_ff, to_presheaf_norm_hom_comp,
      norm_hom.inl, norm_hom.inr] },
end

def to_presheaf : prod_coprod C ⥤ (Cᵒᵖ ⥤ Type) :=
{ obj := to_presheaf_obj,
  map := λ X Y f, quotient.lift_on f (to_presheaf_norm_hom) to_presheaf_norm_hom_rel,
  map_id' := λ _, rfl,
  map_comp' := λ _ _ _ f g, quotient.induction_on₂ f g begin intros, simp,
    erw quotient.lift_on_mk,
    simp [to_presheaf_norm_hom_comp] end }

end norm_hom

def reverse_map : Π {X : C} {Y : prod_coprod C}, (to_presheaf.obj Y).obj (opposite.op X) →
  norm_hom tt (of_cat' X) Y
| X (of_cat' Y) := λ f, norm_hom.of_cat f
| X (prod Y Z) := λ f, norm_hom.prod_mk (reverse_map f.1) (reverse_map f.2)
| X (coprod Y Z) := λ f, f.elim
  (λ f, (reverse_map f).comp norm_hom.inl)
  (λ f, (reverse_map f).comp norm_hom.inr)

lemma reverse_map_to_presheaf : Π {X : C} {Y : prod_coprod C}
  (f : norm_hom tt (of_cat' X) Y),
  norm_hom.rel (reverse_map (yoneda_equiv.1 (to_presheaf.map (show hom (of_cat' X) Y, from ⟦f⟧)))) f :=
begin
  intros X Y f,
  refine @norm_hom.rec_on_tt _ _ (λ X' Y' f', ∀ (X : C) (h : X' = of_cat' X),
    let g : norm_hom tt (of_cat' X) Y' := eq.rec_on h f' in
    norm_hom.rel (reverse_map (yoneda_equiv.1 (to_presheaf.map (show hom (of_cat' X) Y', from ⟦g⟧)))) g)
    _ _ f _ _ X rfl,
  { rintros _ X rfl,
    dsimp [to_presheaf, reverse_map, to_presheaf_obj, norm_hom.of_cat],
    refine @quotient.exact _ (norm_hom.rel_setoid _ _) _ _ _,
    show _ = of_cat.map (𝟙 X),
     },
  { rintros X Y Z f g ih W rfl,
    dsimp, }

end

end prod_coprod
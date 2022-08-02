import .presheaves

open category_theory opposite

noncomputable theory

variables (C : Type) [category.{0} C]

inductive prod_coprod : Type
| of_cat' : C → prod_coprod
| prod : prod_coprod → prod_coprod → prod_coprod
| coprod : prod_coprod → prod_coprod → prod_coprod

variable {C}

namespace prod_coprod

inductive syntax : Π (X Y : prod_coprod C), Type
| of_cat {X Y : C} : (X ⟶ Y) → syntax (of_cat' X) (of_cat' Y)
| prod_mk {X Y Z : prod_coprod C} : syntax X Y → syntax X Z → syntax X (Y.prod Z)
| fst {X Y : prod_coprod C} : syntax (X.prod Y) X
| snd {X Y : prod_coprod C} : syntax (X.prod Y) Y
| coprod_mk {X Y Z : prod_coprod C} : syntax X Z → syntax Y Z → syntax (X.coprod Y) Z
| inl {X Y : prod_coprod C} : syntax X (X.coprod Y)
| inr {X Y : prod_coprod C} : syntax Y (X.coprod Y)
| id (X : prod_coprod C) : syntax X X
| comp {X Y Z : prod_coprod C} : syntax X Y → syntax Y Z → syntax X Z

namespace syntax

inductive rel : Π {X Y : prod_coprod C}, syntax X Y → syntax X Y → Prop
| refl {X Y : prod_coprod C} (f : syntax X Y) : rel f f
| symm {X Y : prod_coprod C} {f g : syntax X Y} : rel f g → rel g f
| trans {X Y : prod_coprod C} {f g h : syntax X Y} : rel f g → rel g h → rel f h
| comp_congr {X Y Z : prod_coprod C} {f₁ f₂ : syntax X Y} {g₁ g₂ : syntax Y Z} :
  rel f₁ f₂ → rel g₁ g₂ → rel (f₁.comp g₁) (f₂.comp g₂)
| prod_mk_congr {X Y Z : prod_coprod C} {f₁ f₂ : syntax X Y} {g₁ g₂ : syntax X Z} :
  rel f₁ f₂ → rel g₁ g₂ → rel (f₁.prod_mk g₁) (f₂.prod_mk g₂)
| coprod_mk_congr {X Y Z : prod_coprod C} {f₁ f₂ : syntax X Z} {g₁ g₂ : syntax Y Z} :
  rel f₁ f₂ → rel g₁ g₂ → rel (f₁.coprod_mk g₁) (f₂.coprod_mk g₂)
| id_comp {X Y : prod_coprod C} (f : syntax X Y) : rel ((syntax.id X).comp f) f
| comp_id {X Y : prod_coprod C} (f : syntax X Y) : rel (f.comp (syntax.id Y)) f
| assoc {W X Y Z : prod_coprod C} (f : syntax W X) (g : syntax X Y) (h : syntax Y Z) :
  rel ((f.comp g).comp h) (f.comp (g.comp h))
| of_cat_id {X : C} : rel (syntax.of_cat (𝟙 X)) (syntax.id (of_cat' X))
| of_cat_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
  rel (syntax.of_cat (f ≫ g)) (syntax.comp (syntax.of_cat f) (syntax.of_cat g))
| mk_fst_comp {X Y Z : prod_coprod C} (f : syntax X Y) (g : syntax X Z) :
  rel (syntax.comp (syntax.prod_mk f g) syntax.fst) f
| mk_snd_comp {X Y Z : prod_coprod C} (f : syntax X Y) (g : syntax X Z) :
  rel (syntax.comp (syntax.prod_mk f g) syntax.snd) g
| prod_eta {X Y Z : prod_coprod C} (f : syntax X (Y.prod Z)) :
  rel (syntax.prod_mk (f.comp syntax.fst) (f.comp syntax.snd)) f
| inl_comp_mk {X Y Z : prod_coprod C} (f : syntax X Z) (g : syntax Y Z) :
  rel (syntax.comp syntax.inl (syntax.coprod_mk f g)) f
| inr_comp_mk {X Y Z : prod_coprod C} (f : syntax X Z) (g : syntax Y Z) :
  rel (syntax.comp syntax.inr (syntax.coprod_mk f g)) g
| coprod_eta {X Y Z : prod_coprod C} (f : syntax (X.coprod Y) Z) :
  rel (syntax.coprod_mk (syntax.inl.comp f) (syntax.inr.comp f)) f

attribute [refl] rel.refl
attribute [symm] rel.symm
attribute [trans] rel.trans

infixl ` ♥ `: 50 := rel

lemma rel_prod {X Y Z : prod_coprod C} {f g : syntax X (Y.prod Z)}
  (h₁ : rel (f.comp syntax.fst) (g.comp syntax.fst))
  (h₂ : rel (f.comp syntax.snd) (g.comp syntax.snd)) :
  rel f g :=
calc f ♥ syntax.prod_mk (f.comp syntax.fst) (f.comp syntax.snd) : rel.symm (rel.prod_eta f)
   ... ♥ syntax.prod_mk (g.comp syntax.fst) (g.comp syntax.snd) : rel.prod_mk_congr h₁ h₂
   ... ♥ g : rel.prod_eta g

lemma rel_coprod {X Y Z : prod_coprod C} {f g : syntax (X.coprod Y) Z}
  (h₁ : rel (syntax.inl.comp f) (syntax.inl.comp g))
  (h₂ : rel (syntax.inr.comp f) (syntax.inr.comp g)) :
  rel f g :=
calc f ♥ syntax.coprod_mk (syntax.inl.comp f) (syntax.inr.comp f) : rel.symm (rel.coprod_eta f)
   ... ♥ syntax.coprod_mk (syntax.inl.comp g) (syntax.inr.comp g) : rel.coprod_mk_congr h₁ h₂
   ... ♥ g : rel.coprod_eta g

instance rel_setoid (X Y : prod_coprod C) : setoid (syntax X Y) :=
{ r := rel,
  iseqv := ⟨rel.refl, λ _ _, rel.symm, λ _ _ _, rel.trans⟩ }

end syntax

section syntax

open syntax

def hom (X Y : prod_coprod C) : Type := quotient (syntax.rel_setoid X Y)

instance : category_struct (prod_coprod C) :=
{ hom := hom,
  id := λ X, quotient.mk' (syntax.id X),
  comp := λ X Y Z f g, quotient.lift_on₂ f g (λ f g, quotient.mk' (syntax.comp f g))
    (λ f₁ g₁ f₂ g₂ hf hg, quotient.sound (rel.comp_congr hf hg)) }

instance : category (prod_coprod C) :=
{ id_comp' := λ X Y f, quotient.induction_on f (λ f, quotient.sound (rel.id_comp f)),
  comp_id' := λ X Y f, quotient.induction_on f (λ f, quotient.sound (rel.comp_id f)),
  assoc' := λ W X Y Z f g h, quotient.induction_on₃ f g h
    (λ f g h, quotient.sound (rel.assoc f g h)) }

def of_syntax {X Y : prod_coprod C} : syntax X Y → (X ⟶ Y) := quotient.mk

def of_cat : C ⥤ prod_coprod C :=
{ obj := λ X, of_cat' X,
  map := λ X Y f, of_syntax (syntax.of_cat f),
  map_id' := λ X, quotient.sound rel.of_cat_id,
  map_comp' := λ X Y Z f g, quotient.sound (rel.of_cat_comp f g) }

@[simp] lemma of_cat_obj (X : C) : of_cat.obj X = of_cat' X := rfl

def prod_mk {X Y Z : prod_coprod C} (f : X ⟶ Y) (g : X ⟶ Z) : X ⟶ (Y.prod Z) :=
quotient.lift_on₂ f g (λ f g, of_syntax (prod_mk f g)) begin
  intros,
  dsimp,
  refine quotient.sound _,
  refine rel.prod_mk_congr _ _; assumption
end

def fst {X Y : prod_coprod C} : (X.prod Y) ⟶ X :=
of_syntax fst

def snd {X Y : prod_coprod C} : (X.prod Y) ⟶ Y :=
of_syntax snd

@[simp] lemma prod_mk_fst_comp {X Y Z : prod_coprod C} (f : X ⟶ Y) (g : X ⟶ Z) :
  prod_mk f g ≫ fst = f :=
quotient.induction_on₂ f g (λ f g, quotient.sound (syntax.rel.mk_fst_comp _ _))

@[simp] lemma prod_mk_snd_comp {X Y Z : prod_coprod C} (f : X ⟶ Y) (g : X ⟶ Z) :
  prod_mk f g ≫ snd = g :=
quotient.induction_on₂ f g (λ f g, quotient.sound (syntax.rel.mk_snd_comp _ _))

lemma prod_mk_eta {X Y Z : prod_coprod C} (f : X ⟶ Y.prod Z) :
  prod_mk (f ≫ fst) (f ≫ snd) = f :=
quotient.induction_on f (λ f, quotient.sound (syntax.rel.prod_eta _))

@[ext] lemma prod_hom_ext {X Y Z : prod_coprod C} {f g : X ⟶ Y.prod Z}
  (h₁ : f ≫ fst = g ≫ fst) (h₂ : f ≫ snd = g ≫ snd) : f = g :=
begin
  conv_lhs { rw ← prod_mk_eta f },
  rw [h₁, h₂, prod_mk_eta]
end

def coprod_mk {X Y Z : prod_coprod C} (f : X ⟶ Z) (g : Y ⟶ Z) : (X.coprod Y) ⟶ Z :=
quotient.lift_on₂ f g (λ f g, of_syntax (coprod_mk f g)) begin
  intros,
  dsimp,
  refine quotient.sound _,
  refine rel.coprod_mk_congr _ _; assumption
end

def inl {X Y : prod_coprod C} : X ⟶ (X.coprod Y) :=
of_syntax inl

def inr {X Y : prod_coprod C} : Y ⟶ (X.coprod Y) :=
of_syntax inr

@[elab_as_eliminator] lemma hom_induction
  {motive : Π (X Y : prod_coprod C), (X ⟶ Y) → Prop}
  {X Y : prod_coprod C} (f : X ⟶ Y)
  (h₁ : Π {X Y : C} (f : X ⟶ Y), motive _ _ (of_cat.map f))
  (h₂ : Π {X Y Z : prod_coprod C} (f : X ⟶ Y) (g : X ⟶ Z),
     motive X Y f → motive X Z g → motive _ _ (prod_mk f g))
  (h₃ : Π {X Y : prod_coprod C}, motive (X.prod Y) X fst)
  (h₄ : Π {X Y : prod_coprod C}, motive (X.prod Y) Y snd)
  (h₅ : Π {X Y Z : prod_coprod C} (f : X ⟶ Z) (g : Y ⟶ Z),
     motive X Z f → motive Y Z g → motive _ _ (coprod_mk f g))
  (h₆ : Π {X Y : prod_coprod C}, motive X (X.coprod Y) inl)
  (h₇ : Π {X Y : prod_coprod C}, motive Y (X.coprod Y) inr)
  (h₈ : Π (X : prod_coprod C), motive X X (𝟙 X))
  (h₉ : Π {X Y Z : prod_coprod C} (f : X ⟶ Y) (g : Y ⟶ Z),
     motive X Y f → motive Y Z g → motive X Z (f ≫ g)) :
  motive X Y f :=
quotient.induction_on f
  begin
    intro f,
    apply syntax.rec_on f; try { assumption },
    { intros _ _ _ f g,
      exact h₂ (of_syntax f) (of_syntax g) },
    { intros _ _ _ f g,
      exact h₅ (of_syntax f) (of_syntax g) },
    { intros _ _ _ f g,
      exact h₉ (of_syntax f) (of_syntax g) }
  end

@[simp] lemma inl_comp_coprod_mk {X Y Z : prod_coprod C} (f : X ⟶ Z) (g : Y ⟶ Z) :
  inl ≫ coprod_mk f g = f :=
quotient.induction_on₂ f g (λ f g, quotient.sound (syntax.rel.inl_comp_mk _ _))

@[simp] lemma inr_comp_coprod_mk {X Y Z : prod_coprod C} (f : X ⟶ Z) (g : Y ⟶ Z) :
  inr ≫ coprod_mk f g = g :=
quotient.induction_on₂ f g (λ f g, quotient.sound (syntax.rel.inr_comp_mk _ _))

lemma coprod_mk_eta {X Y Z : prod_coprod C} (f : X.coprod Y ⟶ Z) :
  coprod_mk (inl ≫ f) (inr ≫ f) = f :=
quotient.induction_on f (λ f, quotient.sound (syntax.rel.coprod_eta _))

@[ext] lemma coprod_hom_ext {X Y Z : prod_coprod C} {f g : X.coprod Y ⟶ Z}
  (h₁ : inl ≫ f = inl ≫ g ) (h₂ : inr ≫ f = inr ≫ g) : f = g :=
begin
  conv_lhs { rw ← coprod_mk_eta f },
  rw [h₁, h₂, coprod_mk_eta]
end

-- def wf_rel (x y : (prod_coprod C × prod_coprod C) ⊕
--   (prod_coprod C × prod_coprod C × prod_coprod C)) :Prop :=
-- sum.lex (measure sizeof) (measure sizeof) x y



-- @[simp] def sizeof2 : prod_coprod C → ℕ
-- | (of_cat' X) := 0
-- | (prod X Y) := sizeof2 X + sizeof2 Y + 0
-- | (coprod X Y) := sizeof2 X + sizeof2 Y + 1

-- def hwf_rel_wf : has_well_founded ((prod_coprod C × prod_coprod C) ⊕
--   (prod_coprod C × prod_coprod C × prod_coprod C)) :=
-- ⟨_, measure_wf (λ x, sum.cases_on x
--     (λ x, sizeof x.1 + sizeof x.2)
--     (λ x, sizeof x.1 + sizeof x.2.1 + sizeof x.2.2))⟩

-- @[simp] lemma hwf_rel_wf_simp :@has_well_founded.r _ (@hwf_rel_wf C _) =
--   measure (λ x, sum.cases_on x
--     (λ x, sizeof x.1 + sizeof x.2)
--     (λ x, sizeof x.1 + sizeof x.2.1 + sizeof x.2.2)) := rfl

-- meta def wf_dec_tac : tactic unit :=
-- `[try { simp },
--   well_founded_tactics.default_dec_tac]

/-- Defining two maps by mutual induction. Morally we are defining the following.
  First - `norm_type (X Y : prod_coprod C) : Type`
    The type of normal form of maps `X ⟶ Y`.
  Second - `norm_type_not_proj (X Y Z : prod_coprod C) : Type`
    The type of normal forms of maps `(X.prod Y) ⟶ Z` that cannot be written
    `fst ≫ f` or `snd ≫ f` for any `f`
-/

-- @[simp] def norm_type :
--   ((prod_coprod C × prod_coprod C) ⊕
--   (prod_coprod C × prod_coprod C × prod_coprod C)) → Type
-- | (sum.inl (coprod X Y, Z)) := norm_type (sum.inl (X, Z)) × norm_type (sum.inl (Y, Z))
-- | (sum.inl (prod X Y, Z)) :=
--   norm_type (sum.inl (X, Z)) ⊕ norm_type (sum.inl (Y, Z))
--   ⊕ norm_type (sum.inr (X, Y, Z))
-- | (sum.inl (of_cat' X, of_cat' Y)) := X ⟶ Y
-- | (sum.inl (of_cat' X, prod Y Z)) :=
--   norm_type (sum.inl (of_cat' X, Y)) × norm_type (sum.inl (of_cat' X, Z))
-- | (sum.inl (of_cat' X, coprod Y Z)) :=
--   norm_type (sum.inl (of_cat' X, Y)) ⊕ norm_type (sum.inl (of_cat' X, Z))
-- | (sum.inr (W, X, coprod Y Z)) :=
--   norm_type (sum.inr (W, X, Y)) ⊕  -- (f : prod W X ⟶ Y) ≫ inl
--   norm_type (sum.inr (W, X, Z))  -- (f : prod W X ⟶ Z) ≫ inr
-- | (sum.inr (W, X, prod Y Z)) :=
--   (norm_type (sum.inr (W, X, Y)) × norm_type (sum.inr (W, X, Z))) ⊕ -- prod_mk _ _
--   (norm_type (sum.inl (W, Y)) × norm_type (sum.inl (X, Z))) ⊕
--   (norm_type (sum.inl (W, Z)) × norm_type (sum.inl (X, Y)))
-- | (sum.inr (X, Y, of_cat' Z)) := empty
-- using_well_founded {
--   dec_tac := wf_dec_tac,
--  rel_tac := λ _ _, `[exact hwf_rel_wf] }

inductive norm_hom :
  ((prod_coprod C × prod_coprod C) ⊕
  (prod_coprod C × prod_coprod C × prod_coprod C)) → Type
| coprod_mk {X Y Z : prod_coprod C} :
  norm_hom (sum.inl (X, Z)) → norm_hom (sum.inl (Y, Z)) →
  norm_hom (sum.inl (coprod X Y, Z))
| fst_comp {X Y Z : prod_coprod C} : norm_hom (sum.inl (X, Z)) →
  norm_hom (sum.inl (prod X Y, Z))
| snd_comp {X Y Z : prod_coprod C} : norm_hom (sum.inl (Y, Z)) →
  norm_hom (sum.inl (prod X Y, Z))
| of_not_proj {X Y Z : prod_coprod C} : norm_hom (sum.inr (X, Y, Z)) →
  norm_hom (sum.inl (prod X Y, Z))
| of_cat {X Y : C} : (X ⟶ Y) → norm_hom (sum.inl (of_cat' X, of_cat' Y))
| comp_inl_of_cat {X : C} {Y Z : prod_coprod C} : norm_hom (sum.inl (of_cat' X, Y)) →
  norm_hom (sum.inl (of_cat' X, coprod Y Z))
| comp_inr_of_cat {X : C} {Y Z : prod_coprod C} : norm_hom (sum.inl (of_cat' X, Z)) →
  norm_hom (sum.inl (of_cat' X, coprod Y Z))
| prod_mk_of_cat {X : C} {Y Z : prod_coprod C} : norm_hom (sum.inl (of_cat' X, Y)) →
  norm_hom (sum.inl (of_cat' X, Z)) → norm_hom (sum.inl (of_cat' X, prod Y Z))
| comp_inl_not_proj {W X Y Z : prod_coprod C} : norm_hom (sum.inr (W, X, Y)) →
  norm_hom (sum.inr (W, X, coprod Y Z))
| comp_inr_not_proj {W X Y Z : prod_coprod C} : norm_hom (sum.inr (W, X, Z)) →
  norm_hom (sum.inr (W, X, coprod Y Z))
| prod_mk_not_proj {W X Y Z : prod_coprod C} : norm_hom (sum.inr (W, X, Y)) →
  norm_hom (sum.inr (W, X, Z)) → norm_hom (sum.inr (W, X, prod Y Z))
| prod_mk_not_proj_fst_comp {W X Y Z : prod_coprod C} : norm_hom (sum.inr (W, X, Y)) →
  norm_hom (sum.inl (W, Z)) → norm_hom (sum.inr (W, X, prod Y Z))
| prod_mk_not_proj_snd_comp {W X Y Z : prod_coprod C} : norm_hom (sum.inr (W, X, Y)) →
  norm_hom (sum.inl (X, Z)) → norm_hom (sum.inr (W, X, prod Y Z))
| prod_mk_fst_comp_not_proj {W X Y Z : prod_coprod C} : norm_hom (sum.inl (W, Y)) →
  norm_hom (sum.inr (W, X, Z)) → norm_hom (sum.inr (W, X, prod Y Z))
| prod_mk_snd_comp_not_proj {W X Y Z : prod_coprod C} : norm_hom (sum.inl (X, Y)) →
  norm_hom (sum.inr (W, X, Z)) → norm_hom (sum.inr (W, X, prod Y Z))
| prod_mk_fst_comp_snd_comp {W X Y Z : prod_coprod C} :
  norm_hom (sum.inl (W, Y)) → norm_hom (sum.inl (X, Z)) →
  norm_hom (sum.inr (W, X, prod Y Z))
| prod_mk_snd_comp_fst_comp {W X Y Z : prod_coprod C} :
  norm_hom (sum.inl (X, Y)) → norm_hom (sum.inl (W, Z)) →
  norm_hom (sum.inr (W, X, prod Y Z))

variables {W X Y Z : prod_coprod C}

open norm_hom

def norm_hom.comp_inl : Π {X Y Z : prod_coprod C}, norm_hom (sum.inl (X, Y)) →
  norm_hom (sum.inl (X, coprod Y Z))
| (of_cat' X) _ _ f := norm_hom.comp_inl_of_cat f
| (coprod W X) Y Z (norm_hom.coprod_mk f g) := norm_hom.coprod_mk (norm_hom.comp_inl f) (norm_hom.comp_inl g)
| (prod W X) Y Z (norm_hom.fst_comp f) := norm_hom.fst_comp (norm_hom.comp_inl f)
| (prod W X) Y Z (norm_hom.snd_comp f) := norm_hom.snd_comp (norm_hom.comp_inl f)
| (prod W X) Y Z (norm_hom.of_not_proj f) := norm_hom.of_not_proj (norm_hom.comp_inl_not_proj f)

def norm_hom.comp_inr : Π {X Y Z : prod_coprod C}, norm_hom (sum.inl (X, Z)) →
  norm_hom (sum.inl (X, coprod Y Z))
| (of_cat' X) _ _ f := norm_hom.comp_inr_of_cat f
| (coprod W X) Y Z (norm_hom.coprod_mk f g) := norm_hom.coprod_mk (norm_hom.comp_inr f) (norm_hom.comp_inr g)
| (prod W X) Y Z (norm_hom.fst_comp f) := norm_hom.fst_comp (norm_hom.comp_inr f)
| (prod W X) Y Z (norm_hom.snd_comp f) := norm_hom.snd_comp (norm_hom.comp_inr f)
| (prod W X) Y Z (norm_hom.of_not_proj f) := norm_hom.of_not_proj (norm_hom.comp_inr_not_proj f)

def norm_hom.id : Π (X : prod_coprod C), norm_hom (sum.inl (X, X))
| (of_cat' X) := norm_hom.of_cat (𝟙 X)
| (prod X Y) := norm_hom.of_not_proj
  (norm_hom.prod_mk_fst_comp_snd_comp (norm_hom.id X) (norm_hom.id Y))
| (coprod X Y) :=
  norm_hom.coprod_mk
    (norm_hom.comp_inl (norm_hom.id _))
    (norm_hom.comp_inr (norm_hom.id _))

def norm_hom.inl {X Y : prod_coprod C} : norm_hom (sum.inl (X, coprod X Y)) :=
norm_hom.comp_inl (norm_hom.id _)

def norm_hom.inr {X Y : prod_coprod C} : norm_hom (sum.inl (Y, coprod X Y)) :=
norm_hom.comp_inr (norm_hom.id _)

def norm_hom.fst {X Y : prod_coprod C} : norm_hom (sum.inl (prod X Y, X)) :=
norm_hom.fst_comp (norm_hom.id _)

def norm_hom.snd {X Y : prod_coprod C} : norm_hom (sum.inl (prod X Y, Y)) :=
norm_hom.snd_comp (norm_hom.id _)

def norm_hom.prod_mk : Π {X Y Z : prod_coprod C} (f : norm_hom (sum.inl (X, Y)))
  (g : norm_hom (sum.inl (X, Z))), norm_hom (sum.inl (X, prod Y Z))
| (of_cat' X) Y Z f g := norm_hom.prod_mk_of_cat f g
| (prod W X) Y Z (norm_hom.fst_comp f) (norm_hom.fst_comp g) :=
  norm_hom.fst_comp (norm_hom.prod_mk f g)
| (prod W X) Y Z (norm_hom.snd_comp f) (norm_hom.snd_comp g) :=
  norm_hom.snd_comp (norm_hom.prod_mk f g)
| (prod W X) Y Z (norm_hom.fst_comp f) (norm_hom.snd_comp g) :=
  norm_hom.of_not_proj (norm_hom.prod_mk_fst_comp_snd_comp f g)
| (prod W X) Y Z (norm_hom.snd_comp f) (norm_hom.fst_comp g) :=
  norm_hom.of_not_proj (norm_hom.prod_mk_snd_comp_fst_comp f g)
| (prod W X) Y Z (norm_hom.of_not_proj f) (norm_hom.fst_comp g) :=
  norm_hom.of_not_proj (norm_hom.prod_mk_not_proj_fst_comp f g)
| (prod W X) Y Z (norm_hom.of_not_proj f) (norm_hom.snd_comp g) :=
  norm_hom.of_not_proj (norm_hom.prod_mk_not_proj_snd_comp f g)
| (prod W X) Y Z (norm_hom.fst_comp f) (norm_hom.of_not_proj g)  :=
  norm_hom.of_not_proj (norm_hom.prod_mk_fst_comp_not_proj f g)
| (prod W X) Y Z (norm_hom.snd_comp f) (norm_hom.of_not_proj g)  :=
  norm_hom.of_not_proj (norm_hom.prod_mk_snd_comp_not_proj f g)
| (prod W X) Y Z (norm_hom.of_not_proj f) (norm_hom.of_not_proj g)  :=
  norm_hom.of_not_proj (norm_hom.prod_mk_not_proj f g)
| (coprod W X) Y Z (norm_hom.coprod_mk f g) (norm_hom.coprod_mk h i) :=
  norm_hom.coprod_mk (norm_hom.prod_mk f h) (norm_hom.prod_mk g i)
--set_option timeout 400000

inductive norm_hom2 : Π (X Y : prod_coprod C), Type
| of_cat {X Y : C} (f : X ⟶ Y) : norm_hom2 (of_cat' X) (of_cat' Y)
| coprod_mk {X Y Z : prod_coprod C} (f : norm_hom2 X Z) (g : norm_hom2 Y Z) :
  norm_hom2 (X.coprod Y) Z
| comp_inl {X Y Z : prod_coprod C} (f : norm_hom2 X Y) :
  norm_hom2 X (coprod Y Z)
| comp_inr {X Y Z : prod_coprod C} (f : norm_hom2 X Z) :
  norm_hom2 X (coprod Y Z)
| prod_mk {X Y Z : prod_coprod C} (f : norm_hom2 X Y) (g : norm_hom2 X Z) :
  norm_hom2 X (prod Y Z)
| fst_comp {X Y Z : prod_coprod C} (f : norm_hom2 X Z) :
  norm_hom2 (prod X Y) Z
| snd_comp {X Y Z : prod_coprod C} (f : norm_hom2 Y Z) :
  norm_hom2 (prod X Y) Z

@[simp] def norm_hom.to_norm_hom2 : Π {X Y : prod_coprod C} (f : norm_hom (sum.inl (X, Y))),
  norm_hom2 X Y
| _ _ (norm_hom.of_cat f) := norm_hom2.of_cat f
| _ _ (norm_hom.coprod_mk f g) := norm_hom2.coprod_mk (norm_hom.to_norm_hom2 f) (norm_hom.to_norm_hom2 g)
| _ _ (norm_hom.fst_comp f) := norm_hom2.fst_comp (norm_hom.to_norm_hom2 f)
| _ _ (norm_hom.snd_comp f) := norm_hom2.snd_comp (norm_hom.to_norm_hom2 f)
| _ _ (norm_hom.comp_inl_of_cat f) := norm_hom2.comp_inl (norm_hom.to_norm_hom2 f)
| _ _ (norm_hom.comp_inr_of_cat f) := norm_hom2.comp_inr (norm_hom.to_norm_hom2 f)
| _ _ (norm_hom.prod_mk_of_cat f g) := norm_hom2.prod_mk (norm_hom.to_norm_hom2 f) (norm_hom.to_norm_hom2 g)
| _ _ (norm_hom.of_not_proj (norm_hom.comp_inl_not_proj f)) :=
  norm_hom2.comp_inl (norm_hom.to_norm_hom2 (norm_hom.of_not_proj f))
| _ _ (norm_hom.of_not_proj (norm_hom.comp_inr_not_proj f)) :=
  norm_hom2.comp_inr (norm_hom.to_norm_hom2 (norm_hom.of_not_proj f))
| _ _ (norm_hom.of_not_proj (norm_hom.prod_mk_not_proj f g)) :=
  norm_hom2.prod_mk (norm_hom.to_norm_hom2 f.of_not_proj) (norm_hom.to_norm_hom2 g.of_not_proj)
| _ _ (norm_hom.of_not_proj (norm_hom.prod_mk_not_proj_fst_comp f g)) :=
  norm_hom2.prod_mk (norm_hom.to_norm_hom2 f.of_not_proj) (norm_hom.to_norm_hom2 g.fst_comp)
| _ _ (norm_hom.of_not_proj (norm_hom.prod_mk_not_proj_snd_comp f g)) :=
  norm_hom2.prod_mk (norm_hom.to_norm_hom2 f.of_not_proj) (norm_hom.to_norm_hom2 g.snd_comp)
| _ _ (norm_hom.of_not_proj (norm_hom.prod_mk_fst_comp_not_proj f g)) :=
  norm_hom2.prod_mk (norm_hom.to_norm_hom2 f.fst_comp) (norm_hom.to_norm_hom2 g.of_not_proj)
| _ _ (norm_hom.of_not_proj (norm_hom.prod_mk_snd_comp_not_proj f g)) :=
  norm_hom2.prod_mk (norm_hom.to_norm_hom2 f.snd_comp) (norm_hom.to_norm_hom2 g.of_not_proj)
| _ _ (norm_hom.of_not_proj (norm_hom.prod_mk_fst_comp_snd_comp f g)) :=
  norm_hom2.prod_mk (norm_hom.to_norm_hom2 f.fst_comp) (norm_hom.to_norm_hom2 g.snd_comp)
| _ _ (norm_hom.of_not_proj (norm_hom.prod_mk_snd_comp_fst_comp f g)) :=
  norm_hom2.prod_mk (norm_hom.to_norm_hom2 f.snd_comp) (norm_hom.to_norm_hom2 g.fst_comp)

@[simp] def norm_hom2.comp : Π {X Y Z : prod_coprod C} (f : norm_hom2 X Y)
  (g : norm_hom2 Y Z), norm_hom2 X Z
| _ _ _ (norm_hom2.coprod_mk f g) h :=
  norm_hom2.coprod_mk (norm_hom2.comp f h) (norm_hom2.comp g h)
| _ _ _ (norm_hom2.fst_comp f) g :=
  norm_hom2.fst_comp (norm_hom2.comp f g)
| _ _ _ (norm_hom2.snd_comp f) g :=
  norm_hom2.snd_comp (norm_hom2.comp f g)
-- | _ _ _ f (norm_hom2.prod_mk g h) :=
--   norm_hom2.prod_mk (norm_hom2.comp f g) (norm_hom2.comp f h)
-- | _ _ _ f (norm_hom2.comp_inl g) :=
--   norm_hom2.comp_inl (norm_hom2.comp f g)
-- | _ _ _ f (norm_hom2.comp_inr g) :=
--   norm_hom2.comp_inr (norm_hom2.comp f g)
| _ _ _ (norm_hom2.of_cat f) (norm_hom2.of_cat g) :=
  norm_hom2.of_cat (f ≫ g)
| _ _ _ (norm_hom2.comp_inl f) (norm_hom2.coprod_mk g h) :=
  norm_hom2.comp f g
| _ _ _ (norm_hom2.comp_inr f) (norm_hom2.coprod_mk g h) :=
  norm_hom2.comp f h
| _ _ _  (norm_hom2.prod_mk f g) (norm_hom2.fst_comp h) :=
  norm_hom2.comp f h
| _ _ _  (norm_hom2.prod_mk f g) (norm_hom2.snd_comp h) :=
  norm_hom2.comp g h
--repeated cases
| _ _ _ (norm_hom2.of_cat f) (norm_hom2.comp_inl g) :=
  norm_hom2.comp_inl (norm_hom2.comp (norm_hom2.of_cat f) g)
| _ _ _ (norm_hom2.of_cat f) (norm_hom2.comp_inr g) :=
  norm_hom2.comp_inr (norm_hom2.comp (norm_hom2.of_cat f) g)
| _ _ _ (norm_hom2.of_cat f) (norm_hom2.prod_mk g h) :=
  norm_hom2.prod_mk (norm_hom2.comp (norm_hom2.of_cat f) g)
    (norm_hom2.comp (norm_hom2.of_cat f) h)
| _ _ _ f'@(norm_hom2.comp_inl f) (norm_hom2.comp_inl g) :=
  norm_hom2.comp_inl (norm_hom2.comp f' g)
| _ _ _ f'@(norm_hom2.comp_inr f) (norm_hom2.comp_inl g) :=
  norm_hom2.comp_inl (norm_hom2.comp f' g)
| _ _ _ f'@(norm_hom2.comp_inr f) (norm_hom2.comp_inr g) :=
  norm_hom2.comp_inr (norm_hom2.comp f' g)
| _ _ _ f'@(norm_hom2.comp_inl f) (norm_hom2.comp_inr g) :=
  norm_hom2.comp_inr (norm_hom2.comp f' g)
| _ _ _ f'@(norm_hom2.comp_inl f) (norm_hom2.prod_mk g h) :=
  norm_hom2.prod_mk (norm_hom2.comp f' g) (norm_hom2.comp f' h)
| _ _ _ f'@(norm_hom2.comp_inr f) (norm_hom2.prod_mk g h) :=
  norm_hom2.prod_mk (norm_hom2.comp f' g) (norm_hom2.comp f' h)
| _ _ _ f@(norm_hom2.prod_mk _ _) (norm_hom2.comp_inl g) :=
  norm_hom2.comp_inl (norm_hom2.comp f g)
| _ _ _ f@(norm_hom2.prod_mk _ _) (norm_hom2.comp_inr g) :=
  norm_hom2.comp_inr (norm_hom2.comp f g)
| _ _ _ f@(norm_hom2.prod_mk _ _) (norm_hom2.prod_mk g h) :=
  norm_hom2.prod_mk (norm_hom2.comp f g) (norm_hom2.comp f h)

@[simp] def norm_hom2.to_norm_hom : Π {X Y : prod_coprod C} (f : norm_hom2 X Y),
  norm_hom (sum.inl (X, Y))
| _ _ (norm_hom2.of_cat f) := norm_hom.of_cat f
| _ _ (norm_hom2.comp_inl f) := norm_hom.comp_inl (norm_hom2.to_norm_hom f)
| _ _ (norm_hom2.comp_inr f) := norm_hom.comp_inr (norm_hom2.to_norm_hom f)
| _ _ (norm_hom2.fst_comp f) := norm_hom.fst_comp (norm_hom2.to_norm_hom f)
| _ _ (norm_hom2.snd_comp f) := norm_hom.snd_comp (norm_hom2.to_norm_hom f)
| _ _ (norm_hom2.prod_mk f g) := norm_hom.prod_mk (norm_hom2.to_norm_hom f) (norm_hom2.to_norm_hom g)
| _ _ (norm_hom2.coprod_mk f g) := norm_hom.coprod_mk (norm_hom2.to_norm_hom f) (norm_hom2.to_norm_hom g)

@[simp] def norm_hom2.to_hom : Π {X Y : prod_coprod C} (f : norm_hom2 X Y), (X ⟶ Y)
| _ _ (norm_hom2.of_cat f) := of_cat.map f
| _ _ (norm_hom2.comp_inl f) := norm_hom2.to_hom f ≫ inl
| _ _ (norm_hom2.comp_inr f) := norm_hom2.to_hom f ≫ inr
| _ _ (norm_hom2.fst_comp f) := fst ≫ norm_hom2.to_hom f
| _ _ (norm_hom2.snd_comp f) := snd ≫ norm_hom2.to_hom f
| _ _ (norm_hom2.prod_mk f g) := prod_mk (norm_hom2.to_hom f) (norm_hom2.to_hom g)
| _ _ (norm_hom2.coprod_mk f g) := coprod_mk (norm_hom2.to_hom f) (norm_hom2.to_hom g)

@[simp] def norm_hom.comp {X Y Z : prod_coprod C} (f : norm_hom (sum.inl (X, Y)))
  (g : norm_hom (sum.inl (Y, Z))) : norm_hom (sum.inl (X, Z)) :=
(f.to_norm_hom2.comp g.to_norm_hom2).to_norm_hom

lemma comp_id {X Y Z : prod_coprod C}
  (f : norm_hom (sum.inl (X, Y))) :
  f.comp (norm_hom.id _) = f :=
begin

end
-- | (coprod W X) Y Z (norm_hom.coprod_mk f g) := norm_hom.coprod_mk (norm_hom.comp_inl f) (norm_hom.comp_inl g)
-- | (prod W X) Y Z (norm_hom.fst_comp f) := norm_hom.fst_comp (norm_hom.comp_inl f)
-- | (prod W X) Y Z (norm_hom.snd_comp f) := norm_hom.snd_comp (norm_hom.comp_inl f)
-- | (prod W X) Y Z (norm_hom.of_not_proj f) := norm_hom.of_not_proj (norm_hom.comp_inl_not_proj f)

@[simp] def norm_syntax : Π {X Y : prod_coprod C} (f : syntax X Y),
  norm_hom (sum.inl (X, Y))
| _ _ (syntax.of_cat f) := norm_hom.of_cat f
| _ _ (syntax.id _) := norm_hom.id _
| _ _ (syntax.comp f g) := (norm_syntax f).comp (norm_syntax g)
| _ _ syntax.fst := norm_hom.fst
| _ _ syntax.snd := norm_hom.snd
| _ _ (syntax.prod_mk f g) := norm_hom.prod_mk (norm_syntax f) (norm_syntax g)
| _ _ syntax.inl := norm_hom.inl
| _ _ syntax.inr := norm_hom.inr
| _ _ (syntax.coprod_mk f g) := norm_hom.coprod_mk (norm_syntax f) (norm_syntax g)

lemma norm_syntax_rel : Π {X Y : prod_coprod C} {f g : syntax X Y}, rel f g → norm_syntax f = norm_syntax g :=
begin
  intros X Y f g h,
  induction h; simp [*, norm_hom.to_norm_hom2, norm_hom.id] at *,

end
#exit
@[simp] lemma to_hom_comp_inl : Π {X Y Z : prod_coprod C} (f : norm_hom (sum.inl (X, Y))),
  (@norm_hom.comp_inl _ _ _ _ Z f).to_norm_hom2.to_hom = f.to_norm_hom2.to_hom ≫ inl
| (of_cat' X) _ _ f := by simp [norm_hom.comp_inl]
| (coprod W X) Y Z (norm_hom.coprod_mk f g) :=
  by ext; simp [norm_hom.comp_inl, to_hom_comp_inl f, to_hom_comp_inl g,
    ← category.assoc]
| (prod W X) Y Z (norm_hom.fst_comp f) := by simp [norm_hom.comp_inl, to_hom_comp_inl f]
| (prod W X) Y Z (norm_hom.snd_comp f) := by simp [norm_hom.comp_inl, to_hom_comp_inl f]
| (prod W X) Y Z (norm_hom.of_not_proj f) :=
  by simp [norm_hom.comp_inl, to_hom_comp_inl f.of_not_proj]

@[simp] lemma to_hom_comp_inr : Π {X Y Z : prod_coprod C} (f : norm_hom (sum.inl (X, Z))),
  (@norm_hom.comp_inr _ _ X Y Z f).to_norm_hom2.to_hom = f.to_norm_hom2.to_hom ≫ inr
| (of_cat' X) _ _ f := by simp [norm_hom.comp_inr]
| (coprod W X) Y Z (norm_hom.coprod_mk f g) :=
  by ext; simp [norm_hom.comp_inr, to_hom_comp_inr f, to_hom_comp_inr g,
    ← category.assoc]
| (prod W X) Y Z (norm_hom.fst_comp f) := by simp [norm_hom.comp_inr, to_hom_comp_inr f]
| (prod W X) Y Z (norm_hom.snd_comp f) := by simp [norm_hom.comp_inr, to_hom_comp_inr f]
| (prod W X) Y Z (norm_hom.of_not_proj f) :=
  by simp [norm_hom.comp_inr, to_hom_comp_inr f.of_not_proj]

@[simp] lemma to_hom_prod_mk : Π {X Y Z : prod_coprod C} (f : norm_hom (sum.inl (X, Y)))
  (g : norm_hom (sum.inl (X, Z))),
  (f.prod_mk g).to_norm_hom2.to_hom = prod_mk f.to_norm_hom2.to_hom g.to_norm_hom2.to_hom
| (of_cat' X) Y Z f g := by simp [norm_hom.prod_mk]
| (prod W X) Y Z (norm_hom.fst_comp f) (norm_hom.fst_comp g) :=
  by ext; simp [norm_hom.prod_mk, to_hom_prod_mk f, to_hom_prod_mk g]
| (prod W X) Y Z (norm_hom.snd_comp f) (norm_hom.snd_comp g) :=
  by ext; simp [norm_hom.prod_mk, to_hom_prod_mk f, to_hom_prod_mk g]
| (prod W X) Y Z (norm_hom.fst_comp f) (norm_hom.snd_comp g) :=
  by ext; simp [norm_hom.prod_mk, to_hom_prod_mk f, to_hom_prod_mk g]
| (prod W X) Y Z (norm_hom.snd_comp f) (norm_hom.fst_comp g) :=
  by ext; simp [norm_hom.prod_mk, to_hom_prod_mk f, to_hom_prod_mk g]
| (prod W X) Y Z (norm_hom.of_not_proj f) (norm_hom.fst_comp g) :=
  by ext; simp [norm_hom.prod_mk, to_hom_prod_mk f.of_not_proj, to_hom_prod_mk g]
| (prod W X) Y Z (norm_hom.of_not_proj f) (norm_hom.snd_comp g) :=
  by ext; simp [norm_hom.prod_mk, to_hom_prod_mk f.of_not_proj, to_hom_prod_mk g]
| (prod W X) Y Z (norm_hom.fst_comp f) (norm_hom.of_not_proj g)  :=
  by ext; simp [norm_hom.prod_mk, to_hom_prod_mk f, to_hom_prod_mk g.of_not_proj]
| (prod W X) Y Z (norm_hom.snd_comp f) (norm_hom.of_not_proj g)  :=
  by ext; simp [norm_hom.prod_mk, to_hom_prod_mk f, to_hom_prod_mk g.of_not_proj]
| (prod W X) Y Z (norm_hom.of_not_proj f) (norm_hom.of_not_proj g)  :=
  by ext; simp [norm_hom.prod_mk, to_hom_prod_mk f.of_not_proj, to_hom_prod_mk g.of_not_proj]
| (coprod W X) Y Z (norm_hom.coprod_mk f g) (norm_hom.coprod_mk h i) :=
  by ext; simp [norm_hom.prod_mk, to_hom_prod_mk f, to_hom_prod_mk g]

@[simp] lemma to_hom_comp : Π {X Y Z : prod_coprod C} (f : norm_hom2 X Y) (g : norm_hom2 Y Z),
  (f.comp g).to_hom = f.to_hom ≫ g.to_hom
| _ _ _ (norm_hom2.coprod_mk f g) h :=
  by ext; simp [to_hom_comp f, to_hom_comp g, ← category.assoc]
| _ _ _ (norm_hom2.fst_comp f) g :=
  by simp [to_hom_comp f]
| _ _ _ (norm_hom2.snd_comp f) g :=
  by simp [to_hom_comp f]
-- | _ _ _ f (norm_hom2.prod_mk g h) :=
-- | _ _ _ f (norm_hom2.comp_inl g) := g)
-- | _ _ _ f (norm_hom2.comp_inr g) :=
| _ _ _ (norm_hom2.of_cat f) (norm_hom2.of_cat g) :=
  by simp
| _ _ _ (norm_hom2.comp_inl f) (norm_hom2.coprod_mk g h) :=
  by simp [to_hom_comp f]
| _ _ _ (norm_hom2.comp_inr f) (norm_hom2.coprod_mk g h) :=
  by simp [to_hom_comp f]
| _ _ _  (norm_hom2.prod_mk f g) (norm_hom2.fst_comp h) :=
  by simp [to_hom_comp _ h, ← category.assoc]
| _ _ _  (norm_hom2.prod_mk f g) (norm_hom2.snd_comp h) :=
  by simp [to_hom_comp _ h, ← category.assoc]
--repeated cases
| _ _ _ (norm_hom2.of_cat f) (norm_hom2.comp_inl g) :=
  by simp [to_hom_comp _ g]
| _ _ _ (norm_hom2.of_cat f) (norm_hom2.comp_inr g) :=
  by simp [to_hom_comp _ g]
| _ _ _ (norm_hom2.of_cat f) (norm_hom2.prod_mk g h) :=
  by ext; simp [to_hom_comp _ g, to_hom_comp _ h]
| _ _ _ (norm_hom2.comp_inl f) (norm_hom2.comp_inl g) :=
  by simp [to_hom_comp _ g]
| _ _ _ (norm_hom2.comp_inr f) (norm_hom2.comp_inl g) :=
  by simp [to_hom_comp _ g]
| _ _ _ f'@(norm_hom2.comp_inr f) (norm_hom2.comp_inr g) :=
  by simp [to_hom_comp _ g]
| _ _ _ f'@(norm_hom2.comp_inl f) (norm_hom2.comp_inr g) :=
  by simp [to_hom_comp _ g]
| _ _ _ f'@(norm_hom2.comp_inl f) (norm_hom2.prod_mk g h) :=
  by ext; simp [to_hom_comp _ g, to_hom_comp _ h]
| _ _ _ f'@(norm_hom2.comp_inr f) (norm_hom2.prod_mk g h) :=
  by ext; simp [to_hom_comp _ g, to_hom_comp _ h]
| _ _ _ f@(norm_hom2.prod_mk _ _) (norm_hom2.comp_inl g) :=
  by simp [to_hom_comp _ g]
| _ _ _ f@(norm_hom2.prod_mk _ _) (norm_hom2.comp_inr g) :=
  by simp [to_hom_comp _ g]
| _ _ _ f@(norm_hom2.prod_mk _ _) (norm_hom2.prod_mk g h) :=
  by ext; simp [to_hom_comp _ g, to_hom_comp _ h]



#exit
lemma to_presheaf_syntax_comp {X Y Z : prod_coprod C} (f : syntax X Y) (g : syntax Y Z) :
  to_presheaf_syntax (f.comp g) = to_presheaf_syntax f ≫ to_presheaf_syntax g := rfl

lemma to_presheaf_syntax_rel {X Y : prod_coprod C} (f g : syntax X Y) (h : rel f g) :
  to_presheaf_syntax f = to_presheaf_syntax g :=
begin
  induction h; try { simp * }; try { ext }; try { refl }; tidy,
end

def to_presheaf : prod_coprod C ⥤ (Cᵒᵖ ⥤ Type) :=
{ obj := to_presheaf_obj,
  map := λ X Y f, quotient.lift_on f (to_presheaf_syntax) to_presheaf_syntax_rel,
  map_id' := λ _, rfl,
  map_comp' := λ _ _ _ f g, quotient.induction_on₂ f g begin intros, simp,
    erw quotient.lift_on_mk,
    simp [to_presheaf_syntax_comp] end }

@[simp] lemma to_presheaf_obj_of_cat (X : C) : to_presheaf.obj (of_cat' X) = yoneda.obj X := rfl

@[simp] lemma to_presheaf_obj_prod (X Y : prod_coprod C) : to_presheaf.obj (prod X Y) =
  Pprod (to_presheaf_obj X) (to_presheaf_obj Y) := rfl

@[simp] lemma to_presheaf_obj_coprod (X Y : prod_coprod C) : to_presheaf.obj (coprod X Y) =
  Pcoprod (to_presheaf_obj X) (to_presheaf_obj Y) := rfl

@[simp] lemma to_presheaf_of_cat {X Y : C} (f : X ⟶ Y) :
  to_presheaf.map (of_cat.map f) = yoneda.map f := rfl

@[simp] lemma to_presheaf_prod_mk {X Y Z : prod_coprod C}
  (f : X ⟶ Y) (g : X ⟶ Z) :
  to_presheaf.map (prod_mk f g) = Pprod_lift (to_presheaf.map f) (to_presheaf.map g) :=
begin
  refine quotient.induction_on₂ f g _,
  intros, refl
end

@[simp] lemma to_presheaf_coprod_mk {X Y Z : prod_coprod C}
  (f : X ⟶ Z) (g : Y ⟶ Z) :
  to_presheaf.map (coprod_mk f g) = Pcoprod_lift (to_presheaf.map f) (to_presheaf.map g) :=
begin
  refine quotient.induction_on₂ f g _,
  intros, refl
end

@[simp] lemma to_presheaf_fst {X Y : prod_coprod C} :
  to_presheaf.map (fst : X.prod Y ⟶ X) = Pprod_fst := rfl

@[simp] lemma to_presheaf_snd {X Y : prod_coprod C} :
  to_presheaf.map (snd : X.prod Y ⟶ Y) = Pprod_snd := rfl

@[simp] lemma to_presheaf_inl {X Y : prod_coprod C} :
  to_presheaf.map (inl : X ⟶ X.coprod Y) = Pcoprod_inl := rfl

@[simp] lemma to_presheaf_inr {X Y : prod_coprod C} :
  to_presheaf.map (inr : Y ⟶ X.coprod Y) = Pcoprod_inr := rfl

end syntax

def transformation_syntax : Π {X : C} {Y : prod_coprod C}, (to_presheaf.obj Y).obj (opposite.op X) →
  syntax (of_cat' X) Y
| X (of_cat' Y) := λ f, syntax.of_cat f
| X (prod Y Z) := λ f, syntax.prod_mk (transformation_syntax f.1) (transformation_syntax f.2)
| X (coprod Y Z) := λ f, f.elim
  (λ f, (transformation_syntax f).comp syntax.inl)
  (λ f, (transformation_syntax f).comp syntax.inr)

@[simp] def transformation : Π {X : C} {Y : prod_coprod C},
  (to_presheaf.obj Y).obj (opposite.op X) →
  ((of_cat' X) ⟶ Y)
| X (of_cat' Y) := λ f, of_cat.map f
| X (prod Y Z) := λ f, prod_mk (transformation f.1) (transformation f.2)
| X (coprod Y Z) := λ f, f.elim
  (λ f, (transformation f) ≫ inl)
  (λ f, (transformation f) ≫ inr)

lemma transformation_eq_of_syntax_transformation_syntax {X : C} {Y : prod_coprod C}
  (x : (to_presheaf.obj Y).obj (opposite.op X)) :
  transformation x = of_syntax (transformation_syntax x) :=
by induction Y; simp [transformation, transformation_syntax, *]; tidy

lemma transformation_left_naturality : Π {X Y : prod_coprod C}
  (f : X ⟶ Y) ⦃Z : C⦄ (z : (to_presheaf.obj X).obj (op Z)),
  transformation ((to_presheaf.map f).app (op Z) z) =
  transformation z ≫ f :=
begin
  intros X Y f Z z, revert Z z,
  refine hom_induction f _ _ _ _ _ _ _ _ _; intros; try { ext };
  try { dsimp at * }; try { simp * at * },
  cases z; simp *
end

def transformation_inverse {X : C} {Y : prod_coprod C}
  (f : (of_cat' X) ⟶ Y) :
  (to_presheaf.obj Y).obj (opposite.op X) :=
yoneda_equiv (to_presheaf.map f)

lemma transformation_transformation_inverse {X : C} {Y : prod_coprod C}
  (f : (of_cat' X) ⟶ Y) : transformation (transformation_inverse f) = f :=
begin
  simp [yoneda_equiv, transformation_inverse, transformation_left_naturality],
  exact category.id_comp _,
end

lemma transformation_inverse_transformation {X : C} {Y : prod_coprod C}
  (f : (to_presheaf.obj Y).obj (opposite.op X)) :
  transformation_inverse (transformation f) = f :=
begin
  simp [yoneda_equiv, transformation_inverse, transformation_left_naturality],
  induction Y,
  { simp [transformation], exact category.id_comp _ },
  { simp [transformation, *] },
  { cases f;
    simp [transformation, *] }
end

instance of_cat_full : full (@of_cat C _) :=
{ preimage := λ X Y f, ((to_presheaf.map f).app (op X) (𝟙 X)),
  witness' := λ X Y f, begin
    have := transformation_left_naturality f (𝟙 X),
    simp at this,
    erw [category.id_comp] at this,
    simpa using this
  end }

instance of_cat_faithful : faithful (@of_cat C _) :=
{ map_injective' := λ X Y f g h, begin
    have := congr_arg transformation_inverse h,
    simp [transformation_inverse] at this,
    erw [category.id_comp] at this,
    erw [category.id_comp] at this,
    assumption
end }

def normalize {X : C} {Y : prod_coprod C}
  (f : (of_cat' X) ⟶ Y) : syntax (of_cat' X) Y :=
transformation_syntax (transformation_inverse f)

lemma of_syntax_normalize {X : C} {Y : prod_coprod C}
  (f : (of_cat' X) ⟶ Y) : of_syntax (normalize f) = f :=
by rw [normalize, ← transformation_eq_of_syntax_transformation_syntax,
  transformation_transformation_inverse]

end prod_coprod
import category_theory.adjunction.basic
import category_theory.limits.preserves.basic

open category_theory category_theory.functor category_theory.limits

variables (𝒞 : Type) [category.{0} 𝒞]

inductive bicompletion_aux : bool → Type 1
| of_cat_obj : 𝒞 → bicompletion_aux ff
| of_cat_hom : Π {X Y : 𝒞}, (X ⟶ Y) → bicompletion_aux tt -- of_cat_obj X ⟶ of_cat_obj Y
| limit_obj {𝒟 : Type} [category.{0} 𝒟] (F_obj : 𝒟 → bicompletion_aux ff) 
  (F_hom : Π {X Y : 𝒟}, (X ⟶ Y) → bicompletion_aux tt) : bicompletion_aux ff
| limit_cone_comp {𝒟 : Type} [category.{0} 𝒟] (F_obj : 𝒟 → bicompletion_aux ff)
  (F_hom : Π {X Y : 𝒟}, (X ⟶ Y) → bicompletion_aux tt)
  (X : 𝒟) (Y : bicompletion_aux ff) (f : bicompletion_aux tt) : -- F_obj X ⟶ Y
  bicompletion_aux tt -- limit_obj F_obj F_hom ⟶ Y
| is_limit {𝒟 : Type} [category.{0} 𝒟] (F_obj : 𝒟 → bicompletion_aux ff) 
  (F_hom : Π {X Y : 𝒟}, (X ⟶ Y) → bicompletion_aux tt)
  (cone_obj : bicompletion_aux ff)
  (cone : Π (X : 𝒟), bicompletion_aux tt) : -- cone_obj ⟶ F_obj X
  bicompletion_aux tt -- cone_obj → limit_obj F_obj F_hom
| colimit_obj {𝒟 : Type} [category.{0} 𝒟] (F_obj : 𝒟 → bicompletion_aux ff) 
  (F_hom : Π {X Y : 𝒟}, (X ⟶ Y) → bicompletion_aux tt) : bicompletion_aux ff
| colimit_cocone_comp {𝒟 : Type} [category.{0} 𝒟] (F_obj : 𝒟 → bicompletion_aux ff) 
  (F_hom : Π {X Y : 𝒟}, (X ⟶ Y) → bicompletion_aux tt) 
  (X : 𝒟) (Y : bicompletion_aux ff) (f : bicompletion_aux tt) : -- Y ⟶ F_obj X
  bicompletion_aux tt -- Y ⟶ colimit_obj F_obj F_hom
| is_colimit {𝒟 : Type} [category.{0} 𝒟] (F_obj : 𝒟 → bicompletion_aux ff) 
  (F_hom : Π {X Y : 𝒟}, (X ⟶ Y) → bicompletion_aux tt) 
  (cocone_obj : bicompletion_aux ff)
  (cocone : Π (X : 𝒟), bicompletion_aux tt) : -- F_obj X ⟶ cocone_obj
  bicompletion_aux tt -- colimit_obj F_obj F_hom ⟶ cocone_obj

namespace bicompletion_aux

variable {𝒞}

@[simp] def dom : Π (X : bicompletion_aux 𝒞 tt), bicompletion_aux 𝒞 ff
| (@of_cat_hom _ _ X Y f) := of_cat_obj X 
| (@limit_cone_comp _ _ 𝒟 _ F_obj F_hom X _ _) := by exactI limit_obj F_obj @F_hom
| (@is_limit _ _ 𝒟 _ F_obj F_hom cone_obj cone) := cone_obj
| (@colimit_cocone_comp _ _ 𝒟 _ F_obj F_hom X Y f) := Y
| (@is_colimit _ _ 𝒟 _ F_obj F_hom cocone_obj cocone) := by exactI colimit_obj F_obj @F_hom

@[simp] def cod : Π (X : bicompletion_aux 𝒞 tt), bicompletion_aux 𝒞 ff
| (@of_cat_hom _ _ X Y f) := of_cat_obj Y 
| (@colimit_cocone_comp _ _ 𝒟 _ F_obj F_hom X _ _) := by exactI colimit_obj F_obj @F_hom
| (@is_colimit _ _ 𝒟 _ F_obj F_hom cocone_obj cocone) := cocone_obj
| (@limit_cone_comp _ _ 𝒟 _ F_obj F_hom X Y f) := Y
| (@is_limit _ _ 𝒟 _ F_obj F_hom cone_obj cone) := by exactI limit_obj F_obj @F_hom


variable (𝒞)

def obj₁ : Type 1 := bicompletion_aux 𝒞 ff

variable {𝒞}
variables {𝒟 : Type} [category.{0} 𝒟]

def hom₁ (X Y : obj₁ 𝒞) : Type 1 :=
{ f : bicompletion_aux 𝒞 tt // f.dom = X ∧ f.cod = Y }

def of_cat_obj₁ (X : 𝒞) : obj₁ 𝒞 := of_cat_obj X

def limit_obj₁ (F_obj : 𝒟 → obj₁ 𝒞) 
  (F_hom : Π {X Y : 𝒟}, (X ⟶ Y) → hom₁ (F_obj X) (F_obj Y)) : obj₁ 𝒞 :=
limit_obj F_obj (λ X Y f, (F_hom f).1)

def colimit_obj₁ (F_obj : 𝒟 → obj₁ 𝒞) 
  (F_hom : Π {X Y : 𝒟}, (X ⟶ Y) → hom₁ (F_obj X) (F_obj Y)) : obj₁ 𝒞 :=
colimit_obj F_obj (λ X Y f, (F_hom f).1)

def of_cat_hom₁ {X Y : 𝒞} (f : X ⟶ Y) : hom₁ (of_cat_obj X) (of_cat_obj Y) :=
⟨of_cat_hom f, by simp⟩

def limit_cone_comp₁ (F_obj : 𝒟 → obj₁ 𝒞)
  (F_hom : Π {X Y : 𝒟}, (X ⟶ Y) → hom₁ (F_obj X) (F_obj Y)) (X : 𝒟) 
  {Y : obj₁ 𝒞} (f : hom₁ (F_obj X) Y) :
  hom₁ (limit_obj₁ F_obj @F_hom) Y :=
⟨limit_cone_comp F_obj (λ X Y f, (F_hom f).1) X Y f.1, by simp [limit_obj₁]⟩

def colimit_cocone_comp₁ (F_obj : 𝒟 → obj₁ 𝒞)
  (F_hom : Π {X Y : 𝒟}, (X ⟶ Y) → hom₁ (F_obj X) (F_obj Y)) (X : 𝒟) 
  {Y : obj₁ 𝒞} (f : hom₁ Y (F_obj X)) :
  hom₁ Y (colimit_obj₁ F_obj @F_hom) :=
⟨colimit_cocone_comp F_obj (λ X Y f, (F_hom f).1) X Y f.1, by simp [colimit_obj₁]⟩

def is_limit₁ (F_obj : 𝒟 → obj₁ 𝒞) 
  (F_hom : Π {X Y : 𝒟}, (X ⟶ Y) → hom₁ (F_obj X) (F_obj Y))
  (cone_obj : obj₁ 𝒞)
  (cone : Π (X : 𝒟), hom₁ cone_obj (F_obj X)) :
  hom₁ cone_obj (limit_obj₁ F_obj @F_hom) :=
⟨is_limit F_obj (λ X Y f, (F_hom f).1) cone_obj (λ X, (cone X).1), by simp [limit_obj₁]⟩

def is_colimit₁ (F_obj : 𝒟 → obj₁ 𝒞) 
  (F_hom : Π {X Y : 𝒟}, (X ⟶ Y) → hom₁ (F_obj X) (F_obj Y))
  (cocone_obj : obj₁ 𝒞)
  (cocone : Π (X : 𝒟), hom₁ (F_obj X) cocone_obj) :
  hom₁ (colimit_obj₁ F_obj @F_hom) cocone_obj  :=
⟨is_colimit F_obj (λ X Y f, (F_hom f).1) cocone_obj (λ X, (cocone X).1), by simp [colimit_obj₁]⟩

def id₁ : Π (X : obj₁ 𝒞), hom₁ X X
| (of_cat_obj X) := of_cat_hom₁ (𝟙 X)
| (@limit_obj _ _ 𝒟 _ F_obj F_hom) := 
  by exactI ⟨is_limit F_obj @F_hom (limit_obj F_obj @F_hom) 
    (λ D, limit_cone_comp F_obj @F_hom D _ _), _⟩

inductive valid_obj₁ : Π (X : obj₁ 𝒞), Prop
| of_cat_obj (X : 𝒞) : valid_obj₁ (of_cat_obj X)
| limit_obj {𝒟 : Type} [category.{0} 𝒟] (F_obj : 𝒟 → obj₁ 𝒞) 
  (F_hom : Π {X Y : 𝒟}, (X ⟶ Y) → hom₁ (F_obj X) (F_obj Y)) 
  (h : Π X : 𝒟, valid_obj₁ (F_obj X)) : 
  valid_obj₁ (limit_obj₁ F_obj @F_hom)
| colimit_obj {𝒟 : Type} [category.{0} 𝒟] (F_obj : 𝒟 → obj₁ 𝒞) 
  (F_hom : Π {X Y : 𝒟}, (X ⟶ Y) → hom₁ (F_obj X) (F_obj Y)) 
  (h : Π X : 𝒟, valid_obj₁ (F_obj X)) :
  valid_obj₁ (colimit_obj₁ F_obj @F_hom)

def valid_obj₁_limit_obj 
  {𝒟 : Type} [category.{0} 𝒟] {F_obj : 𝒟 → obj₁ 𝒞}
  {F_hom : Π {X Y : 𝒟}, (X ⟶ Y) → bicompletion_aux 𝒞 tt}
  (h : valid_obj₁ (limit_obj F_obj @F_hom)) :
  Π (X : 𝒟), valid_obj₁ (F_obj X) :=
begin
  generalize hX : limit_obj F_obj @F_hom = X,
  rw hX at h,
  induction h,
  { simp * at * },
  { simp [limit_obj₁] at hX,
    rcases hX with ⟨hX₁, hX₂, hX₂, hX₄⟩,
    subst hX₁,
    simp at *,
    subst hX₂,
    assumption },
  { simp [*, colimit_obj₁] at * }
end

def valid_obj₁_colimit_obj 
  {𝒟 : Type} [category.{0} 𝒟] {F_obj : 𝒟 → obj₁ 𝒞}
  {F_hom : Π {X Y : 𝒟}, (X ⟶ Y) → bicompletion_aux 𝒞 tt}
  (h : valid_obj₁ (colimit_obj F_obj @F_hom)) :
  Π (X : 𝒟), valid_obj₁ (F_obj X) :=
begin
  generalize hX : colimit_obj F_obj @F_hom = X,
  rw hX at h,
  induction h,
  { simp * at * },
  { simp [*, limit_obj₁] at * },
  { simp [colimit_obj₁] at hX,
    rcases hX with ⟨hX₁, hX₂, hX₂, hX₄⟩,
    subst hX₁,
    simp at *,
    subst hX₂,
    assumption }
end

inductive valid_hom₁ : Π {X Y : obj₁ 𝒞}, hom₁ X Y → Type 1
| of_cat_hom {X Y : 𝒞} (f : X ⟶ Y) : valid_hom₁ (of_cat_hom₁ f)
| limit_cone_comp {𝒟 : Type} [category.{0} 𝒟] (F_obj : 𝒟 → obj₁ 𝒞)
  (F_hom : Π {X Y : 𝒟}, (X ⟶ Y) → hom₁ (F_obj X) (F_obj Y)) 
  (X : 𝒟) {Y : obj₁ 𝒞} (f : hom₁ (F_obj X) Y) 
  (F_hom_valid : Π {X Y : 𝒟} (f : X ⟶ Y), valid_hom₁ (F_hom f))
  (f_valid : valid_hom₁ f) :
  valid_hom₁ (limit_cone_comp₁ F_obj @F_hom X f)
| colimit_cocone_comp {𝒟 : Type} [category.{0} 𝒟] (F_obj : 𝒟 → obj₁ 𝒞)
  (F_hom : Π {X Y : 𝒟}, (X ⟶ Y) → hom₁ (F_obj X) (F_obj Y)) 
  (X : 𝒟) {Y : obj₁ 𝒞} (f : hom₁ Y (F_obj X)) 
  (F_hom_valid : Π {X Y : 𝒟} (f : X ⟶ Y), valid_hom₁ (F_hom f))
  (f_valid : valid_hom₁ f) :
  valid_hom₁ (colimit_cocone_comp₁ F_obj @F_hom X f)
| is_limit {𝒟 : Type} [category.{0} 𝒟] (F_obj : 𝒟 → obj₁ 𝒞) 
  (F_hom : Π {X Y : 𝒟}, (X ⟶ Y) → hom₁ (F_obj X) (F_obj Y))
  (cone_obj : obj₁ 𝒞)
  (cone : Π (X : 𝒟), hom₁ cone_obj (F_obj X)) 
  (F_hom_valid : Π {X Y : 𝒟} (f : X ⟶ Y), valid_hom₁ (F_hom f))
  (cone_valid : Π (X : 𝒟), valid_hom₁ (cone X)) :
  valid_hom₁ (is_limit₁ F_obj @F_hom cone_obj cone)
| is_colimit {𝒟 : Type} [category.{0} 𝒟] (F_obj : 𝒟 → obj₁ 𝒞) 
  (F_hom : Π {X Y : 𝒟}, (X ⟶ Y) → hom₁ (F_obj X) (F_obj Y))
  (cocone_obj : obj₁ 𝒞)
  (cocone : Π (X : 𝒟), hom₁ (F_obj X) cocone_obj) 
  (F_hom_valid : Π {X Y : 𝒟} (f : X ⟶ Y), valid_hom₁ (F_hom f))
  (cocone_valid : Π (X : 𝒟), valid_hom₁ (cocone X)) :
  valid_hom₁ (is_colimit₁ F_obj @F_hom cocone_obj cocone)

variable (𝒞)

def obj₂ : Type 1 := { X : obj₁ 𝒞 // valid_obj₁ X }

variable {𝒞}

def hom₂ (X Y : obj₂ 𝒞) : Type 1 := Σ (f : hom₁ X.1 Y.1), valid_hom₁ f

def of_cat_obj₂ (X : 𝒞) : obj₂ 𝒞 :=
⟨of_cat_obj X, valid_obj₁.of_cat_obj _⟩ 

lemma of_cat_obj₂_injective : function.injective (@of_cat_obj₂ 𝒞 _) :=
begin
  intros X Y hXY,
  simp [of_cat_obj₂] at hXY,
  injection hXY,
end

def limit_obj₂ (F_obj : 𝒟 → obj₂ 𝒞) 
  (F_hom : Π {X Y : 𝒟}, (X ⟶ Y) → hom₂ (F_obj X) (F_obj Y)) : obj₂ 𝒞 :=
⟨limit_obj₁ (λ X, (F_obj X).1) (λ X Y f, (F_hom f).1), valid_obj₁.limit_obj _ _ (λ X, (F_obj X).2)⟩

def colimit_obj₂ (F_obj : 𝒟 → obj₂ 𝒞) 
  (F_hom : Π {X Y : 𝒟}, (X ⟶ Y) → hom₂ (F_obj X) (F_obj Y)) : obj₂ 𝒞 :=
⟨colimit_obj₁ (λ X, (F_obj X).1) (λ X Y f, (F_hom f).1), valid_obj₁.colimit_obj _ _ (λ X, (F_obj X).2)⟩

def of_cat_hom₂ {X Y : 𝒞} (f : X ⟶ Y) : hom₂ (of_cat_obj₂ X) (of_cat_obj₂ Y) :=
⟨of_cat_hom₁ f, valid_hom₁.of_cat_hom _⟩ 

def limit_cone_comp₂ (F_obj : 𝒟 → obj₂ 𝒞)
  (F_hom : Π {X Y : 𝒟}, (X ⟶ Y) → hom₂ (F_obj X) (F_obj Y)) (X : 𝒟) 
  {Y : obj₂ 𝒞} (f : hom₂ (F_obj X) Y) :
  hom₂ (limit_obj₂ F_obj @F_hom) Y :=
⟨limit_cone_comp₁ (λ X, (F_obj X).1) (λ X Y f, (F_hom f).1) X f.1, 
  valid_hom₁.limit_cone_comp _ _ _ _ (λ X Y f, (F_hom f).2) f.2⟩

def colimit_cocone_comp₂ (F_obj : 𝒟 → obj₂ 𝒞)
  (F_hom : Π {X Y : 𝒟}, (X ⟶ Y) → hom₂ (F_obj X) (F_obj Y)) (X : 𝒟) 
  {Y : obj₂ 𝒞} (f : hom₂ Y (F_obj X)):
  hom₂ Y (colimit_obj₂ F_obj @F_hom) :=
⟨colimit_cocone_comp₁ (λ X, (F_obj X).1) (λ X Y f, (F_hom f).1) X f.1, 
  valid_hom₁.colimit_cocone_comp _ _ _ _ (λ X Y f, (F_hom f).2) f.2⟩

def is_limit₂ (F_obj : 𝒟 → obj₂ 𝒞) 
  (F_hom : Π {X Y : 𝒟}, (X ⟶ Y) → hom₂ (F_obj X) (F_obj Y))
  (cone_obj : obj₂ 𝒞)
  (cone : Π (X : 𝒟), hom₂ cone_obj (F_obj X)) :
  hom₂ cone_obj (limit_obj₂ F_obj @F_hom) :=
⟨is_limit₁ (λ X, (F_obj X).1) (λ X Y f, (F_hom f).1) cone_obj.1 (λ X, (cone X).1), 
  valid_hom₁.is_limit _ _ _ _ (λ X Y f, (F_hom f).2) (λ X, (cone X).2)⟩

def is_colimit₂ (F_obj : 𝒟 → obj₂ 𝒞) 
  (F_hom : Π {X Y : 𝒟}, (X ⟶ Y) → hom₂ (F_obj X) (F_obj Y))
  (cocone_obj : obj₂ 𝒞)
  (cocone : Π (X : 𝒟), hom₂ (F_obj X) cocone_obj) :
  hom₂ (colimit_obj₂ F_obj @F_hom) cocone_obj  :=
⟨is_colimit₁ (λ X, (F_obj X).1) (λ X Y f, (F_hom f).1) cocone_obj.1 (λ X, (cocone X).1), 
  valid_hom₁.is_colimit _ _ _ _ (λ X Y f, (F_hom f).2) (λ X, (cocone X).2)⟩

@[elab_as_eliminator] protected def hom₂.rec_on 
  {motive : Π {X Y : obj₂ 𝒞} (f : hom₂ X Y), Sort*} {X Y : obj₂ 𝒞} (f : hom₂ X Y)
  (of_cat_hom : Π {X Y : 𝒞} (f : X ⟶ Y), motive (of_cat_hom₂ f))
  (limit_cone_comp : Π {𝒟 : Type} [category 𝒟] (F_obj : 𝒟 → obj₂ 𝒞)
    (F_hom : Π {X Y : 𝒟}, (by exactI X ⟶ Y) → hom₂ (F_obj X) (F_obj Y))
    (ih_F_hom : Π {X Y : 𝒟} (f : by exactI X ⟶ Y), motive (F_hom f))
    (X : 𝒟) {Y : obj₂ 𝒞} (f : hom₂ (F_obj X) Y)
    (ih_f : motive f),
      motive (by exactI limit_cone_comp₂ F_obj @F_hom X f))
  (colimit_cocone_comp : Π {𝒟 : Type} [category 𝒟] (F_obj : 𝒟 → obj₂ 𝒞)
    (F_hom : Π {X Y : 𝒟}, (by exactI X ⟶ Y) → hom₂ (F_obj X) (F_obj Y)) 
    (ih_F_hom : Π {X Y : 𝒟} (f : by exactI X ⟶ Y), motive (F_hom f))
    (X : 𝒟) {Y : obj₂ 𝒞} (f : hom₂ Y (F_obj X))
    (ih_f : motive f),
      motive (by exactI colimit_cocone_comp₂ F_obj @F_hom X f))
  (is_limit : Π {𝒟 : Type} [category 𝒟] (F_obj : 𝒟 → obj₂ 𝒞)
    (F_hom : Π {X Y : 𝒟}, (by exactI X ⟶ Y) → hom₂ (F_obj X) (F_obj Y))
    (ih_F_hom : Π {X Y : 𝒟} (f : by exactI X ⟶ Y), motive (F_hom f)) 
    (cone_obj : obj₂ 𝒞) (cone : Π (X : 𝒟), hom₂ cone_obj (F_obj X))
    (ih_cone : Π (X : 𝒟), motive (cone X)),
      motive (by exactI is_limit₂ F_obj @F_hom cone_obj cone))
  (is_colimit : Π {𝒟 : Type} [category 𝒟] (F_obj : 𝒟 → obj₂ 𝒞)
    (F_hom : Π {X Y : 𝒟}, (by exactI X ⟶ Y) → hom₂ (F_obj X) (F_obj Y)) 
    (ih_F_hom : Π {X Y : 𝒟} (f : by exactI X ⟶ Y), motive (F_hom f))
    (cocone_obj : obj₂ 𝒞) (cocone : Π (X : 𝒟), hom₂ (F_obj X) cocone_obj)
    (ih_cone : Π (X : 𝒟), motive (cocone X)),
      motive (by exactI is_colimit₂ F_obj @F_hom cocone_obj cocone)) :
  motive f :=
begin
  cases X with X hX, cases Y with Y hY,
  cases f with f hf,
  dsimp at f, dsimp at hf,
  revert hX hY,
  refine valid_hom₁.rec_on hf _ _ _ _ _,
  { intros A B g hX hY,
    exact of_cat_hom g },
  { introsI 𝒟 _ F_obj F_hom X Y f F_hom_valid f_valid ih₁ ih₂ hX hY,
    exact @limit_cone_comp _ _ (λ A, ⟨F_obj A, valid_obj₁_limit_obj hX A⟩)
      (λ X Y f, ⟨F_hom f, F_hom_valid f⟩)
      (λ X Y f, ih₁ f _ _) X ⟨Y, hY⟩ ⟨f, f_valid⟩ (ih₂ _ _) },
  { introsI 𝒟 _ F_obj F_hom X Y f F_hom_valid f_valid ih₁ ih₂ hY hX,
    exact @colimit_cocone_comp _ _ (λ A, ⟨F_obj A, valid_obj₁_colimit_obj hX A⟩)
      (λ X Y f, ⟨F_hom f, F_hom_valid f⟩)
      (λ X Y f, ih₁ f _ _) X ⟨Y, hY⟩ ⟨f, f_valid⟩ (ih₂ _ _) },
  { introsI 𝒟 _ F_obj F_hom cone_obj cone F_hom_valid cone_valid ih₁ ih₂ hX hY,
    exact @is_limit 𝒟 _ (λ A, ⟨F_obj A, valid_obj₁_limit_obj hY A⟩)
      (λ X Y f, ⟨F_hom f, F_hom_valid f⟩)
      (λ X Y f, ih₁ f _ _) ⟨cone_obj, hX⟩
      (λ X, ⟨cone X, cone_valid X⟩)
      (λ X, ih₂ X _ _) },
  { introsI 𝒟 _ F_obj F_hom cocone_obj cocone F_hom_valid cocone_valid ih₁ ih₂ hX hY,
    exact @is_colimit 𝒟 _ (λ A, ⟨F_obj A, valid_obj₁_colimit_obj hX A⟩)
      (λ X Y f, ⟨F_hom f, F_hom_valid f⟩)
      (λ X Y f, ih₁ f _ _) ⟨cocone_obj, hY⟩
      (λ X, ⟨cocone X, cocone_valid X⟩)
      (λ X, ih₂ X _ _) }
end

def comp {X Y : obj₂ 𝒞} (f : hom₂ X Y) : Π {Z : obj₂ 𝒞}, hom₂ Y Z → hom₂ X Z :=
hom₂.rec_on f 
  (λ (X Y : 𝒞) (f : X ⟶ Y) (Z : obj₂ 𝒞) (g : hom₂ (of_cat_obj₂ Y) Z), 
    (show ∀ (Y' Z : obj₂ 𝒞), 
      hom₂ Y' Z → Y' = of_cat_obj₂ Y → hom₂ (of_cat_obj₂ X) Z,
      from λ Y' Z g, show Y' = of_cat_obj₂ Y → hom₂ (of_cat_obj₂ X) Z, 
        begin
          refine hom₂.rec_on g _ _ _ _ _,
          { intros A B g h,
            rw [of_cat_obj₂_injective h] at g,
            exact of_cat_hom₂ (f ≫ g) },
          { intros,
            simp [limit_obj₂, of_cat_obj₂, limit_obj₁, *] at * },
          { introsI 𝒟 _ F_obj F_hom ih₁ A B g ih₂ h,
            subst h,
            simp [limit_obj₂, of_cat_obj₂, limit_obj₁, *] at *,
            refine colimit_cocone_comp₂ F_obj _ _ (ih₂ rfl) },
          { introsI 𝒟 _ F_obj F_hom ih₁ cone_obj cone ih₂ h,
            subst h,
            refine is_limit₂ _ _ _ (λ X, ih₂ _ rfl) },
          { intros,
            simp [colimit_obj₂, of_cat_obj₂, colimit_obj₁, *] at * }
       end) (of_cat_obj₂ Y) Z g rfl)
  begin
    introsI 𝒟 _ F_obj F_hom ih₁ A B f ih₂ Z g,
    revert f ih₂,
    refine hom₂.rec_on g _ _ _ _ _,
    { intros C D g f ih₂,
      exact limit_cone_comp₂ _ _ _ (ih₂ (of_cat_hom₂ g)) },
    { introsI 𝓔 _ G_obj G_hom ih₃ C D g ih₄ f ih₂,
      refine limit_cone_comp₂ _ _ _ (ih₂ _),
      exact limit_cone_comp₂ _ _ _ g },
    { introsI ℰ _ G_obj G_hom ih₃ A B g ih₄ f ih₂,
      exact colimit_cocone_comp₂ _ _ _ (ih₄ f @ih₂) },
    { introsI 𝓔 _ G_obj G_hom ih₃ cone_obj cone ih₄ f ih₂,
      refine is_limit₂ _ _ _ (λ X, ih₄ _ (ih₂ _) _), }

  end
  _ 
  _ 
  _

end bicompletion_aux

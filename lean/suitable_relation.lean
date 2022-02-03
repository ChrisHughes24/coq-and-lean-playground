import tactic
import data.setoid.basic
import .scratch

open function

-- Downside, does not send equivalences to equivalences. At least need reflexivity for
-- category structure. Need something more like what they have in structure identity principle.
-- Need to figure out the point of the final condition.
structure suitable (F : Type → Type) 
  (ρ : Π {X Y}, (X → Y → Prop) → (F X → F Y → Prop)) : Prop :=
(symm : Π {X Y : Type} (R : X → Y → Prop) (x : F X) (y : F Y),
  ρ R x y → ρ (swap R) y x)
(trans : Π {X Y Z : Type} (R : X → Y → Prop) (R' : Y → Z → Prop) x y z,
  ρ R x y → ρ R' y z → ρ (λ x z, ∃ y, R x y ∧ R' y z) x z)
(desc : Π {X : Type} (R : setoid X) (s) (h : ρ R.r s s),
  ∃! (s' : F (quotient R)), ρ (λ (x : X) (y : quotient R), quotient.mk x = y) s s')

def functional {X Y : Type} (R : X → Y → Prop) : Prop :=
∀ x, ∃! y, R x y

lemma functional_iff_exists_function {X Y : Type} (R : X → Y → Prop) :
  functional R ↔ ∃ f : X → Y, R = (λ x y, f x = y) :=
begin
  split,
  { intro h,
    cases classical.axiom_of_choice h with f hf,
    dsimp at hf,
    use f,
    ext x y,
    split,
    { intro h,
      exact ((hf _).2 _ h).symm },
    { rintro rfl,
      exact (hf x).1 } },
  { rintros ⟨f, rfl⟩,
    intro x,
    use f x,
    simp } 
end 

def is_equivalence {X Y : Type} (R : X → Y → Prop) :=
functional R ∧ functional (function.swap R)

lemma is_equivalence_iff_exists_equiv {X Y : Type} (R : X → Y → Prop) :
  is_equivalence R ↔ ∃ f : X ≃ Y, R = (λ x y, f x = y) :=
begin
  split,
  { intro h,
    rcases (functional_iff_exists_function _).1 h.1 with ⟨f, rfl⟩,
    rcases (functional_iff_exists_function _).1 h.2 with ⟨g, hg⟩,
    simp only [function.funext_iff, function.swap, eq_iff_iff] at hg,
    refine ⟨⟨f, g, λ x, _, λ y, _⟩, _⟩,
    { rw ← hg },
    { rw hg },
    { refl } },
  { rintros ⟨f, rfl⟩,
    split,
    { rw [functional_iff_exists_function],
      use f },
    { rw [functional_iff_exists_function],
      use f.symm,
      simp [function.swap, function.funext_iff, equiv.symm_apply_eq],
      simp [eq_comm] } }
end
-- Not true
example (F ρ) (hsuit : suitable F ρ) {X Y : Type}
  (R : X → Y → Prop) (h : is_equivalence R) : functional (ρ R) :=
begin
  intro x,


end

-- λ X, X → X does not map reflexive relations to reflexive relations.
example {X Y : Type} (f : X → Y) (hf : surjective f) :
  functional (λ (a : X → X) (b : Y → Y), ∀ x, f (a x) = b (f x)) :=
begin
  intro a,
  have : (λ (a b : X → X), ∀ x y, f x = f y → f (a x) = f (b y)) a a,
  { simp, },
  dsimp only,
  use f ∘ a ∘ surj_inv hf,
  dsimp only,
  split,
  { intro x,
    dsimp, 
    
     },
  { intros b hb,
    funext,
    dsimp,
    rcases hf x with ⟨x, rfl⟩,
    rw ← hb,
     }

end

lemma alt_def (F ρ) (hsuit : suitable F ρ) 
  {X Y : Type} (f : X → Y) (hf : surjective f)
  (hrefl : reflexive (ρ (setoid.ker f).r)) : 
  functional (ρ (λ x y, f x = y)) :=
let R : setoid X := setoid.ker f in
λ x, begin
  cases hsuit.desc R x (hrefl x) with y hy,
  dsimp at

end

 

example (F ρ) (hsuit : suitable F ρ) {X Y : Type}
  (R : X → Y → Prop) (h : square R) : square (ρ R) :=
begin
  intros x₁ x₂ y₁ y₂ h₁ h₂ h₃,
  have := hsuit.trans R (swap R) _ _ _ h₁ (hsuit.symm _ _ _ h₂),
  have := hsuit.trans _ _ _ _ _ this h₃,
  convert this,
  ext x y,
  split,
  { intros,
    use x,
    split,
    { use y,
      split, assumption, assumption },
    { assumption } },
  { rintros ⟨x', ⟨y', hy⟩, hx'y⟩,
    exact h _ _ _ _ hy.1 hy.2 hx'y }
end 

-- structure positive (F : Type → Type)
--   (ρ : Π {X Y}, (X → Y → Prop) → (F X → F Y → Prop)) : Prop :=
-- (refl : Π {X : Type}, ρ (@eq X) = eq)
-- (rev_trans : Π {X Y Z} (R : X → Y → Prop) (R' : Y → Z → Prop),
--   ρ R x z → ρ (λ x z, ∃ y, R x y ∧ R' y z) x z)

example : suitable (λ X : Type, X → X) (λ X Y R f g, ∀ x y, R x y → R (f x) (g y)) :=
{ symm := λ X Y R x y h y x, h x y,
  trans := λ X Y Z R R' a b c h₁ h₂ x z, 
    begin
      rintros ⟨y, hxy, hyz⟩,
      use b y,
      split,
      { exact h₁ _ _ hxy },
      { exact h₂ _ _ hyz }
    end,
  desc := λ X R a h, 
    ⟨@quotient.map _ _ R R a h, begin
      dsimp,
      split,
      { rintros x y rfl,
        refl },
      { intros b h,
        funext x,
        resetI,
        refine quotient.induction_on x _,
        intro x,
        rw ← h x _ rfl,
        refl } 
    end⟩ }

example {X Y : Type} (R : X → Y → Prop) (h : square R) : 
  square (λ (f : (X → X) → X) (g : (Y → Y) → Y), ∀ (a : X → X) (b : Y → Y),
    (∀ x y, R x y → R (a x) (b y)) → R (f a) (g b)) :=
λ f₁ f₂ g₁ g₂ h₁ h₂ h₃ a b hab, begin
  dsimp at *,
  apply h,
  apply h₁,
  apply hab,
  apply h₂,
  apply hab,
  apply h₃, 
  apply hab
end

example : suitable (λ X, (X → X) → X) 
  (λ X Y R f g, ∀ (a : X → X) (b : Y → Y), (∀ x y, R x y → R (a x) (b y)) → R (f a) (g b)) :=
{ symm := λ X Y R f g h₁ a b h₂, h₁ _ _ (λ x y, h₂ y x),
  trans := λ X Y Z R R' f g i h₁ h₂ a b h₃, begin
    dsimp at *,
  end }

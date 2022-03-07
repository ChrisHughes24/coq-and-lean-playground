import tactic
import order.galois_connection

def hProp := { T : Type // ∀ x y : T, x = y }

structure powerset_adjunction (X Y : Type) :=
( preim : (set Y) → (set X) )
( im : (set X) → (set Y) )
( adj : galois_connection im preim )

example {X Y : Type} (f : X → Y) (s t : set Y) : 
  f ⁻¹' (s ∩ t) = (f ⁻¹' s) ∩ (f ⁻¹' t) := rfl

example : powerset_adjunction ℕ ℕ :=
{ preim := λ _, set.univ,
  im := λ _, ∅,
  adj := λ _, by simp }

structure powerset_adjunction2 (X Y : Type) :=
( preim₁ : set (Y × Y) → set (X × Y) )
( im₁    : set (X × Y) → set (Y × Y) )
( preim₂ : set (X × Y) → set (X × X) )
( im₂    : set (X × X) → set (X × Y) )
( adj₁   : galois_connection im₁ preim₁ )
( adj₂   : galois_connection im₂ preim₂ )
( swap   : ∀ s, (im₂ ∘ preim₂) s ⊆ (preim₁ ∘ im₁) s )


example {X Y : Type} (f : X → Y) (s : set (X × Y)) :
  prod.map (id : X → X) f '' (prod.map id f ⁻¹' s) ≤ 
  prod.map f (id : Y → Y) ⁻¹' (prod.map f id '' s) :=
begin
  intro x,
  cases x with x y,
  { simp,
    rintros x₁ x₂ h rfl rfl,
    use x₁,
    simp * }
end

example {X Y : Type} (h : powerset_adjunction2 X Y) (x : X) : Y :=
begin
  have := h.im₂ {y : X × X | y.1 = y.2}, 

end


structure powerset_adjunction (X Y : Type) :=
( preim : (Y → hProp) → (X → hProp) )
( im : (X → hProp) → (Y → hProp) )
( adj : ∀ (s : X → hProp) (t : Y → hProp), 
    (∀ x, (s x).1 → (preim t x).1) ≃ (∀ x, (im s x).1 → (t x).1) )

example {X Y : Type} (h : powerset_adjunction X Y) (x : X) : Y :=
begin
  cases h with preim im adj,
  have := adj (λ y : X, ⟨plift (x = y), by simp⟩)
    (λ y, nonempty ),

end
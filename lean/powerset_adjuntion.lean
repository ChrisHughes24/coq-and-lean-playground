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
( preim : Π {Z : Type}, (set (Y × Z)) → (set (X × Z)) )
( im : Π {Z : Type}, (set (X × Z)) → (set (Y × Z)) )
( adj : Π {Z : Type}, galois_connection (@im Z) preim )

example : powerset_adjunction2 ℕ ℕ :=
{ preim := λ _ _, set.univ,
  im := λ _ _, ∅,
  adj := λ _ _, by simp }


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
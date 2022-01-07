import tactic

universes u v

structure edge : Type (u+1) :=
( left : Type u )
( right : Type u )
( out : Type u )
( aleft : left → out )
( aright : right → out )

namespace edge

structure pullback (E : edge.{u}) : Type u :=
( l : E.left )
( r : E.right )
( eq : E.aleft l = E.aright r )

-- constant parametricity {Γ : Type u} (F : Γ → Type v) : Π γ₁ γ₂ : Γ, edge (F γ₁) (F γ₂)

-- @[simp] axiom parametricity_pi {Γ : Type u} (F : Γ → Type v) (G : Π {γ : Γ}, F γ → Type) 
--   (γ₁ γ₂ : Γ) : parametricity (λ γ : Γ, Π x : F γ, G x) γ₁ γ₂ =
--   { out := Π x : (parametricity F γ₁ γ₂).pullback, 
--       (parametricity (λ s : Σ γ, F γ, G s.2) ⟨γ₁, x.l⟩ ⟨γ₂, x.r⟩).out,
--     aleft := λ p pb, (parametricity (λ s : Σ γ, F γ, G s.2) ⟨γ₁, pb.l⟩ ⟨γ₂, pb.r⟩).aleft (p pb.l),
--     aright := λ p pb, (parametricity (λ s : Σ γ, F γ, G s.2) ⟨γ₁, pb.l⟩ ⟨γ₂, pb.r⟩).aright (p pb.r) }

def thing (X : Type) : Type :=
Π (f : Π x : X, {l : list X // x ∈ l}) (x : X), {l : list (list X) // (f x).1 ∈ l}

def thing' (E : edge) : edge :=
{ left := thing E.left,
  right := thing E.right,
  out := λ  }


end edge
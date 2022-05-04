import tactic

noncomputable theory

variables {R S T : Type} [comm_ring R] [comm_ring S] [comm_ring T]

constant polynomial (R : Type) [comm_ring R] : Type

@[instance] constant polynomial.comm_ring : comm_ring (polynomial R)

namespace polynomial

constant C : R →+* polynomial R

constant X : polynomial R

constant eval₂ (f : R →+* S) (x : S) : polynomial R →+* S

@[simp] constant eval₂_X (f : R →+* S) (x : S) : eval₂ f x X = x

@[simp] constant eval₂_comp_C (f : R →+* S) (x : S) : (eval₂ f x).comp C = f

@[simp] constant eval₂_C (f : R →+* S) (x : S) (r : R): eval₂ f x (C r) = f r

constant hom_ext {f g : polynomial R →+* S} (h1 : f X = g X) 
  (h2 : f.comp C = g.comp C) : f = g

def map (f : R →+* S) : polynomial R →+* polynomial S :=
eval₂ (C.comp f) X

example (f : R →+* S) (g : S →+* T) (x : T) : (eval₂ g x).comp (map f) = eval₂ (g.comp f) x :=
hom_ext (by simp [ring_hom.comp_assoc, map]) 
  -- begin
  --   ext,
  --   simp [map]
  -- end
  begin
    rw [map, eval₂_comp_C, ring_hom.comp_assoc, eval₂_comp_C,
      ← ring_hom.comp_assoc, eval₂_comp_C],
  end

end polynomial
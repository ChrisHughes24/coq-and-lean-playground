import tactic
import algebra.ring.prod

noncomputable theory

variables {σ R S T : Type} [comm_ring R] [comm_ring S] [comm_ring T]

constant mv_polynomial (R : Type) [comm_ring R] (σ : Type) : Type

@[instance] constant mv_polynomial.comm_ring : comm_ring (mv_polynomial R σ)

namespace mv_polynomial

constant C : R →+* mv_polynomial R σ

constant X : σ → mv_polynomial R σ

constant eval₂ (f : R →+* S) (x : σ → S) : mv_polynomial R σ →+* S

@[simp] constant eval₂_comp_X (f : R →+* S) (x : σ → S) : eval₂ f x ∘ X = x

@[simp] constant eval₂_comp_C (f : R →+* S) (x : σ → S) : (eval₂ f x).comp C = f

@[simp] constant eval₂_X (f : R →+* S) (x : σ → S) (i : σ): eval₂ f x (X i) = x i

@[simp] constant eval₂_C (f : R →+* S) (x : σ → S) (r : R) : eval₂ f x (C r) = f r

@[ext] constant hom_ext {f g : mv_polynomial R σ →+* S} (h1 : f ∘ X = g ∘ X) 
  (h2 : f.comp C = g.comp C) : f = g

def map (f : R →+* S) : mv_polynomial R σ →+* mv_polynomial S σ :=
eval₂ (C.comp f) X

@[ext] lemma sum.hom_ext {α β γ : Type} {f g : α ⊕ β → γ} 
  (h1 : f ∘ sum.inl = g ∘ sum.inl)
  (h1 : f ∘ sum.inr = g ∘ sum.inr) : f = g :=
begin
  ext x, cases x; simp [function.funext_iff, *] at *,
end

@[simp] lemma sum.elim_comp_inl {α β γ : Type} {f : α  → γ} {g : β → γ} :
  sum.elim f g ∘ sum.inl = f :=
begin
  ext x, simp,
end

@[simp] lemma sum.elim_comp_inr {α β γ : Type} {f : α  → γ} {g : β → γ} :
  sum.elim f g ∘ sum.inr = g :=
begin
  ext x, simp,
end

example {α β : Type} : mv_polynomial R (α ⊕ β) ≃+* mv_polynomial (mv_polynomial R α) β :=
ring_equiv.of_hom_inv
  (eval₂ (C.comp C) (sum.elim (C ∘ X) X))
  (eval₂ (eval₂ C (X ∘ sum.inl)) (X ∘ sum.inr))
  begin
    ext; simp,
  end
  begin
    ext; simp,
  end
  -- (hom_ext (sum.hom_ext begin
  --   rw [ring_hom.coe_comp, ← function.comp.assoc _ _ sum.inl, 
  --     function.comp.assoc _ _ X, eval₂_comp_X, function.comp.assoc,
  --     sum.elim_comp_inl, ← function.comp.assoc,
  --     ← ring_hom.coe_comp, eval₂_comp_C, eval₂_comp_X],
  --   refl  
  -- end
  -- begin
  --   rw [ring_hom.coe_comp, 
  --     function.comp.assoc _ _ X, eval₂_comp_X, function.comp.assoc,
  --     sum.elim_comp_inr, eval₂_comp_X],
  --   refl  
  -- end) 
  -- begin
  --   rw [ring_hom.comp_assoc, eval₂_comp_C, ← ring_hom.comp_assoc,
  --     eval₂_comp_C, eval₂_comp_C, ring_hom.id_comp]
  -- end)
  -- (hom_ext 
  --   begin
  --     rw [ring_hom.coe_comp, function.comp.assoc _ _ X,
  --       eval₂_comp_X, ← function.comp.assoc, eval₂_comp_X, sum.elim_comp_inr],
  --    refl,
  --   end
  --   (hom_ext begin
  --     rw [ring_hom.id_comp, ring_hom.comp_assoc, eval₂_comp_C,
  --       ring_hom.coe_comp, function.comp.assoc, eval₂_comp_X,
  --       ← function.comp.assoc, eval₂_comp_X, sum.elim_comp_inl]
  --   end begin
  --     rw [ring_hom.comp_assoc _ (eval₂ _ _), eval₂_comp_C,
  --       ring_hom.comp_assoc, eval₂_comp_C, eval₂_comp_C,
  --       ring_hom.id_comp],
  --   end))

end mv_polynomial
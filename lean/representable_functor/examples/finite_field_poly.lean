import .polynomial_eval
import algebra.ring.equiv

constant rquotient (R : Type) [comm_ring R] {ι : Type} (I : ι → R) : Type

namespace rquotient

variables {R : Type} [comm_ring R] {ι : Type} (I : ι → R)

@[instance] protected constant comm_ring : comm_ring (rquotient R I)

constant of : R →+* rquotient R I

constant of_I (i : ι) : of I (I i) = 0

variables {S : Type} [comm_ring S] (f : R →+* S) (hf : ∀ i : ι, f (I i) = 0)

include hf

constant desc : rquotient R I →+* S

omit hf

@[simp] constant desc_comp_of : (desc I f hf).comp (of I) = f

@[simp] lemma desc_of (x : R) : desc I f hf (of I x) = f x := 
by conv_rhs { rw [← desc_comp_of I f hf] }; refl

@[ext] constant hom_ext {f g : rquotient R I →+* S} 
  (h : f.comp (of I) = g.comp (of I)) : f = g

end rquotient

open polynomial

noncomputable example : rquotient (polynomial (rquotient ℤ (λ _ : unit, 3))) 
  (λ _ : unit, X^2 + 1) ≃+*
  rquotient (rquotient (polynomial ℤ) (λ _ : unit, X^2 + 1)) 
    (λ _ : unit, 3) := 
@ring_equiv.of_hom_inv 
  _
  _
  (rquotient (polynomial (rquotient ℤ (λ _ : unit, 3))) 
    (λ _ : unit, X^2 + 1) →+*
    rquotient (rquotient (polynomial ℤ) (λ _ : unit, X^2 + 1)) 
    (λ _ : unit, 3))
  (rquotient (rquotient (polynomial ℤ) (λ _ : unit, X^2 + 1)) 
    (λ _ : unit, 3) →+*
    rquotient (polynomial (rquotient ℤ (λ _ : unit, 3))) 
    (λ _ : unit, X^2 + 1))
  _
  _
  _
  _
  (rquotient.desc _ 
    (polynomial.eval₂ (rquotient.desc _ (int.cast_ring_hom _) 
      (λ _, begin simp, rw [← rquotient.of_I _ ()], simp, end)) 
      (rquotient.of _ (rquotient.of _ X))) 
      begin
        simp,
        rw [← map_zero (rquotient.of (λ _ : unit, (3 : 
          rquotient (polynomial ℤ) (λ _ : unit, X^2 + 1)))),
          ← rquotient.of_I _ ()],
        simp
      end) 
  (rquotient.desc _ 
    (rquotient.desc _ 
      (polynomial.eval₂ (int.cast_ring_hom _) 
        (rquotient.of _ X)) 
      (λ _, begin
        simp,
        rw [← rquotient.of_I _ ()],
        simp,
        
      end)) 
    (λ _, begin
      simp,
      rw [← map_zero (rquotient.of (λ _ : unit, 
        (X^2 + 1 : polynomial (rquotient ℤ (λ _ : unit, 3))))),
        ← map_zero (@polynomial.C (rquotient ℤ (λ _ : unit, 3)) _),
        ← rquotient.of_I _ ()],
      simp
    end)) 
  (by ext; simp)
  (by ext; simp)
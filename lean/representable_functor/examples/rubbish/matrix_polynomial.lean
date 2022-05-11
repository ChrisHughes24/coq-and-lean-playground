import tactic
import linear_algebra.tensor_algebra.basic

instance pi.linear_map_module (S R : Type) [semiring S] [semiring R] (ι : Type)
  (M : ι → Type) [Π (i : ι), add_comm_monoid (M i)]
  [Π (i : ι), module R (M i)]
  (N : Type)
  [add_comm_monoid N]
  [module R N]
  [module S N] [smul_comm_class R S N] : module S (Π i : ι, (M i →ₗ[R] N)) :=
@pi.module ι (λ i, (M i →ₗ[R] N)) S _ _ (λ i, linear_map.module)

variables (R : Type) [comm_ring R]

constant coproduct {ι : Type} (M : ι → Type) [Π i, add_comm_group (M i)] 
  [Π i, module R (M i)] : Type

variables {R}

namespace coproduct

variables {ι : Type} {M : ι → Type} [Π i, add_comm_group (M i)] [Π i, module R (M i)]

@[instance] protected constant add_comm_group : 
  add_comm_group (coproduct R M)

@[instance] protected constant module : module R (coproduct R M)

constant of (i : ι) : M i →ₗ[R] coproduct R M

variables {N : Type} [add_comm_group N] [module R N]

set_option class.instance_max_depth 1000

constant extend : (Π i : ι, (M i →ₗ[R] N)) →ₗ[R] (coproduct R M →ₗ[R] N)

@[simp] constant extend_comp_of (i : ι) (f : Π i, M i →ₗ[R] N) : (extend f).comp (of i) = f i

@[simp] lemma extend_of (i : ι) (f : Π i, M i →ₗ[R] N) (x : M i) : 
  extend f (of i x) = f i x :=
by rw [← extend_comp_of i f]; refl

@[ext] constant hom_ext {f g : coproduct R M →ₗ[R] N} 
  (h : ∀ i, f.comp (of i) = g.comp (of i)) :
  f = g 

end coproduct

section pi




end pi

variables {M : Type} [add_comm_group M] [module R M]

def poly_mul (mul : M →ₗ[R] M →ₗ[R] M) : 
  coproduct R (λ n : ℕ, M) →ₗ[R] coproduct R (λ n : ℕ, M) →ₗ[R] coproduct R (λ n : ℕ, M) :=
coproduct.extend (λ n, begin
  refine linear_map.lcomp R _ _ _,
  
end)

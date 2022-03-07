import linear_algebra.finsupp

variables {R α M N P : Type} [comm_ring R]
variables [add_comm_group M] [module R M]
variables [add_comm_group N] [module R N]
variables [add_comm_group P] [module R P]

noncomputable theory

namespace poly_example

variables (R α)

@[derive add_comm_group, derive module R]
def free_module : Type := finsupp α R

variables {R α}

def lift (f : α → M) : free_module R α →ₗ[R] M :=
finsupp.total _ _ _ f

def X (a : α) : free_module R α := finsupp.single a 1

@[simp] lemma lift_X (f : α → M) (a : α) : lift f (X a : free_module R α) = f a :=
by simp [lift, X]

@[ext] lemma hom_ext {f g : free_module R α →ₗ[R] M} (h : ∀ a, f (X a) = g (X a)) : f = g :=
by ext; simp [*, X] at *

@[simp] lemma lift_comp (f : M →ₗ[R] N) (g : α → M) :
  f.comp (lift g) = lift (λ x, f (g x)) :=
by ext; simp

@[simp] lemma lift_comp_apply (f : M →ₗ[R] N) (g : α → M) (x : free_module R α) :
  f (lift g x) = lift (λ x, f (g x)) x :=
by rw [← lift_comp]; refl

def lcomp : (M →ₗ[R] N) →ₗ[R] (P →ₗ[R] M) →ₗ[R] (P →ₗ[R] N) :=
{ to_fun := λ f,
  { to_fun := linear_map.comp f,
    map_add' := by intros; ext; simp,
    map_smul' := by intros; ext; simp },
  map_add' := by intros; ext; simp,
  map_smul' := by intros; ext; simp }

def lcompop : (P →ₗ[R] M) →ₗ[R] (M →ₗ[R] N) →ₗ[R] (P →ₗ[R] N) :=
{ to_fun := λ f,
  { to_fun := λ g, linear_map.comp g f,
    map_add' := by intros; ext; simp,
    map_smul' := by intros; ext; simp },
  map_add' := by intros; ext; simp,
  map_smul' := by intros; ext; simp }

def swap : (M →ₗ[R] N →ₗ[R] P) →ₗ[R] (N →ₗ[R] M →ₗ[R] P) :=
{ to_fun := λ f,
  { to_fun := λ n,
    { to_fun := λ m, f m n,
      map_add' := λ _ _, by rw [f.map_add]; refl,
      map_smul' := λ _ _, by rw [f.map_smul]; refl, },
    map_add' := λ _ _, by simp only [(f _).map_add]; refl,
    map_smul' := λ _ _, by simp only [(f _).map_smul]; refl },
  map_add' := λ _ _, rfl,
  map_smul' := λ _ _, rfl }

@[simp] lemma lift_apply (f : α → M →ₗ[R] N) (x : free_module R α) (m : M) :
  lift f x m = lift (λ a, f a m) x :=
show swap (lift f) m x = lift (λ a, f a m) x,
begin
  refine congr_fun _ _,
  refine congr_arg _ _,
  ext,
  simp [swap]
end

variable {M}

attribute [irreducible] free_module lift X

def mul : free_module R ℕ →ₗ[R] free_module R ℕ →ₗ[R] free_module R ℕ :=
lift (λ n, lift (λ m, X (n + m)))

-- free_module R ℕ →ₗ[R] free_module R ℕ →ₗ[R] free_module R ℕ →ₗ[R] free_module R ℕ

lemma mul_assoc (p q r : free_module R ℕ) : mul (mul p q) r = mul p (mul q r) :=
-- by simp [mul, add_assoc]

-- #print mul_assoc

show (lcomp (@mul R _)).comp mul p q r = (lcompop (@mul R _)).comp (lcomp.comp mul) p q r,
--by congr' 3; ext; simp [lcomp, lcompop, mul, add_assoc]
begin
  congr' 3,
  apply hom_ext,
  intro,
  apply hom_ext,
  intro,
  apply hom_ext,
  intro,
  dsimp [lcomp, lcompop, mul],
  rw [lift_X, lift_X, lift_X, lift_X, lift_X, lift_X, lift_X, add_assoc],
end

lemma mul_comm (p q : free_module R ℕ) : mul p q = mul q p :=
show mul p q = swap mul p q,
begin
  refine linear_map.congr_fun _ _,
  refine linear_map.congr_fun _ _,
  ext,
  simp [mul, swap, add_comm],

end

end

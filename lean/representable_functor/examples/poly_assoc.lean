import linear_algebra.finsupp

variables {R α β γ M N P : Type} [comm_ring R]
variables [add_comm_group M] [module R M]
variables [add_comm_group N] [module R N]
variables [add_comm_group P] [module R P]

noncomputable theory

namespace poly_example

variables (R α)

@[derive add_comm_group, derive module R]
def free_module : Type := finsupp α R

variables {R α}

def extend (f : α → M) : free_module R α →ₗ[R] M :=
finsupp.total _ _ _ f

def X (a : α) : free_module R α := finsupp.single a 1

@[simp] lemma extend_X (f : α → M) (a : α) : extend f (X a : free_module R α) = f a :=
by simp [extend, X]

@[simp] lemma extend_X' (f : free_module R α →ₗ[R] M) : extend (f ∘ X) = f :=
by ext; simp [extend, X]

@[ext] lemma hom_ext {f g : free_module R α →ₗ[R] M} (h : ∀ a, f (X a) = g (X a)) : f = g :=
by rw [← extend_X' f, function.comp]; simp only [h, extend_X']

variable (R)

def map (f : α → β) : free_module R α →ₗ[R] free_module R β :=
extend (X ∘ f)

variable {R}
lemma map_id  : map R (id : α → α) = linear_map.id :=
hom_ext (λ a, by rw [map, extend_X]; refl)

lemma map_comp (f : α → β) (g : β → γ) : map R (g ∘ f) = (map R g).comp (map R f) :=
hom_ext begin
  rw [map, map, map],
  intro i,
  rw [extend_X, linear_map.comp_apply, extend_X, extend_X],
end

@[simp] lemma extend_comp (f : M →ₗ[R] N) (g : α → M) :
  f.comp (extend g) = extend (λ x, f (g x)) :=
by ext; simp only [linear_map.coe_comp, function.comp_app, extend_X]

@[simp] lemma extend_comp_apply (f : M →ₗ[R] N) (g : α → M) (x : free_module R α) :
  f (extend g x) = extend (λ x, f (g x)) x :=
by rw [← extend_comp]; refl

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



@[simp] lemma extend_apply (f : α → M →ₗ[R] N) (x : free_module R α) (m : M) :
  extend f x m = extend (λ a, f a m) x :=
show swap (extend f) m x = extend (λ a, f a m) x,
begin
  refine congr_fun _ _,
  refine congr_arg _ _,
  ext,
  simp [swap]
end

variable {M}

attribute [irreducible] free_module extend X

def mul : free_module R ℕ →ₗ[R] free_module R ℕ →ₗ[R] free_module R ℕ :=
extend (λ n, extend (λ m, X (n + m)))

-- free_module R ℕ →ₗ[R] free_module R ℕ →ₗ[R] free_module R ℕ →ₗ[R] free_module R ℕ

lemma mul_assoc (p q r : free_module R ℕ) : mul (mul p q) r = mul p (mul q r) :=
--by simp only [mul, add_assoc, extend_apply, extend_comp_apply, extend_X]

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
  dsimp [mul, lcomp, lcompop],
  rw [extend_X, extend_X, extend_X, extend_X, extend_X, extend_X, extend_X, add_assoc],
end

lemma mul_comm (p q : free_module R ℕ) : mul p q = mul q p :=
show mul p q = swap mul p q,
begin
  refine linear_map.congr_fun _ _,
  refine linear_map.congr_fun _ _,
  ext,
  simp [mul, swap, add_comm]
end



@[derive module R] def matrix : Type := free_module

end

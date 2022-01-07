import tactic

structure Group : Type 1 := 
( type : Type  )
( one : type )
( mul : type → type → type )
( inv : type → type )

instance (G : Group) : has_mul G.type := ⟨G.mul⟩
instance (G : Group) : has_one G.type := ⟨G.one⟩
instance (G : Group) : has_inv G.type := ⟨G.inv⟩

structure edge (G H : Group) : Type :=
( R : G.type → H.type → Prop )
( one : R 1 1 )
( inv : Π {a b}, R a b → R (a⁻¹) (b⁻¹) )
( mul : Π {a₁ a₂ b₁ b₂}, R a₁ b₁ → R a₂ b₂ → R (a₁ * a₂) (b₁ * b₂) )

def edge_to_Group {G H : Group} (E : edge G H) : Group :=
{ type := Σ' (x : G.type) (y : H.type), E.R x y,
  one := ⟨1, 1, E.one⟩,
  mul := λ x y, ⟨x.1 * y.1, x.2.1 * y.2.1, E.mul x.2.2 y.2.2⟩,
  inv := λ x, ⟨x.1⁻¹, x.2.1⁻¹, E.inv x.2.2⟩ }

def id_edge (G : Group) : edge G G :=
{ R := λ x y, x = y,
  one := rfl,
  inv := by intros; simp *,
  mul := by intros; simp * }

structure to_edge_edge {G₁ G₂ H₁ H₂ : Group} (E₁ : edge G₁ H₁) (E₂ : edge G₂ H₂) 
  (Eg : edge G₁ G₂) (Eh : edge H₁ H₂) : Type :=
( R : Π g₁ g₂ h₁ h₂, E₁.R g₁ h₁ → E₂.R g₂ h₂ → Eg.R g₁ g₂ → Eh.R h₁ h₂ → Prop )
( one : R 1 1 1 1 E₁.one E₂.one Eg.one Eh.one )
( inv : Π g₁ g₂ h₁ h₂ p₁ p₂ p₃ p₄, R g₁ g₂ h₁ h₂ p₁ p₂ p₃ p₄ → 
    R (g₁⁻¹) (g₂⁻¹) (h₁⁻¹) (h₂⁻¹) (E₁.inv p₁) (E₂.inv p₂) (Eg.inv p₃) (Eh.inv p₄) )
( mul : Π g₁ g₂ h₁ h₂ p₁ p₂ p₃ p₄ g₁' g₂' h₁' h₂' p₁' p₂' p₃' p₄', 
  R (g₁ * g₁') (g₂ * g₂') (h₁ * h₁') (h₂ * h₂') 
  (E₁.mul p₁ p₁') (E₂.mul p₂ p₂') (Eg.mul p₃ p₃') (Eh.mul p₄ p₄') )

structure hom (G H : Group) : Type 1 :=
( e : edge G H )
( unique : ∀ (K : Group) (R : edge G K), 
    Σ' (E : edge H K) (h : to_edge_edge e (id_edge K) R E),
    ∀ (E' : edge H K) (h' : to_edge_edge e (id_edge K) R E'), 
    E = E' ∧ h == h' )


def to_hom (G H : Group) (f : G.type → H.type) (h1 : f 1 = 1) (hinv : ∀ a, f (a⁻¹) = (f a)⁻¹) 
  (hmul : ∀ a b, f (a * b) = f a * f b) : hom G H :=
{ e := { R := λ x y, f x = y, one := by simp *, mul := by simp * {contextual := tt},
            inv := by simp * { contextual := tt } },
  unique := λ K R, ⟨{ R := λ h k, ∃ g : G.type, f g = h ∧ R.R g k,
       one := ⟨1, by simp [*, R.one]⟩,
       mul := λ a₁ a₂ b₁ b₂, begin
         simp { contextual := tt },
         intros,
         use x * x_1,
         simp *,
         apply R.mul; simp *,    
       end,
       inv := λ a b,begin
         simp { contextual := tt },
         intros,
         use x⁻¹,
         simp *,
         apply R.inv; simp *,    
       end}, ⟨by intros; exact true, by intros; trivial, by intros; trivial, by intros; trivial⟩, 
         begin
           assume E' h',
           cases E', cases h',
           simp [function.funext_iff],
           split,
         end⟩ } 

inductive group_gen {G : Group} (g : G.type) : edge G H :=


def to_function {G H : Group} (f : hom G H) (x : G.type) : H.type :=
begin
  have := f.unique H f.e,

end


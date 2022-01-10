import tactic

universes u v

structure edge : Type 1 :=
( op_type : Type )
( type : Type )
( R : op_type → type → Prop )

namespace edge

def op (E : edge) : edge :=
{ op_type := E.type,
  type := E.op_type,
  R := λ x y, E.R y x }

structure hom (X Y : edge) : Type :=
( op_hom : Y.op_type → X.op_type )
( hom : X.type → Y.type )
( adj : ∀ (x : X.type) (y : Y.op_type), X.R (op_hom y) x ↔ Y.R y (hom x) )

def functional (E : edge) : Prop :=
∃ f : E.op_type → E.type, ∀ x y, E.R x y ↔ f x = y

def id (X : edge) : hom X X :=
{ op_hom := id,
  hom := id,
  adj := λ _ _, iff.rfl }

def comp {X Y Z : edge} (f : hom Y Z) (g : hom X Y) : hom X Z :=
{ op_hom := g.op_hom ∘ f.op_hom,
  hom := f.hom ∘ g.hom,
  adj := λ x y, by simp [f.adj, g.adj] }

def pullback (E : edge) : Type := { x : E.op_type × E.type // E.R x.1 x.2 }

def id_edge (X : Type) : edge :=
{ op_type := X,
  type := X,
  R := eq }

def of_fun {X Y : Type} (f : X → Y) : edge :=
{ op_type := X,
  type := Y,
  R := λ x y, f x = y }

def id_to_of_fun {X Y : Type} (f : X → Y) : hom (id_edge Y) (of_fun f) :=
{ op_hom := f,
  hom := _root_.id,
  adj := begin
    intros, refl,
  end }

-- def thing (X : Type) : Type :=
-- Π (f : Π x : X, {l : list X // x ∈ l}) (x : X), {l : list (list X) // (f x).1 ∈ l}

-- inductive list.rel_lift {A B : Type} (R : A → B → Prop) : list A → list B → Prop
-- | nil : list.rel_lift [] []
-- | cons : ∀ a b l₁ l₂, list.rel_lift l₁ l₂ → R a b → list.rel_lift (a :: l₁) (b::l₂)

-- def thing' (E : edge) : Type := 
-- Π (f : Π x : E.type, { l : list E.op_type // ∃ (y : E.op_type) (h : E.R y x), y ∈ l }) (x : E.op_type),
--   {l : list (list E.type) // ∃ (y : E.type) (h : E.R x y) 
--     (l' : list E.type) (h : list.rel_lift E.R (f y).1 l'), l' ∈ l  }

-- def thing'_map {X Y : edge} (f : hom X Y) (t : thing' X) : thing' Y :=
-- λ g y, begin
--   dsimp only [thing', thing] at t,
--   let g' : Π (x : X.type), { l : list X.op_type // ∃ (y : X.op_type) (h : X.R y x ), y ∈ l },
--     from λ x, ⟨(g (f.hom x)).1.map f.op_hom, begin
--       rcases (g (f.hom x)).2 with ⟨y, hy₁, hy₂⟩,
--       existsi f.op_hom y,
--       rw [f.adj],
--       use hy₁,
--       rw [list.mem_map],
--       use y,
--       simpa using hy₂,
--     end⟩,
--   let l := t g' (f.op_hom y),
--   fsplit,
--   exact l.1.map (list.map f.hom),
--   rcases l.2 with ⟨x, hxy, l', hl', hll⟩,
--   use f.hom x,
--   rw ← f.adj,
--   use hxy,
--   use l'.map f.hom,
--   split,
--   intros,
--   clear_except hl' ,
--   dsimp [g'] at hl',
--   simp,
--   generalize hk : (↑(g (f.hom x)) : list _) = k,
--   rw hk at hl',
--   clear_except hl',
--   generalize hm : list.map f.op_hom k = m,
--   rw hm at hl', 
--   induction hl' generalizing k,
--   { simp * at *, constructor },
--   { cases k,
--     simp * at *,
--     simp at hm,
--     cases hm with hm1 hm2,
--     subst hm1,
--     constructor,
--     apply hl'_ih,
--     assumption,
--     rwa ← f.adj },
--   simp,
--   use l',
--   simp * at *
-- end

-- @[simp] lemma list.map_id {A : Type} : list.map (_root_.id : A → A) = _root_.id := 
-- by funext; simp

-- lemma list.map_comp {A B C : Type} (f : A → B) (g : B → C) : 
--   list.map (g ∘ f) = list.map g ∘ list.map f := 
-- by funext; simp

-- lemma thing'_map_id (X : edge) : thing'_map (edge.id X) = _root_.id :=
-- begin
--   cases X, funext, simp [thing'_map],
--   refine subtype.ext _,
--   dsimp [id] at *,
--   rw [list.map_id, list.map_id],
--   simp,
--   congr,
--   simp,
--   simp,
--   simp,
--   simp,
--   simp,
-- end

-- lemma thing'_map_comp  (X Y Z : edge) (f : hom X Y) (g : hom Y Z) : 
--   thing'_map (comp g f) =  thing'_map g ∘ thing'_map f :=
-- begin
--   cases X, cases Y, cases Z, cases f, cases g, funext, simp [thing'_map, comp],
--   congr,
--   simp,
--   simp,
--   simp,
--   simp,
--   simp,
-- end

def id2 (E : edge) : Type := E.type

def id2_map {E₁ E₂ : edge} (f : hom E₁ E₂) : id2 E₁ → id2 E₂ := f.hom

lemma id2_map_id (E : edge) : id2_map (id E) = _root_.id := rfl

lemma id2_map_comp (E₁ E₂ E₃ : edge) (f : hom E₁ E₂) (g : hom E₂ E₃) : 
  id2_map (comp g f) = id2_map g ∘ id2_map f := rfl

def set2 (E : edge) : Type := E.op_type → Prop

def set2_map {E₁ E₂ : edge} (f : hom E₁ E₂) : set2 E₁ → set2 E₂ := (∘ f.op_hom)

lemma set2_map_id (E : edge) : set2_map (id E) = _root_.id := rfl

lemma set2_map_comp (E₁ E₂ E₃ : edge) (f : hom E₁ E₂) (g : hom E₂ E₃) : 
  set2_map (comp g f) = set2_map g ∘ set2_map f := rfl

structure group2 (E : edge) : Type :=
( one : E.type )
( inv : E.op_type → E.type )
( mul : E.op_type → E.op_type → E.type )
( one_mul : ∀ (x : E.op_type) (one' : E.op_type) (h1 : E.R one' one), mul one' x = one  )
(inv_mul : ∀ (x : E.op_type), ∀ (inv_y : E.op_type) (hi : E.R inv_y (inv x)), mul inv_y x = one )
( mul_assoc : ∀ (x y z : E.op_type),
    ∀ (mul_y_z : E.op_type) (mul_x_y : E.op_type) (hyz : E.R mul_y_z (mul y z))
      (hxy : E.R mul_x_y (mul x y)),
    mul x mul_y_z = mul mul_x_y z )

def group2_map {X Y : edge} (f : hom X Y) (G : group2 X) : group2 Y :=
{ one := f.hom G.one,
  inv := λ x, f.hom (G.inv (f.op_hom x)),
  mul := λ x y, f.hom (G.mul (f.op_hom x) (f.op_hom y)),
  one_mul := λ x one' h1,
    by rw G.one_mul (f.op_hom x) (f.op_hom one') ((f.adj _ _).2 h1),
  inv_mul := λ x y hxy, 
    by rw (G.inv_mul (f.op_hom x) (f.op_hom y)) ((f.adj _ _).2 hxy),
  mul_assoc := λ x y z mul_y_z mul_x_y h1 h2, begin 
    rw G.mul_assoc,
    apply (f.adj _ _).2,
    assumption,
    apply (f.adj _ _).2,
    assumption
  end, }

lemma group2_map_id {X : edge} : group2_map (id X) = _root_.id :=
begin
  funext,
  cases G,
  refl,
end

lemma group2_map_comp {X Y Z : edge} (f : hom X Y) (g : hom Y Z ) : 
   group2_map (comp g f) = group2_map g ∘ group2_map f :=
begin
  funext,
  cases G,
  refl,
end

end edge
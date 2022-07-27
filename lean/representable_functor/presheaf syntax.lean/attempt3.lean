
inductive cat : Type
| Set : cat
| const : ℕ → cat

open sum

inductive func_obj : cat ⊕ ((cat × cat) ⊕ (cat × cat)) → Type
| opaque_obj (C : cat) (n : ℕ) : func_obj (inl C)
| opaque_func (C D : cat) (n : ℕ) : func_obj (inr $ inl (C, D))
| hom (C : cat) (X : func_obj (inl C)) : func_obj (inr $ inl (C, cat.Set)) --X is the domain
| id (C : cat) : func_obj (inr $ inr (C, C))
| comp {C D E : cat} (F : func_obj (inr $ inl (C, D))) (G : func_obj (inr $ inr (D, E))) :
  func_obj (inr $ inr (C, E))
| prod {C : cat} (F G : func_obj (inr $ inr (C, cat.Set))) : func_obj (inr $ inl (C, cat.Set))
| app {C D : cat} (F : func_obj (inr $ inl (C, D))) (X : func_obj (inl C)) : func_obj (inl D)
| corepr {C : cat} (F : func_obj (inr $ inr (C, cat.Set))) : func_obj (inl C)

def obj (C : cat) : Type := func_obj (inl C)

def func (C D : cat) : Type := func_obj (inr $ inr (C, D))

def opaque_obj (C : cat) (n : ℕ) : obj C :=
func_obj.opaque_obj C n

def opaque_func (C D : cat) (n : ℕ) : func C D :=
func_obj.comp (func_obj.opaque_func C D n) (func_obj.id _)

def hom {C : cat} (X : obj C) : func C cat.Set :=
func_obj.comp (func_obj.hom C X) (func_obj.id _)

def idf (C : cat) : func C C :=
func_obj.id C

def comp {C D E : cat} (F : func C D) (G : func D E) : func C E :=
begin
  dsimp [func] at *,
  generalize hx : (inr (inr (C, D)) : cat ⊕ ((cat × cat) ⊕ (cat × cat))) = x,
  rw [hx] at F,
  induction F generalizing C D E,
  { simp * at * },
  { simp * at * },
  { simp * at * },
  { simp only at hx,
    rcases hx with ⟨rfl, rfl⟩,
    exact G },
  { simp only at hx,
    rcases hx with ⟨rfl, rfl⟩,
    exact func_obj.comp F_F (F_ih_G G rfl) },
  { simp * at * },
  { simp * at * },
  { simp * at * }
end

def corepr {C : cat} (F : func C cat.Set) : obj C :=
func_obj.corepr F

def prodf {C : cat} (F G : func C cat.Set) : func C cat.Set :=
func_obj.comp (func_obj.prod F G) (func_obj.id _)

def app {C D : cat} (F : func C D) (X : obj C) : obj D :=
begin
  dsimp [func] at *,
  generalize hx : (inr (inr (C, D)) : cat ⊕ ((cat × cat) ⊕ (cat × cat))) = x,
  rw [hx] at F,
  induction F generalizing C D,
  { simp * at * },
  { simp * at * },
  { simp * at * },
  { simp only at hx,
    rcases hx with ⟨rfl, rfl⟩,
    exact X },
  { simp only at hx,
    rcases hx with ⟨rfl, rfl⟩,
    exact F_ih_G (func_obj.app F_F X) rfl },
  { simp * at * },
  { simp * at * },
  { simp * at * }
end
-- Don't need composition. Hom is already a functor.
inductive elem : Π (X : obj cat.Set), Type
| opaque (X : obj cat.Set) (n : ℕ) : elem X
| id {C : cat} (X : obj C) : elem (app (hom X) X)
| comp {C : cat} {X Y Z : obj C}
  (f : elem (app (hom X) Y))
  (g : elem (app (hom Y) Z)) : elem (app (hom X) Z)
| app {X Y : obj cat.Set} (f : elem (app (hom X) Y)) (x : elem X) : elem Y
| map {C D : cat} (F : func C D) {X Y : obj C} (f : elem (app (hom X) Y)) :
    elem (app (hom (app F X)) (app F Y))
| extend {C : cat} (F : func C cat.Set) {X : obj C} :
  elem ((app (hom (app F X)) (app (hom (corepr F)) X)))
| unit {C : cat} (F : func C cat.Set) : elem (app F (corepr F))
| prod_mk {C : cat} (F G : func C cat.Set) (X : obj C) :
  elem (app (hom (app F X)) (app (hom (app G X)) (app (prodf F G) X)))
| prod_fst {C : cat} (F G : func C cat.Set) (X : obj C) :
  elem (app (hom (app (prodf F G) X)) (app F X))
| prod_snd {C : cat} (F G : func C cat.Set) (X : obj C) :
  elem (app (hom (app (prodf F G) X)) (app G X))

def cat_context : Type := cat → bool

def obj_context (Γ_c : cat_context) : Type :=
Π (C : cat),

inductive rel : Π {X : obj cat.Set}, elem X → elem X → Prop
| refl {X : obj cat.Set} (x : elem X) : rel x x
| symm {X : obj cat.Set} {x y : elem X} : rel x y → rel y x
| trans {X : obj cat.Set} {x y z : elem X} : rel x y → rel y z → rel x z

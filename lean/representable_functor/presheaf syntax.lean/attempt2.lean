


#exit
import category_theory.abelian.basic

open category_theory

inductive cat : Type
| Set : cat
| const : ℕ → cat

open sum

inductive func_obj : cat ⊕ (cat × cat) → Type
| opaque_obj (C : cat) (n : ℕ) : func_obj (inl C)
| opaque_func (C D : cat) (n : ℕ) : func_obj (inr (C, D))
| hom (C : cat) (X : func_obj (inl C)) : func_obj (inr (C, cat.Set)) --X is the domain
| id (C : cat) : func_obj (inr (C, C))
| comp {C D E : cat} (F : func_obj (inr (C, D))) (G : func_obj (inr (D, E))) :
  func_obj (inr (C, E))
| prod {C : cat} (F G : func_obj (inr (C, cat.Set))) : func_obj (inr (C, cat.Set))
| app {C D : cat} (F : func_obj (inr (C, D))) (X : func_obj (inl C)) : func_obj (inl D)
| corepr {C : cat} (F : func_obj (inr (C, cat.Set))) : func_obj (inl C)

def obj (C : cat) : Type := func_obj (inl C)

def func (C D : cat) : Type := func_obj (inr (C, D))

def opaque_obj (C : cat) (n : ℕ) : obj C :=
func_obj.opaque_obj C n

def opaque_func (C D : cat) (n : ℕ) : func C D :=
func_obj.opaque_func C D n

def hom {C : cat} (X : obj C) : func C cat.Set :=
func_obj.hom C X

def idf (C : cat) : func C C :=
func_obj.id C

def comp {C D E : cat} (F : func C D) (G : func D E) : func C E :=
func_obj.comp F G

def corepr {C : cat} (F : func_obj (inr (C, cat.Set))) : obj C :=
func_obj.corepr F

def prodf {C : cat} (F G : func_obj (inr (C, cat.Set))) : func C cat.Set :=
func_obj.prod F G

def app {C D : cat} (F : func C D) (X : obj C) : obj D :=
func_obj.app F X

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

inductive rel : Π {X : obj cat.Set}, elem X → elem X → Prop
| refl {X : obj cat.Set} (x : elem X) : rel x x
| symm {X : obj cat.Set} {x y : elem X} : rel x y → rel y x
| trans {X : obj cat.Set} {x y z : elem X} : rel x y → rel y z → rel x z

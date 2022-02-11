import tactic

def hom {X Y : Type} (f : X → X) (g : Y → Y) : Type :=
{ h : X → Y // ∀ z, h (f z) = g (h z) }

instance {X Y : Type} (f : X → X) (g : Y → Y) : 
  has_coe_to_fun (hom f g) (λ _, X → Y) :=
{ coe := subtype.val }

@[simp] lemma map_f {X Y : Type} (f : X → X) (g : Y → Y) 
  (h : hom f g) : ∀ z, h (f z) = g (h z) := h.2

@[simp] def iterate_aux {X : Type} (x : X) (f : X → X) : ℕ → X
| 0     := x
| (n+1) := f (iterate_aux n)

def iterate {X : Type} (x : X) (f : X → X) : hom nat.succ f :=
⟨iterate_aux x f, λ _, rfl⟩

@[simp] lemma iterate_zero {X : Type} (x : X) (f : X → X) :
  iterate x f 0 = x := rfl

lemma app_iterate {X Y : Type} (x : X) (f : X → X)
  (g : Y → Y) (h : hom f g) (n : ℕ) :
  h (iterate x f n) = iterate (h x) g n :=
by induction n; simp *

@[simp] def add (a b : ℕ) := iterate a nat.succ b

@[simp] def mul (a b : ℕ) := iterate 0 (add b) a 

lemma add_assoc' (a b c : ℕ) : add (add a b) c = add a (add b c) :=
(app_iterate _ _ _ _ _).symm

def succ_eq_iterate (n : ℕ) : n.succ = iterate n nat.succ 1 := rfl 

lemma mul_assoc' (a b c : ℕ) : mul (mul a b) c = mul a (mul b c) :=
begin
  delta add mul,
  dsimp,
  simp only [app_iterate],

end

#print add_assoc'
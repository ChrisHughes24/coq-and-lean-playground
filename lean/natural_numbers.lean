import tactic

def hom  {X Y : Type} (f : X → X) (g : Y → Y) : Type :=
{ h : X → Y // ∀ z, h (f z) = g (h z) }

instance {X Y : Type} (f : X → X) (g : Y → Y) :
  has_coe_to_fun (hom f g) (λ _, X → Y) :=
{ coe := subtype.val }

-- Σ (X : Type) (x : X), (X → X)

-- def T := Σ (X : Type), X → X

-- def C := Σ t : T, t.fst

@[simp] lemma map_f {X Y : Type} (f : X → X) (g : Y → Y)
  (h : hom f g) : ∀ z, h (f z) = g (h z) := h.2

@[simp] def iterate_aux {X : Type} (x : X) (f : X → X) : ℕ → X
| 0     := x
| (n+1) := f (iterate_aux n)

def iterate {X : Sort*} (x : X) (f : X → X) : ℕ → X :=
iterate_aux x f
-- #print nat.rec_on
def nat.rec_on2 {motive : ℕ → Sort*} (n : ℕ) (h0 : motive 0) 
  (h1 : Π (n : ℕ), motive n → motive n.succ) : motive n :=
let x : Σ n, motive n := iterate ⟨0, h0⟩ (λ x, ⟨x.1 + 1, h1 x.1 x.2⟩) n in


def factorial (n : ℕ) : ℕ :=
(iterate (1, 1) (λ x, (x.1 + 1, x.1 * x.2)) n).2

lemma factorial_zero : factorial 0 = 1 := rfl

#eval factorial 0


@[simp] lemma iterate_zero {X : Type} (x : X) (f : X → X) :
  iterate x f 0 = x := rfl

@[simp] lemma iterate_succ {X : Type} (x : X) (f : X → X) (n : ℕ) :
  iterate x f n.succ = f (iterate x f n) := rfl

lemma factorial_succ_aux (n : ℕ) :
  (iterate (1, 1) (λ x, (x.1 + 1, x.1 * x.2)) (n + 1)) =
    let x := iterate (1, 1) (λ x, (x.1 + 1, x.1 * x.2)) n in
      (n + 2, (n + 1) * x.2) :=
by induction n; simp *

lemma factorial_succ (n : ℕ) : factorial (n + 1) = (n + 1) * factorial n :=
begin
  rw [factorial, factorial_succ_aux],
  refl
end

lemma app_iterate {X Y : Type} (h : X → Y) (x : X) (n : ℕ) (f : X → X)
  (g : Y → Y)
  (H : ∀ x, h (f x) = g (h x)) :
  h (iterate x f n) = iterate (h x) g n :=
begin
  induction n with n ih,
  { refl },
  { rw [iterate_succ, iterate_succ, H, ih], }
end

lemma iterate_iterate {X : Type} (f : X → X) (x : X) (g : ℕ → ℕ) (y : ℕ) (n : ℕ)
  (H : ∀ z, iterate x f (g z) = f (iterate x f z)) :
  iterate x f (iterate y g n) = iterate (iterate x f y) f n :=
begin
  induction n with n ih,
  { refl },
  { simp [H, ih] }
end


-- @[simp] lemma iterate_zero_succ : ⇑(iterate 0 nat.succ) = id :=
-- by funext n; induction n; simp *

-- @[simp] lemma iterate_one_succ : ⇑(iterate 1 nat.succ) = nat.succ :=
-- by funext n; induction n; simp *

lemma succ_iterate (g : ℕ → ℕ) (y : ℕ) (n : ℕ)
  (H : ∀ z, nat.succ (g z) = nat.succ z.succ) :
  nat.succ (iterate y g n) = iterate y.succ nat.succ n :=
begin
  have := iterate_iterate nat.succ 1,
  rw [iterate_one_succ] at this,
  apply this,
  assumption,
end

@[simp] lemma iterate_zero_id {X : Type} {x : X}: ⇑(iterate x id) = (λ _, x) :=
by funext n; induction n; simp *

lemma iterate_eq (x : ℕ) (f : ℕ → ℕ) (g : ℕ → ℕ) (n : ℕ)
  (h0 : x = g 0)
  (h1 : ∀ n, f (g n) = g n.succ) :
  iterate x f n = g n :=
begin
  subst h0,
  induction n,
  { simp },
  { simp * }
end

@[simp] def add (a : ℕ) : ℕ → ℕ := iterate a nat.succ
@[simp] def mul (a : ℕ) : ℕ → ℕ := iterate 0 (add a)

infix ` + ` := add
infix ` * ` := mul

lemma add_assoc' (a b c : ℕ) : add (add a b) c = add a (add b c) :=
begin
  dunfold add,
  rw [iterate_iterate],
  intros,
  simp,
end

lemma succ_add (a b : ℕ) : (add a b).succ = add a.succ b :=
begin
  simp [add],
  rw succ_iterate,
  intros, refl
end

meta def tactic.interactive.fold :=
`[repeat { rw [← add] }, repeat { rw ← mul}]

lemma mul_add' (a b c : ℕ) : mul a (add b c) = add (mul a b) (mul a c) :=
begin
  delta add mul,
  rw [app_iterate (iterate 0 (iterate a nat.succ)) b],
  rw iterate_iterate,
  { apply iterate_eq,
    { refl },
    { intro c,
      rw iterate_iterate,
      { simp,
        symmetry,
        rw iterate_iterate,
        { apply iterate_eq,
          { simp,
            induction a with a ih,
            { simp, },
            { simp,
              rw [ih],
              fold, }
             } }

          } } }
end

def succ_eq_iterate (n : ℕ) : n.succ = iterate n nat.succ 1 := rfl

lemma mul_assoc' (a b c : ℕ) : mul (mul a b) c = mul a (mul b c) :=
begin
  delta add mul,
  dsimp,
  rw [app_iterate],


end

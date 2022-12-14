import tactic
import category_theory.functor
import data.W.basic
import category_theory.closed.types
import algebra.category.CommRing.basic
import algebra.category.Module.basic

universes w x u v 

open category_theory

variables (ð : Type u) [category.{v} ð]

@[protect_proj] structure struc : Type (max u v (w+1) (x+1)) :=
( F : ð â Type w )
[ cat : category.{x} (sigma F) ]
( fst_map : Î  {A B : sigma F} (f : A â¶ B), A.1 â¶ B.1 )
( fst_map_id : â (A : sigma F), fst_map (ð A) = ð A.1 )
( fst_map_comp : â {A B C : sigma F} (f : A â¶ B) (g : B â¶ C),
    fst_map (f â« g) = fst_map f â« fst_map g )

namespace struc

instance : has_coe_to_fun (struc ð) (Î» _, ð â Type w) :=
{ coe := struc.F }

variables {ð} {F : struc ð}

instance : category (sigma F) := F.cat

def fst : sigma F â¥¤ ð :=
{ obj := sigma.fst,
  map := F.fst_map,
  map_id' := F.fst_map_id,
  map_comp' := F.fst_map_comp }

instance (X : ð) : category_struct (F X) :=
{ hom := Î» A B, { f : sigma.mk X A â¶ â¨X, Bâ© // fst.map f = ð X },
  id := Î» A, â¨ð _, by simp; reflâ©,
  comp := Î» A B C f g, â¨f.1 â« g.1, by erw [functor.map_comp, f.2, g.2, category.comp_id]â© }

instance (X : ð) : category (F X) :=
{ comp_id' := Î» _ _ _, subtype.ext (category.comp_id _),
  id_comp' := Î» _ _ _, subtype.ext (category.id_comp _),
  assoc' := Î» _ _ _ _ _ _ _, subtype.ext (category.assoc _ _ _) }

open opposite

def of_functor (F : ð â¥¤ Type w) : struc ð :=
{ F := F.obj,
  cat := 
  { hom := Î» A B, {f : A.1 â¶ B.1 // F.map f A.2 = B.2 },
    id := Î» A, â¨ð A.1, by simpâ©,
    comp := Î» A B C f g, â¨f.1 â« g.1, by simp [f.prop, g.prop]â©,
    comp_id' := Î» _ _ _, subtype.ext (category.comp_id _),
    id_comp' := Î» _ _ _, subtype.ext (category.id_comp _),
    assoc' := Î» _ _ _ _ _ _ _, subtype.ext (category.assoc _ _ _) },
  fst_map := Î» _ _, subtype.val,
  fst_map_id := by intros; refl,
  fst_map_comp := by intros; refl }

def Moduleâ : struc Ring :=
{ F := Î» R, Module R,
  cat :=
  { hom := Î» A B, Î£ f : A.1 â¶ B.1, A.2 âââ[f] B.2,
    id := Î» A, â¨ð A.1, linear_map.idâ©,
    comp := Î» A B C f g, â¨f.1 â« g.1, 
      @linear_map.comp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ â¨rflâ© g.2 f.2â©,
    comp_id' := by { intros, cases f, cases f_fst, cases f_snd, refl },
    id_comp' := by { intros, cases f, cases f_fst, cases f_snd, refl },
    assoc' := by { intros, refl } },
  fst_map := Î» _ _ f, f.fst,
  fst_map_id := by intros; refl,
  fst_map_comp := by intros; refl }


def of_category (ð : Type*) [category ð] : struc ð :=
{ F := Î» _, ð,
  cat := 
  { hom := Î» A B, (A.1 â¶ B.1) Ã (A.2 â¶ B.2),
    id := Î» _, (ð _, ð _),
    comp := Î» A B C f g, (f.1 â« g.1, f.2 â« g.2),
    comp_id' := Î» A B f, prod.ext (category.comp_id _) (category.comp_id _),
    id_comp' := Î» A B f, prod.ext (category.id_comp _) (category.id_comp _),
    assoc' := Î» A B C D f g h, prod.ext (category.assoc _ _ _) (category.assoc _ _ _) },
  fst_map := Î» _ _, prod.fst,
  fst_map_id := Î» _, rfl,
  fst_map_comp := by intros; refl }

variable (ð)

def type : struc ð := of_category (Type v)

def prop : struc ð := of_category Prop

lemma hcongr {Î± Î±' : Sort*}
  {Î² : Î± â Sort*} {Î²' : Î±' â Sort*} {f : Î  a, Î² a}
  {g : Î  a, Î²' a} (hÎ² : Î² == Î²')
  (a a') (h : f == g) (ha : a == a') :
  f a == g a' :=
begin
  have := type_eq_of_heq ha,
  subst this,
  simp at *,
  substs hÎ² ha,
  simp at *,
  subst h
end


def sigma_pi (F : ð â¥¤ Type) (G : struc (sigma (of_functor F))) : struc ð :=
{ F := Î» X, Î  a : F.obj X, G.F â¨X, aâ©,
  cat := 
  { hom := Î» A B, Î£ (f : A.1 â¶ B.1), 
      Î  (a : of_functor F A.1) (b : of_functor F B.1) (hab : b = F.map f a), 
      sigma.mk (sigma.mk A.1 a) (A.2 a) â¶ sigma.mk (sigma.mk B.1 b) (B.2 b),
    id := Î» X, â¨ð X.1, Î» x y h, cast (by simp [F.map_id] at h; rw h) 
        (ð (sigma.mk (sigma.mk X.1 x) (X.2 x)))â©,
    comp := Î» X Y Z f g, â¨f.1 â« g.1, 
        Î» a b h, cast (by simp) (f.2 a _ rfl â« g.2 (F.map f.1 a) b (by simp [h]))â©,
    comp_id' := Î» X Y f, begin 
        cases f with fâ fâ,
        ext,
        { simp },
        { refl },
        { intros a a' h,
          rw heq_iff_eq at h,
          subst a',
          dsimp,
          apply function.hfunext,
          { refl },
          { intros b b' h,
            rw [heq_iff_eq] at h,
            subst b',
            apply function.hfunext,
            simp,
            intros _ h _,
            subst h,
            simp } }
      end,
    id_comp' := Î» X Y f, begin 
        cases f with fâ fâ,
        ext,
        { simp },
        { refl },
        { intros a a' h,
          dsimp,
          rw heq_iff_eq at h,
          subst a',
          apply function.hfunext,
          { refl },
          { intros b b' h,
            rw heq_iff_eq at h,
            subst b',
            apply function.hfunext,
            { simp * at * },
            { intros,
              simp * at *,
              convert category.id_comp (fâ a b a'),
              { simp },
              { rw [F.map_id],
                refl },
              { simp },
              { simp } } } }
      end,
    assoc' := Î» W X Y Z f g h, begin
        ext, simp [category.assoc],
        intros a a' h,
        rw [heq_iff_eq] at h,
        subst h,
        simp,
        apply function.hfunext,
        { refl },
        { intros b b' h,
          rw heq_iff_eq at h,
          subst b',
          apply function.hfunext,
          { simp [category.assoc] },
          { intros c c' h,
            simp,
            dsimp,
            congr,
            { simp },
            { rw F.map_comp, refl },
            { apply hcongr,
              apply function.hfunext,
              rw F.map_comp; refl,
              intros,
              rw [F.map_comp],
              refl,
              rw [F.map_comp],
              refl,
              exact proof_irrel_heq _ _ },
            { apply hcongr,
              apply function.hfunext,
              rw F.map_comp; refl,
              intros,
              rw [F.map_comp],
              refl,
              rw [F.map_comp],
              refl,
              exact proof_irrel_heq _ _ } } }
      end },
  fst_map := Î» _ _ f, f.fst,
  fst_map_id := by intros; refl,
  fst_map_comp := by intros; refl }

example : 1 = 1 := rfl

def sigma_arrow (F : ð â¥¤ Type) (G : struc ð) : struc ð :=
{ F := Î» X, F.obj X â G X,
  cat := 
  { hom := Î» A B, Î£ (f : A.1 â¶ B.1), 
      Î  (a : of_functor F A.1) (b : of_functor F B.1) (h : b = F.map f a), 
      { g : sigma.mk A.1 (A.2 a) â¶ sigma.mk B.1 (B.2 b) // fst.map g = f } ,
    id := Î» X, â¨ð X.1, Î» x y h, â¨cast (by simp [h]) (ð (sigma.mk X.1 (X.2 x))), 
      begin simp, endâ©â©,
    comp := Î» X Y Z f g, â¨f.1 â« g.1, 
        Î» x z h, cast (by simp [h]) (f.2 x (F.map f.1 x) rfl â« g.2 (F.map f.1 x) z (by simp [h]))â©,
    comp_id' := Î» X Y f,  
      begin 
        cases f with fâ fâ,
        ext,
        { simp },
        { refl },
        { intros a a' h,
          rw heq_iff_eq at h,
          subst a',
          apply function.hfunext,
          { refl },
          { intros b b' h,
            rw heq_iff_eq at h,
            subst b',
            dsimp,
            apply function.hfunext,
            { simp },
            { intros _ h _,
              subst h,
              simp } } }
      end,
    id_comp' := Î» X Y f, begin 
        cases f with fâ fâ,
        ext,
        { simp },
        { refl },
        { intros a a' h,
          dsimp,
          rw heq_iff_eq at h,
          subst a',
          apply function.hfunext,
          { refl },
          { intros b b' h,
            rw heq_iff_eq at h,
            subst b',
            apply function.hfunext,
            { simp * at * },
            { intros,
              simp * at *,
              convert category.id_comp (fâ a b a'),
              { simp },
              { simp },
              { simp } } } }
      end,
    assoc' := Î» W X Y Z f g h, begin
        ext, simp [category.assoc],
        intros a a' h,
        rw [heq_iff_eq] at h,
        subst h,
        simp,
        apply function.hfunext,
        { refl },
        { intros b b' h,
          rw heq_iff_eq at h,
          subst b',
          apply function.hfunext,
          { simp [category.assoc] },
          { intros c c' h,
            simp,
            dsimp,
            congr,
            { simp },
            { apply hcongr,
              apply function.hfunext,
              rw F.map_comp; refl,
              intros,
              rw [F.map_comp],
              refl,
              rw [F.map_comp],
              refl,
              exact proof_irrel_heq _ _ },
            { apply hcongr,
              apply function.hfunext,
              rw F.map_comp; refl,
              intros,
              rw [F.map_comp],
              refl,
              rw [F.map_comp],
              refl,
              exact proof_irrel_heq _ _ } } }
      end },
  fst_map := Î» _ _ f, f.fst,
  fst_map_id := by intros; refl,
  fst_map_comp := by intros; refl }

-- def sigma_arrow (F : struc ð) (G : struc ð) : struc ð :=
-- { F := Î» X, Î£ (i : F X â G X), 
--     (Î  (a b : F X), (sigma.mk X a â¶ â¨X, bâ©) â 
--       { f : sigma.mk X (i a) â¶ â¨X, i bâ© // fst.map f = ð X}),
--   cat := 
--   { hom := Î» A B, Î£ (f : A.1 â¶ B.1), Î  (a : F A.1) (b : F B.1),
--       (sigma.mk A.1 a â¶ sigma.mk B.1 b) â
--       { g : (sigma.mk A.1 (A.2.1 a)) â¶ (sigma.mk B.1 (B.2.1 b)) // fst.map g = f },
--     id := Î» A, â¨ð _, Î» a b f, A.2.2 a b fâ©,
--     comp := Î» A B C f g, â¨f.1 â« g.1, Î» a c h, 
--       begin
--         have := sigma.snd f a,
        
--       endâ©,
--     comp_id' := sorry,
--     id_comp' := sorry,
--     assoc' := sorry },

--   fst_map := Î» _ _ f, f.fst,
--   fst_map_id := by intros; refl,
--   fst_map_comp := by intros; refl }


-- def sigma_piâ (F : struc ð) (G : struc (sigma F)) : struc ð :=
-- { F := Î» X, Î£ (i : Î  a : F X, G.F â¨X, aâ©), 
--     (Î  (a b : F X) (f : sigma.mk X a â¶ sigma.mk X b), 
--       { g : sigma.mk (sigma.mk X a) (i a) â¶ â¨â¨X, bâ©, i bâ© // fst.map g = f }),
--   cat := 
--   { hom := Î» A B, Î£ (f : A.1 â¶ B.1), (Î  (a : F A.1) (b : F B.1), 
--       (sigma.mk A.1 a â¶ sigma.mk B.1 b) â 
--         (sigma.mk (sigma.mk A.1 a) (A.2.1 a) â¶ â¨â¨B.1, bâ©, B.2.1 bâ©)),
--     id := Î» A, â¨ð _, Î» a b f, (A.2.2 a b f).1â©,
--     comp := Î» A B C f g, â¨f.1 â« g.1, Î» a c h, 
--       begin
--         have := sigma.snd f a,
        
--       endâ©,
--     comp_id' := sorry,
--     id_comp' := sorry,
--     assoc' := sorry },

--   fst_map := Î» _ _ f, f.fst,
--   fst_map_id := by intros; refl,
--   fst_map_comp := by intros; refl }

end struc
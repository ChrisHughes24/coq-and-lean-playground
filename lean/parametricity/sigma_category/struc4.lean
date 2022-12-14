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
( hom : Î  (A B : sigma F) (f : A.1 â¶ B.1), Type x )
( id : Î  (A : sigma F), hom A A (ð A.1) )
( comp : Î  {A B C : sigma F}
    (f : Î£ f : A.1 â¶ B.1, hom A B f)
    (g : Î£ g : B.1 â¶ C.1, hom B C g),
    hom A C (f.1 â« g.1) )
( id_comp' : Î  {A B : sigma F} (f : Î£ f : A.1 â¶ B.1, hom A B f), 
    sigma.mk (ð A.1 â« f.1) (comp â¨ð A.1, id Aâ© f) = f )
( comp_id' : Î  {A B : sigma F} (f : Î£ f : A.1 â¶ B.1, hom A B f), 
    sigma.mk (f.1 â« ð B.1) (comp f â¨ð B.1, id Bâ©) = f )
( assoc' : Î  {A B C D : sigma F} 
    (f : Î£ f : A.1 â¶ B.1, hom A B f)
    (g : Î£ g : B.1 â¶ C.1, hom B C g)
    (h : Î£ h : C.1 â¶ D.1, hom C D h), 
    sigma.mk ((f.1 â« g.1) â« h.1) (comp â¨f.1 â« g.1, comp f gâ© h) = 
    sigma.mk (f.1 â« (g.1 â« h.1)) (comp f â¨g.1 â« h.1, comp g hâ©) )

@[protect_proj] structure strucp : Type (max u v (w+1)) :=
( F : ð â Type w )
( hom : Î  (A B : sigma F) (f : A.1 â¶ B.1), Prop )
( id : Î  (A : sigma F), hom A A (ð A.1) )
( comp : Î  {A B C : sigma F}
    (f : { f : A.1 â¶ B.1 // hom A B f } )
    (g : { g : B.1 â¶ C.1 // hom B C g } ),
    hom A C (f.1 â« g.1) )

namespace struc

instance : has_coe_to_fun (struc ð) (Î» _, ð â Type w) :=
{ coe := struc.F }

variables {ð} {F : struc ð} {Fp : strucp ð}

instance : category (sigma F) :=
{ hom := Î» A B, Î£ f : A.1 â¶ B.1, F.hom A B f,
  id := Î» A, â¨ð A.1, F.id Aâ©,
  comp := Î» A B C f g, â¨f.1 â« g.1, F.comp f gâ©,
  comp_id' := Î» A B f, F.comp_id' f,
  id_comp' := Î» A B f, F.id_comp' f,
  assoc' := Î» A B C D f g h, F.assoc' f g h }

def fst : sigma F â¥¤ ð :=
{ obj := sigma.fst,
  map := Î» _ _, sigma.fst,
  map_id' := Î» _, rfl,
  map_comp' := Î» _ _ _ _ _, rfl }

instance (X : ð) : category_struct (F X) :=
{ hom := Î» A B, F.hom â¨X, Aâ© â¨X, Bâ© (ð X),
  id := Î» A, F.id â¨X, Aâ©,
  comp := Î» A B C f g, cast  
    (show F.hom â¨X, Aâ© â¨X, Câ© (ð X â« ð X) = F.hom â¨X, Aâ© â¨X, Câ© (ð X), by simp)
    (@struc.comp ð _ F â¨X, Aâ© â¨X, Bâ© â¨X, Câ© â¨ð X, fâ© â¨ð X, gâ©), }

lemma comp_mk_cast_left {A B C : sigma F}
  {fâ fâ : A.fst â¶ B.fst} (h : fâ = fâ)
  (f' : F.hom A B fâ)
  {g : Î£ (g : B.fst â¶ C.fst), F.hom B C g} :
  F.comp â¨fâ, cast (by rw h) f'â© g = 
  cast (show F.hom A C (fâ â« g.fst) = F.hom A C (fâ â« g.fst),
    by subst h) (F.comp â¨fâ, f'â© g) :=
by subst h; refl

lemma comp_mk_cast_right {A B C : sigma F}
  {f : Î£ (f : A.1 â¶ B.1), F.hom A B f}
  {gâ gâ : B.fst â¶ C.fst} (h : gâ = gâ) 
  (g' : F.hom B C gâ) :
  F.comp f â¨gâ, cast (by rw h) g'â© = 
  cast (show F.hom A C (f.1 â« gâ) = F.hom A C (f.1 â« gâ),
    by subst h) (F.comp f â¨gâ, g'â©) :=
by subst h; refl

instance (X : ð) : category (F X) :=
{ comp_id' := Î» A B f, cast_eq_iff_heq.2 $
    (sigma.ext_iff.1 (@category.comp_id (sigma F) _ â¨X, Aâ© â¨X, Bâ© â¨ð X, fâ©)).2,
  id_comp' := Î» A B f, cast_eq_iff_heq.2 $
    (sigma.ext_iff.1 (@category.id_comp (sigma F) _ â¨X, Aâ© â¨X, Bâ© â¨ð X, fâ©)).2,
  assoc' := Î» A B C D f g h, begin
    dunfold category_struct.comp,
    dsimp,
    rw [comp_mk_cast_left, comp_mk_cast_right, cast_cast, cast_cast, cast_eq_iff_heq],
    symmetry,
    rw [â cast_eq_iff_heq, cast_cast, cast_eq_iff_heq],
    exact (sigma.ext_iff.1 (@category.assoc (sigma F) _ â¨X, Aâ© â¨X, Bâ© â¨X, Câ© â¨X, Dâ©
      â¨ð X, fâ© â¨ð X, gâ© â¨ð X, hâ©)).2.symm,
    all_goals { simp; refl }
  end }

open opposite

-- def of_functor (F : ð â¥¤ Type w) : struc ð :=
-- { F := F.obj,
--   cat := 
--   { hom := Î» A B, {f : A.1 â¶ B.1 // F.map f A.2 = B.2 },
--     id := Î» A, â¨ð A.1, by simpâ©,
--     comp := Î» A B C f g, â¨f.1 â« g.1, by simp [f.prop, g.prop]â©,
--     comp_id' := Î» _ _ _, subtype.ext (category.comp_id _),
--     id_comp' := Î» _ _ _, subtype.ext (category.id_comp _),
--     assoc' := Î» _ _ _ _ _ _ _, subtype.ext (category.assoc _ _ _) },
--   fst_map := Î» _ _, subtype.val,
--   fst_map_id := by intros; refl,
--   fst_map_comp := by intros; refl }

-- def Moduleâ : struc Ring :=
-- { F := Î» R, Module R,
--   cat :=
--   { hom := Î» A B, Î£ f : A.1 â¶ B.1, A.2 âââ[f] B.2,
--     id := Î» A, â¨ð A.1, linear_map.idâ©,
--     comp := Î» A B C f g, â¨f.1 â« g.1, 
--       @linear_map.comp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ â¨rflâ© g.2 f.2â©,
--     comp_id' := by { intros, cases f, cases f_fst, cases f_snd, refl },
--     id_comp' := by { intros, cases f, cases f_fst, cases f_snd, refl },
--     assoc' := by { intros, refl } },
--   fst_map := Î» _ _ f, f.fst,
--   fst_map_id := by intros; refl,
--   fst_map_comp := by intros; refl }


def of_category (ð : Type*) [category ð] : struc ð :=
{ F := Î» _, ð,
  
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
import category_theory.abelian.basic

open category_theory

inductive cat : Type
| Set : cat
| mk : ℕ → cat

structure obj (C : cat) : Type :=
( n : ℕ )

structure functor : cat → cat → Type :=


inductive hom (C : cat) : obj C → obj C → Type
| id (X : obj C) : hom X X
| cons {X Y Z : obj C} : Π (n : ℕ) (f : hom X Y),

inductive functor (dom cod : cat) : Type
| opaque (dom cod i : ℕ) :
/-
Authors: Markus de Medeiros
-/





/--
A proper map wrt. two relations
FIXME: Move if right
-/
@[simp]
def proper1 {T1 T2 : Type} (R1 : T1 -> T1 -> Prop) (R2 : T2 -> T2 -> Prop) (f : T1 -> T2) : Prop :=
  ∀ {x y : T1}, R1 x y -> R2 (f x) (f y)

/--
A proper map wrt. three relations
FIXME: Move if right
-/
@[simp]
def proper2 {T1 T2 T3 : Type} (R1 : T1 -> T1 -> Prop) (R2 : T2 -> T2 -> Prop) (R3 : T3 -> T3 -> Prop) (f : T1 -> T2 -> T3) : Prop :=
  ∀ {x y : T1} {z w : T2}, R1 x y -> R2 z w -> R3 (f x z) (f y w)


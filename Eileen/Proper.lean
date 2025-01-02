/-
Authors: Markus de Medeiros
-/




/--
A proper map wrt. two relations
-/
@[simp]
def proper1 {T1 T2 : Type} (R1 : T1 -> T1 -> Prop) (R2 : T2 -> T2 -> Prop) (f : T1 -> T2) : Prop :=
  ∀ {x y : T1}, R1 x y -> R2 (f x) (f y)

/--
A proper map wrt. three relations
-/
@[simp]
def proper2 {T1 T2 T3 : Type} (R1 : T1 -> T1 -> Prop) (R2 : T2 -> T2 -> Prop) (R3 : T3 -> T3 -> Prop) (f : T1 -> T2 -> T3) : Prop :=
  ∀ {x y : T1} {z w : T2}, R1 x y -> R2 z w -> R3 (f x z) (f y w)

@[simp]
def proper3 (R1 : T1 -> T1 -> Prop) (R2 : T2 -> T2 -> Prop) (R3 : T3 -> T3 -> Prop) (R4 : T4 -> T4 -> Prop)
    (f : T1 -> T2 -> T3 -> T4) : Prop :=
  ∀ {x y : T1} {z w : T2} {a b : T3}, R1 x y -> R2 z w -> R3 a b -> R4 (f x z a) (f y w b)


section proper_playground

-- Welcome to setoid hell
-- Rewrite with Eq trans (resp. end relation trans + refl) to open and close a new mvar
-- Apply proper theorems manually to the evar


variable (T1 T2 : Type)
variable (R1 : T1 -> T1 -> Prop) (R2 : T2 -> T2 -> Prop)
variable (s: T1) (R1_refl : ∀ {t : T1}, R1 t t)
variable (e1 e2 : T2) (Heq : R2 e1 e2)
variable (f : T1 -> T2 -> Prop) (P2 : proper2 R1 R2 Iff f)

example : f s e1 <-> f s e2 := by
  apply Iff.trans
  · apply P2
    · apply R1_refl
    · apply Heq
  apply Iff.refl

end proper_playground

/-
Authors: Markus de Medeiros
-/

section Proper

universe u1 u2 u3 u4 -- u5
variable {T1 : Sort u1}
variable {T2 : Sort u2}
variable {T3 : Sort u3}
variable {T4 : Sort u4}
-- variable {T5 : Sort u5}

@[simp]
def is_proper1 (R1 : T1 -> T1 -> Prop) (R2 : T2 -> T2 -> Prop) (f : T1 -> T2) : Prop :=
  ∀ {x1 y1 : T1}, R1 x1 y1 -> R2 (f x1) (f y1)

@[simp]
def is_proper2  (R1 : T1 -> T1 -> Prop) (R2 : T2 -> T2 -> Prop) (R3 : T3 -> T3 -> Prop)
    (f : T1 -> T2 -> T3) : Prop :=
  ∀ {x1 y1 : T1} {x2 y2 : T2}, R1 x1 y1 -> R2 x2 y2 -> R3 (f x1 x2) (f y1 y2)

@[simp]
def is_proper3 (R1 : T1 -> T1 -> Prop) (R2 : T2 -> T2 -> Prop) (R3 : T3 -> T3 -> Prop)
    (R4 : T4 -> T4 -> Prop) (f : T1 -> T2 -> T3 -> T4) : Prop :=
  ∀ {x1 y1 : T1} {x2 y2 : T2} {x3 y3 : T3}, R1 x1 y1 -> R2 x2 y2 -> R3 x3 y3 -> R4 (f x1 x2 x3) (f y1 y2 y3)

end Proper


section proper_playground

-- Welcome to setoid hell
-- Rewrite with Eq trans (resp. end relation trans + refl) to open and close a new mvar
-- Apply proper theorems manually to the evar


variable (T1 T2 : Type)
variable (R1 : T1 -> T1 -> Prop) (R2 : T2 -> T2 -> Prop)
variable (s: T1) (R1_refl : ∀ {t : T1}, R1 t t)
variable (e1 e2 : T2) (Heq : R2 e1 e2)
variable (f : T1 -> T2 -> Prop) (P2 : is_proper2 R1 R2 Iff f)

example : f s e1 <-> f s e2 := by
  apply Iff.trans
  · apply P2
    · apply R1_refl
    · apply Heq
  apply Iff.refl

end proper_playground

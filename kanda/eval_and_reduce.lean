import Init.Prelude
namespace functionexpantion
/-関数外延性による計算のブロック例-/
def f (x : Nat) := x
def g (x : Nat) := 0 + x

theorem f_eq_g : f = g :=
  funext fun x => (Nat.zero_add x).symm

def val : Nat :=
  Eq.recOn (motive := fun _ _ => Nat) f_eq_g 0

#check Eq.recOn
#check Nat.add_assoc

#eval val
#reduce val
#reduce (g 7)

/-帰納型について-/
end functionexpantion

namespace funcExtest

def f (x : Nat) := x
def g (x : Nat) := 1 + x
def h (x : Nat) := x + 1

theorem feqg_Fake : f=g := sorry

def valFake : Nat :=
  Eq.recOn (motive := fun _ _ => Nat) feqg_Fake 0

theorem g_eq_h : g=h := funext fun x =>(Nat.add_comm 1 x)

#eval valFake

def valgh:= Eq.recOn (motive := fun _ _ => Nat) g_eq_h 0

#eval valgh

def valtes := Eq.recOn (motive := fun _ _ => Nat) (Nat.add_zero 1) 0

#eval valtes

end funcExtest

namespace quot

/-about quot-/
def mod7Rel (x y : Nat) : Prop :=
  x % 7 = y % 7

-- the quotient type
#check (Quot mod7Rel : Type)

-- the class of a
#check (Quot.mk mod7Rel 4 : Quot mod7Rel)


def f
 (x : Nat) : Bool :=
  x % 7 = 0

theorem f_respects (a b : Nat) (h : mod7Rel a b) : f a = f b := by
  simp [mod7Rel, f] at *
  rw [h]

#check (Quot.lift f f_respects : Quot mod7Rel → Bool)

-- the computation principle
example (a : Nat) : Quot.lift f f_respects (Quot.mk mod7Rel a) = f a :=
  rfl

end quot

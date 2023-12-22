import Init.Prelude
import Mathlib.Tactic
namespace functionexpantion
/-関数外延性による計算のブロック例-/
variable (z: Nat)
def f (x : Nat) := x
def g (x : Nat) := 0 + x

theorem f_eq_g : f = g :=
  funext fun x => (Nat.zero_add x).symm

def val /-(x:Nat)-/: Nat :=
  Eq.recOn (motive := fun _ _ => Nat) f_eq_g 0 --x

#check Eq.recOn
#check Nat.add_assoc

#eval val --なお、変数を入れられるようにしてzを入れるとエラー
#reduce val
#reduce (g 7)

/-帰納型について-/
end functionexpantion

namespace funcExtest
/-Strange!!-/

def f (x : Nat) := x -- + 10 --色々変えてみました
def g (x : Nat) := 1 + x
def h (x : Nat) := x + 1

theorem feqg_Fake : f=g := sorry --sorryを消しても実はevalで0が出た。何故？

def valFake : Nat :=
  Eq.recOn (motive := fun _ _ => Nat) feqg_Fake 0 -- <-この末尾の数字が反映されている？

#eval valFake --fの値を実は反映している
#reduce valFake

theorem geqf_Fake : g=f := sorry

def reverse_vF : Nat:=
  Eq.recOn (motive := fun _ _ => Nat) geqf_Fake 0

#eval reverse_vF --順番を入れ替えたらgを反映するわけではなかった

theorem g_eq_h : g=h := funext fun x =>(Nat.add_comm 1 x)

def valgh /-(x:Nat)-/ := Eq.recOn (motive := fun _ _=> Nat) g_eq_h 0 --x

#eval valgh --g(0),h(0)いずれも反映していない。
--変数でNat→Nat型をいれられるようにして、
--(motive := fun g h=> Nat)となるようにしてみたがこれも反映していない。
#reduce valgh

variable (a : Nat)
theorem foo : 5 ≤ a + 5 := by
  nth_rw 1 [←Nat.add_zero 5, add_comm]
  apply add_le_add_right
  exact Nat.zero_le a

theorem foo2 : 5+a=a+5 :=by
  rw [add_comm]

def valtes := Eq.recOn (motive := fun _ _ => Nat) (Nat.add_zero 1) 9
--def valtes := Eq.recOn (motive := fun _ _ => Nat) (foo) 0 --なお、これにはエラーが出る。
--x＝yの形であるかどうかはEq.recOnが判断を要求するようだ。
--def valtes := Eq.recOn (motive := fun _ _ => Nat) (foo2 9) 0
--命題foo2自体は真だが、x=yの形式を要求するためaの具体的数値が要求されている。

#eval valtes  --どの値を反映しているのか？　fの改変結果からfでない。値よりg,hでない
#reduce valtes

def k (x : Nat) (y : Nat) := x + y + 1
#eval k 2 3
#reduce k 2 3

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

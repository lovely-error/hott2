
import Simptt.core


def not_iso: iso Bool Bool := by
  unfold iso
  exact ~(not, by unfold iscoh_map; exact (.mksprop not (by intro i; cases i <;> rfl)))

def proof : (not a) = not (not (not a)) := by cases a <;> rfl

-- notice that proof is not definitionally equal to the
-- thing bellow
example : a = not (not a) := by
  let (.mksprop _ c) := p1 not_iso a
  unfold iso.bw not_iso at c;
  simp at c
  rw [c]
  exact proof

-- this is a type mismatch!
-- example : a = not (not a) := proof



def f : Nat -> List Unit
| .zero => .nil
| .succ a => .cons () (f a)
def b : List Unit -> Nat
| .nil => .zero
| .cons .unit t => .succ (b t)
def coh : (a : Nat) -> a = b (f a) := by
  intro i
  match i with
  | .succ a => unfold b f; simp; exact (coh a)
  | .zero => unfold b f; simp;

def int_list : iso Nat (List Unit) := by
  unfold iso
  exact ~(
    f,
    by unfold iscoh_map
       exact (.mksprop b coh)
  )

-- a proof about integers
-- by doing pattern matching on a list!!!!
example : (a > 0) -> (a + 1 > 0) := by
  let (.mksprop k p) := p1 int_list a
  rw [p]
  unfold iso.bw int_list;
  cases k
  . case nil => intro; contradiction
  . case cons a b => simp;

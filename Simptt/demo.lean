
import Simptt.core
import Simptt.others

def not_wmap: wmap Bool Bool :=
  ~(not, (.mksprop not (by intro i; cases i <;> rfl)))

def proof : (not a) = not (not (not a)) := by cases a <;> rfl

-- notice that proof is not definitionally equal to the
-- thing bellow
example : a = not (not a) := by
  let (.mksprop _ c) := p1 not_wmap a
  rw [<-c]
  apply proof

-- this is a type mismatch!
-- example : a = not (not a) := proof

def nat2list : Nat -> List Unit
| .zero => .nil
| .succ a => .cons () (nat2list a)
def list2nat : List Unit -> Nat
| .nil => .zero
| .cons .unit t => .succ (list2nat t)
def nl_coh : (a : Nat) -> a = list2nat (nat2list a) := by
  intro i
  match i with
  | .succ a => unfold list2nat nat2list; simp; exact (nl_coh a)
  | .zero => unfold list2nat nat2list; simp;

def int_list : wmap Nat (List Unit) := by
  unfold wmap
  exact ~(
    nat2list,
    by unfold iscoh_wmap
       exact (.mksprop list2nat nl_coh)
  )


example : (a > 0) -> (a + 1 > 0) := by
  let (.mksprop k p) := p1 int_list a
  rw [<-p]
  cases k
  . case nil => intro; contradiction
  . case cons a b => simp;



def ln_coh : (a : List Unit) -> a = nat2list (list2nat a) := by
  intro i
  match i with
  | .cons () a => unfold list2nat nat2list; simp; exact (ln_coh a)
  | .nil => unfold list2nat nat2list; simp;



def list_int : wmap (List Unit) Nat := by
  unfold wmap
  exact ~(
    list2nat,
    (.mksprop nat2list ln_coh)
  )

def fmap_append_plus :
    (nat2list a1).append (nat2list a2) = nat2list (a1 + a2)
:= by
  cases a1
  {
    cases a2
    {
      unfold nat2list
      simp
    }
    {
      case _ n =>
        cases n
        {
          unfold nat2list
          simp
        }
        {
          case _ n =>
            unfold nat2list at *
            simp
        }
    }
  }
  {
    cases a2
    {
      case _ a =>
        unfold nat2list
        simp
    }
    {
      case _ a b =>
        rw [Nat.add_add_add_comm]
        unfold nat2list
        simp
        induction a
        {
          simp [nat2list]
        }
        {
          case _ n ih =>
            simp [nat2list]
            rw [ih]
            rw [Nat.add_right_comm _ 1 b]
        }
    }
  }

-- juggle around a funtor technique
example : List.append (a:List Unit) (b:List Unit) = List.append b a := by
  let (.mksprop a1 r1) := p1 list_int a
  let (.mksprop a2 r2) := p1 list_int b
  rw [<-r1, <-r2]
  rw [fmap_append_plus]
  rw [fmap_append_plus]
  rw [Nat.add_comm]

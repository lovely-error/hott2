import Simptt.core
import Simptt.demo

def fmap_general {A:Type _}{B:Type _}{op:A->A->A}{a b:B}:
  (w:wmap A B) -> let (.mk f (.mksprop h _)) := w;
  sigmaprop (B->B->B) fun opm => (op (h a) (h b) = h (opm a b)) ∧
                                 (opm = fun (b1:B) (b2:B) => f (op (h b1) (h b2)))
:= by
  intro w
  let (.mk f (.mksprop h p1)) := w
  simp
  refine .mksprop ?_ ?_
  exact fun b1 b2 =>
    f (op (h b1) (h b2))
  rw [Eq.symm (p1 (op (h a) (h b)))]
  exact ⟨rfl, rfl⟩


example : List.append (a:List Unit) (b:List Unit) = List.append b a := by
  let (.mksprop a1 r1) := p1 list_int a
  let (.mksprop a2 r2) := p1 list_int b
  rw [<-r1, <-r2]
  let (sigmaprop.mksprop f1 ~(r3, r4)) := @fmap_general _ _ List.append a1 a2 list_int
  simp at r3
  simp
  rw [r3]
  let (sigmaprop.mksprop f2 ~(r5, r6)) := @fmap_general _ _ List.append a2 a1 list_int
  simp at r5
  rw [r5]
  rw [r4, r6]
  simp
  admit



def list_int_iso : iso (List Unit) Nat :=
  mkiso list2nat nat2list nl_coh ln_coh




-- https://ncatlab.org/nlab/show/weak+homotopy+equivalence#ExamplesOfNonReversibleWHEs
-- def invert_wmap : wmap A B -> wmap B A




def bool_nat : wmap Bool Nat := by
  refine mkwmap ?_ ?_ ?_
  intro i
  cases i
  . exact 0
  . exact 1
  intro i
  cases i
  . exact false
  . exact true
  intro b
  cases b <;> rfl



def hgroup (n:Nat)(T:Type u): Type u := match n with
| .zero => wmap T T
| .succ a => wmap (hgroup a T) (hgroup a T)


def hboundry : Nat -> Type _ -> Type _ := fun n T => iscontr (hgroup n T)

def hgroup_unit : hgroup 0 Unit := by
  unfold hgroup
  refine mkwmap ?_ ?_ ?_
  exact id
  exact id
  intro
  simp

def unit_contr : iscontr Unit := .mksprop () fun i => @rfl _ i

example : hboundry 0 Unit := by
  unfold hboundry
  unfold iscontr
  refine .mksprop ?_ ?_
  exact hgroup_unit
  intro i
  let (.mk f (.mksprop h p)) := i
  let rr := no_autos unit_contr f
  subst rr
  let rr2 := no_autos unit_contr h
  subst rr2
  unfold hgroup_unit
  rfl

def id_hgroup : hgroup n T := by
  cases n <;> exact idwmap

example : hgroup 1 Bool := by
  unfold hgroup hgroup
  refine .mk ?_ (.mksprop ?_ ?_)
  exact id
  exact id
  simp

set_option pp.proofs true

def comp_wmap_bool_not_id (i:wmap Bool Bool) : i = comp not_wmap (comp not_wmap i) := by
  let (.mk f (.mksprop h p)) := i
  unfold comp not_wmap
  simp [mkwmap]

  admit

example : hboundry 1 Bool := by
  unfold hboundry iscontr
  refine .mksprop ?_ ?_
  {
    unfold hgroup hgroup
    refine .mk ?_ (.mksprop ?_ ?_)
    intro i
    exact comp not_wmap i
    intro i
    exact comp not_wmap i
    intro (.mk f (.mksprop h p))
    unfold not_wmap comp mkwmap
    simp
    let sr1 : (fun a => f !!a) = (fun a => f a) := by
      simp [Bool.not_not]
    -- subst sr1
    -- rw [sr1]

    admit
  }
  simp
  admit




def iterf : Nat -> (T -> T) -> (T -> T)
| .zero , _ => id
| .succ (.zero), f => fun i => f i
| .succ (.succ a), f => fun i => ((iterf (.succ a) f) (f i))


def orbit : T -> (T -> T) -> Type _ :=
  fun is f => sigmaprop Nat fun k => (iterf k f is) = is

def id_iter {T}: ∀ a , (iterf a (@id T)) = id := fun i => by
  induction i
  unfold iterf
  rfl
  case succ n ih =>
    cases n
    rfl
    unfold iterf;
    simp
    rw [ih]


def id_iter2 : ∀ a b , (iterf a (@id T)) = (iterf b id) := by
  intro a b
  rw [id_iter]
  rw [id_iter]

def id_contr_orbit_wmap {T}: ∀ (a:T) (b:T) , wmap (orbit a id) (orbit b id) := by
  intros a b
  refine mkwmap ?f ?h ?_
  unfold orbit
  simp only [id_iter2 _ 0]
  simp [iterf]
  exact id
  unfold orbit
  simp only [id_iter2 _ 0]
  simp [iterf]
  exact id
  intro p
  simp
  let (.mksprop n p2) := p
  admit

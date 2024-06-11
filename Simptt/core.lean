
notation "~(" L "," R ")" => ⟨ L , R ⟩

inductive sigmaprop (T:Type _)(P:T -> Prop) : Type _
| mksprop : (t:T) -> P t -> sigmaprop T P

def iscoh_map {A:Type _}{B:Type _} : (A -> B) -> Type _ := fun f => sigmaprop (B -> A) fun r => ∀ a , a = r (f a)
def iso : Type _ -> Type _ -> Type _ := fun A B => @Sigma (A -> B) fun f => iscoh_map f

def iso.fw : iso A B -> (A -> B) := fun (.mk f _) => f
def iso.bw : iso A B -> (B -> A) := fun (.mk _ d) => by unfold iscoh_map at d; let (.mksprop bw _) := d; exact bw

def p1 : (p:iso A B) -> ∀ a , sigmaprop B fun b => a = (p.bw b) := by
  intros p a; unfold iso iscoh_map at p
  let (Sigma.mk f k) := p;
  simp at k
  let (.mksprop h r) := k
  unfold iso.bw; simp
  exact (.mksprop (f a) (r a))


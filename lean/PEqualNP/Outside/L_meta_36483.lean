import PEqualNP.Defs

-- The witness has 11 binary gates. Any circuit with a NOT and fewer gates
-- would have at most 9 binary gates even with every negation available for free.
-- Finite signed-circuit certificates below exclude that possibility.
-- Signed-wire search, gate projections and the certificate verifier adapt L-meta-16701 (Apache-2.0).
namespace PEqualNP.Outside.L_meta_36483_aux
namespace CoreSigned

-- The signed live-wire search follows L-meta-8463 and L-meta-1449, Apache-2.0.

section Live

variable {α : Type} [DecidableEq α]

def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k + 1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k + 1, s => live ops goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest)

set_option maxRecDepth 100000 in
theorem compress {ops : α → α → Finset α} {goal : α} {k : ℕ} {available : Finset α}
    (h : build ops goal k available) : ∃ s ⊆ available, live ops goal k s := by
  induction k generalizing available with
  | zero =>
    exact ⟨{goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · obtain ⟨s, hs, hrun⟩ := ih skip
      exact ⟨s, hs, Or.inl hrun⟩
    · obtain ⟨t, ht, hrun⟩ := ih tail
      by_cases sub : t ⊆ available
      · exact ⟨t, sub, Or.inl hrun⟩
      · have hzmem : z ∈ t := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ available := by
          intro hh
          exact sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase z
        have hrest : rest ⊆ available := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
        let s := insert a (insert b rest)
        have hs : s ⊆ available := Finset.insert_subset ha (Finset.insert_subset hb hrest)
        refine ⟨s, hs, Or.inr ⟨a, by simp [s], b, by simp [s], hab, z, hz,
          fun h => hzout (hs h), rest, rfl, ?_⟩⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun

set_option maxRecDepth 100000 in
theorem live_card {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal k s) : s.card ≤ k + 1 := by
  induction k generalizing s with
  | zero => change s = {goal} at h; simp [h]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact (ih skip).trans (by omega)
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a (insert b rest)
      have h₂ := Finset.card_insert_le b rest
      omega

set_option maxRecDepth 100000 in
theorem live_separates {ops : α → α → Finset α} {goal : α} (D : α → Prop)
    (hd : D goal) (hops : ∀ a b, ∀ z ∈ ops a b, D z → D a ∨ D b)
    {k : ℕ} {s : Finset α} (h : live ops goal k s) : ∃ w ∈ s, D w := by
  induction k generalizing s with
  | zero => change s = {goal} at h; exact ⟨goal, by simp [h], hd⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact ih skip
    · obtain ⟨w, hw, hD⟩ := ih tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases hops a b w hz hD with h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
      · exact ⟨w, by simp [hw], hD⟩

set_option maxRecDepth 100000 in
theorem first_live {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal (k + 1) s) :
    s = {goal} ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | step
    · rcases ih skip with done | ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, tail⟩
      · exact .inl done
      · exact .inr ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, Or.inl tail⟩
    · exact .inr step

end Live

def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

set_option maxRecDepth 100000 in
theorem pick_one {α : Type} {a : α} {ws : List α} (h : a ∈ ws) :
    ∃ rest, (a, rest) ∈ singles ws ∧ ws.Perm (a :: rest) := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with e | h
    · subst x; exact ⟨xs, by simp [singles], .refl _⟩
    · obtain ⟨rest, hm, hp⟩ := ih h
      refine ⟨x :: rest, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a, rest), hm, rfl⟩), ?_⟩
      exact (hp.cons x).trans (.swap _ _ _)

set_option maxRecDepth 100000 in
theorem pick_two {α : Type} {a b : α} {ws : List α} (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    ∃ rest, ((a, b, rest) ∈ pairs ws ∨ (b, a, rest) ∈ pairs ws) ∧
      ws.Perm (a :: b :: rest) := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with h | ha
    · subst x
      obtain ⟨r, hm, hp⟩ := pick_one ((List.mem_cons.mp hb).resolve_left (Ne.symm hne))
      exact ⟨r, .inl (List.mem_append_left _ (List.mem_map.mpr ⟨(b, r), hm, rfl⟩)), hp.cons a⟩
    · rcases List.mem_cons.mp hb with h | hb
      · subst x
        obtain ⟨r, hm, hp⟩ := pick_one (ws := xs) (a := a) (by assumption)
        exact ⟨r, .inr (List.mem_append_left _ (List.mem_map.mpr ⟨(a, r), hm, rfl⟩)),
          (hp.cons b).trans (.swap _ _ _)⟩
      · obtain ⟨r, hm, hp⟩ := ih ha hb
        refine ⟨x :: r, ?_,
          (hp.cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons a))⟩
        rcases hm with hm | hm
        · exact .inl (List.mem_append_right _ (List.mem_map.mpr ⟨(a, b, r), hm, rfl⟩))
        · exact .inr (List.mem_append_right _ (List.mem_map.mpr ⟨(b, a, r), hm, rfl⟩))

def F (x : Fin 6 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 3) || (x 1 && x 5) || (x 2 && x 3) || (x 2 && x 4)

end CoreSigned

namespace SignedProjection
variable {α β : Type} [DecidableEq α] [DecidableEq β] [Zero β]

def avail (pin : α → β) (S : Finset α) := (S.image pin).erase 0
def lost (pin : α → β) (S : Finset α) := (S.filter fun x => pin x = 0).card

theorem avail_mem (pin : α → β) {S : Finset α} {x : β} :
    x ∈ avail pin S ↔ x ≠ 0 ∧ ∃ a ∈ S, pin a = x := by simp [avail]

theorem avail_mono (pin : α → β) {S T : Finset α} (h : S ⊆ T) : avail pin S ⊆ avail pin T := by
  intro y hy
  obtain ⟨hn,x,hx,rfl⟩ := (avail_mem pin).mp hy
  exact (avail_mem pin).mpr ⟨hn,x,h hx,rfl⟩

theorem avail_cases (pin : α → β) {S : Finset α} {c : α} {x : β} (h : x ∈ avail pin (insert c S)) :
    x = pin c ∨ x ∈ avail pin S := by
  obtain ⟨hn,y,hy,rfl⟩ := (avail_mem pin).mp h
  rcases Finset.mem_insert.mp hy with rfl|hy
  · exact Or.inl rfl
  · exact Or.inr ((avail_mem pin).mpr ⟨hn,y,hy,rfl⟩)

theorem lost_insert (pin : α → β) (c : α) (S : Finset α) :
    lost pin (insert c S) = lost pin S + (if pin c = 0 ∧ c ∉ S then 1 else 0) := by
  by_cases mem : c ∈ S
  · rw [Finset.insert_eq_of_mem mem,ite_eq_right (fun q => q.2 mem),Nat.add_zero]
  · by_cases h : pin c = 0
    · rw [ite_eq_left ⟨h,mem⟩]
      unfold lost
      rw [Finset.filter_insert,ite_eq_left h,Finset.card_insert_of_notMem]
      exact fun q => mem (Finset.mem_filter.mp q).1
    · rw [ite_eq_right (fun q => h q.1),Nat.add_zero]
      unfold lost
      rw [Finset.filter_insert,ite_eq_right h]

theorem projected (pin : α → β) (ops : α → α → Finset α) (ops2 : β → β → Finset β) (goal : α)
    (hgoal : pin goal ≠ 0)
    (maps : ∀ {a b c}, c ∈ ops a b → pin c ∈ ops2 (pin a) (pin b))
    (idA : ∀ {a b c}, c ∈ ops2 a b → a = 0 → c = 0 ∨ c = b)
    (idB : ∀ {a b c}, c ∈ ops2 a b → b = 0 → c = 0 ∨ c = a)
    (idS : ∀ {a b c}, c ∈ ops2 a b → a = b → c = 0 ∨ c = b)
    {k : Nat} {S : Finset α} (h : CoreSigned.live ops goal k S) :
    ∃ j, j + lost pin S ≤ k ∧ ∃ T ⊆ avail pin S, CoreSigned.live ops2 (pin goal) j T := by
  induction k generalizing S with
  | zero =>
    change S = {goal} at h
    subst S
    exact ⟨0,by simp [lost,hgoal],{(pin goal)},by simp [avail,hgoal],rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a,_,b,_,ne,c,op,fresh,U,rfl,tail⟩
    · obtain ⟨j,hj,ws,sub,hws⟩ := ih skip
      exact ⟨j,by omega,ws,sub,hws⟩
    let prev := insert a (insert b U)
    have cnew : c ∉ U := fun h => fresh (by simp [h])
    have repr := maps op
    obtain ⟨j,limit,T,sub,path⟩ := ih tail
    have both (ha : pin a = 0) (hb : pin b = 0) : pin c = 0 := by
      exact (idA repr ha).elim id (fun e => e.trans hb)
    have skipcost : lost pin prev ≤ lost pin (insert c U) + 1 := by
      simp only [prev,lost_insert]
      split_ifs <;> grind
    have liftU : avail pin U ⊆ avail pin prev := avail_mono pin (by intro u hu; simp [prev,hu])
    by_cases useful : pin c ∈ T ∧ pin c ∉ avail pin prev
    · have nz := ((avail_mem pin).mp (sub useful.1)).1
      have df (v : α) (hv : v ∈ prev) : pin c ≠ pin v := by
        intro e
        exact useful.2 ((avail_mem pin).mpr ⟨nz,v,hv,e.symm⟩)
      have da := df a (by simp [prev])
      have db := df b (by simp [prev])
      have ha : pin a ≠ 0 := fun e => (idA repr e).elim nz db
      have hb : pin b ≠ 0 := fun e => (idB repr e).elim nz da
      have distinct : pin a ≠ pin b := fun e => (idS repr e).elim nz db
      have vcost : lost pin prev ≤ lost pin (insert c U) := by
        simp only [prev,lost_insert]
        split_ifs <;> grind
      let V := T.erase (pin c)
      have old (v : β) (hv : v ∈ V) : v ∈ avail pin U :=
        (avail_cases pin (sub (Finset.mem_erase.mp hv).2)).resolve_left (Finset.mem_erase.mp hv).1
      let B := insert (pin a) (insert (pin b) V)
      refine ⟨j+1,by change j+1+lost pin prev ≤ k+1; omega,B,?_,Or.inr ?_⟩
      · intro v hv
        rcases Finset.mem_insert.mp hv with rfl|hv
        · exact (avail_mem pin).mpr ⟨ha,a,by simp,rfl⟩
        rcases Finset.mem_insert.mp hv with rfl|hv
        · exact (avail_mem pin).mpr ⟨hb,b,by simp,rfl⟩
        exact liftU (old _ hv)
      · refine ⟨pin a,by simp [B],pin b,by simp [B],distinct,pin c,?_,?_,V,rfl,?_⟩
        · exact repr
        · simp [B,V,da,db]
        · rwa [show insert (pin c) V = T from Finset.insert_erase useful.1]
    · refine ⟨j,by change j+lost pin prev ≤ k+1; omega,T,?_,path⟩
      intro v hv
      rcases avail_cases pin (sub hv) with rfl|old
      · by_contra miss
        exact useful ⟨hv,miss⟩
      · exact liftU old


end SignedProjection

namespace SignedProjection
variable {n : Nat}

def signedOps (a b : BitVec n) := [a &&& b, a ||| b, a &&& ~~~b, b &&& ~~~a].toFinset

theorem zero_left {a b c : BitVec n} (h : c ∈ signedOps a b) (eq : a = 0) : c = 0 ∨ c = b := by
  subst a
  simpa [signedOps,or_comm] using h

theorem zero_right {a b c : BitVec n} (h : c ∈ signedOps a b) (eq : b = 0) : c = 0 ∨ c = a := by
  subst b
  simpa [signedOps,or_comm] using h

theorem equal_inputs {a b c : BitVec n} (h : c ∈ signedOps a b) (eq : a = b) : c = 0 ∨ c = b := by
  subst a
  simpa [signedOps,or_comm] using h

def signedPin (mask : BitVec n) (base : Fin n) (x : BitVec n) : BitVec n :=
  (if x[base.val] then ~~~x else x) &&& mask

theorem masked_ops (m : BitVec n) {a b c : BitVec n} (h : c ∈ signedOps a b) :
    c &&& m ∈ signedOps (a &&& m) (b &&& m) := by
  simp only [signedOps,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at *
  rcases h with rfl|rfl|rfl|rfl
  · left; ext i h; simp [Bool.and_assoc, Bool.and_left_comm, Bool.and_comm]
  · right;left; ext i h; simp only [BitVec.getElem_or,BitVec.getElem_and]; cases a[i] <;> cases b[i] <;> simp
  · right;right;left; ext i h
    simp only [BitVec.getElem_and,BitVec.getElem_not]
    cases a[i] <;> cases b[i] <;> cases m[i] <;> decide
  · right;right;right; ext i h
    simp only [BitVec.getElem_and,BitVec.getElem_not]
    cases a[i] <;> cases b[i] <;> cases m[i] <;> decide

def polarity (b : Bool) (x : BitVec n) := if b then ~~~x else x

theorem polarity_ops (i : Fin n) {a b c : BitVec n} (h : c ∈ signedOps a b) :
    polarity (c[i.val]) c ∈ signedOps (polarity (a[i.val]) a) (polarity (b[i.val]) b) := by
  simp only [signedOps,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at *
  rcases h with rfl|rfl|rfl|rfl <;>
    simp only [BitVec.getElem_and,BitVec.getElem_or,BitVec.getElem_not] <;>
    cases a[i.val] <;> cases b[i.val] <;>
    simp [polarity,BitVec.not_and,BitVec.not_or,BitVec.and_comm,BitVec.or_comm]

theorem signedPin_ops (m : BitVec n) (i : Fin n) {a b c : BitVec n} (h : c ∈ signedOps a b) :
    signedPin m i c ∈ signedOps (signedPin m i a) (signedPin m i b) :=
  masked_ops m (polarity_ops i h)

theorem live_build {α : Type} [DecidableEq α] {ops : α → α → Finset α} {goal : α}
    {k : Nat} {S V : Finset α} (h : CoreSigned.live ops goal k S) (sub : S ⊆ V) :
    CoreSigned.build ops goal k V := by
  induction k generalizing S V with
  | zero => change S = {goal} at h; subst S; exact sub (Finset.mem_singleton_self _)
  | succ k ih =>
    rcases h with skip|⟨a,ha,b,hb,ne,c,opc,_,rest,eq,tail⟩
    · exact Or.inl (ih skip sub)
    · refine Or.inr ⟨a,sub ha,b,sub hb,ne,c,opc,ih tail ?_⟩
      intro v hv
      rcases Finset.mem_insert.mp hv with rfl|hr
      · simp
      · exact Finset.mem_insert_of_mem (sub (eq ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hr)))

end SignedProjection

namespace SignedProjection
variable {α : Type} [DecidableEq α]

def generated (ops : α → α → Finset α) (stock : Finset α) : List (α × α × α) → Finset α → Prop
  | [], result => stock = result
  | (a,b,w) :: rest, result =>
    a ∈ stock ∧ b ∈ stock ∧ a ≠ b ∧ w ∈ ops a b ∧ generated ops (insert w stock) rest result

theorem extend_generated {ops : α → α → Finset α} {goal : α} {stock result : Finset α}
    {recipe : List (α × α × α)} {k : ℕ}
    (h : generated ops stock recipe result) (tail : CoreSigned.build ops goal k result) :
    CoreSigned.build ops goal (k + recipe.length) stock := by
  induction recipe generalizing stock with
  | nil => change stock = result at h; simpa [h] using tail
  | cons step rest ih =>
    obtain ⟨a,b,w⟩ := step
    rcases h with ⟨ha,hb,hn,ho,hrest⟩
    change CoreSigned.build ops goal (k+rest.length+1) stock
    exact Or.inr ⟨a,ha,b,hb,hn,w,ho,ih hrest⟩

theorem pad_build {ops : α → α → Finset α} {goal : α} {S : Finset α} {a b : Nat}
    (le : a ≤ b) (ha : CoreSigned.build ops goal a S) : CoreSigned.build ops goal b S := by
  induction le with
  | refl => exact ha
  | step _ ih => exact Or.inl ih

end SignedProjection

namespace SignedProjection
variable {n : Nat}

theorem exclude_cut (m : BitVec n) (i : Fin n) (goal : BitVec n) (k cap : ℕ)
    (S A U : Finset (BitVec n)) (recipes : List (BitVec n × BitVec n × BitVec n))
    (nonzero : signedPin m i goal ≠ 0)
    (bound : ¬ CoreSigned.build signedOps (signedPin m i goal) cap A)
    (regen : generated signedOps A recipes U) (sub : avail (signedPin m i) S ⊆ U)
    (budget : recipes.length + k ≤ cap + lost (signedPin m i) S) :
    ¬ CoreSigned.live signedOps goal k S := by
  intro h
  obtain ⟨j, hj, T, ht, path⟩ := projected (signedPin m i) signedOps signedOps goal nonzero
    (signedPin_ops m i) zero_left zero_right equal_inputs h
  have localRun := live_build path (ht.trans sub)
  exact bound (pad_build (by omega) (extend_generated regen localRun))

end SignedProjection

namespace SignedProjection
open CoreSigned (live build first_live live_card pairs pick_two live_separates)

abbrev Word := BitVec 64
def signedList (a b : Word) := [a &&& b, a ||| b, a &&& ~~~b, b &&& ~~~a]
theorem ops_swap (a b : Word) : signedOps a b = signedOps b a := by
  ext z
  simp only [signedOps, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  rw [BitVec.and_comm a b, BitVec.or_comm a b]
  tauto
def keepChoices (a b : Word) (r : List Word) : List (List Word) := [r, a :: r, b :: r, a :: b :: r]

theorem recover_kept {ws r : List Word} {a b : Word} {needed : Finset Word}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v
    simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by
      rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a :: b :: r, by simp [keepChoices], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a :: r, by simp [keepChoices], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b :: r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

theorem singleton_list {goal : Word} {ws : List Word} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

def insertW (v : Word) : List Word → List Word
  | [] => [v]
  | x :: xs => if v ≤ x then v :: x :: xs else x :: insertW v xs

def ordered (ws : List Word) := ws.foldr insertW []

theorem insertW_perm (v : Word) (ws : List Word) : (insertW v ws).Perm (v :: ws) := by
  induction ws with
  | nil => exact .refl _
  | cons x xs ih =>
    simp only [insertW]
    split
    · exact .refl _
    · exact (ih.cons x).trans (.swap _ _ _)

theorem ordered_perm (ws : List Word) : (ordered ws).Perm ws := by
  induction ws with
  | nil => exact .refl _
  | cons x xs ih => exact (insertW_perm x (ordered xs)).trans (ih.cons x)

theorem perm_set {u v : List Word} (p : u.Perm v) : u.toFinset = v.toFinset := by
  ext a
  simpa only [List.mem_toFinset] using (p.mem_iff : a ∈ u ↔ a ∈ v)


def children (k : Nat) (ws : List Word) : List (List Word) :=
  (pairs ws).flatMap fun (a,b,r) => (signedList a b).flatMap fun z =>
    if z ∈ ws then [] else
      (keepChoices a b r).filterMap fun kept =>
        if kept.length ≤ k then some (ordered (z :: kept)) else none

theorem zero_prune {goal : Word} (nz : goal ≠ 0) {k : Nat} {S : Finset Word}
    (h : live signedOps goal k S) : ∃ j ≤ k, ∃ T ⊆ S.erase 0, live signedOps goal j T := by
  obtain ⟨j,le,T,sub,path⟩ := projected id signedOps signedOps goal nz (fun q => q)
    zero_left zero_right equal_inputs h
  refine ⟨j,by omega,T,?_,path⟩
  simpa [avail] using sub

theorem step_no (goal : Word) (n : Nat) (ws : List Word) (hn : ws.Nodup)
    (done_ : ws ≠ [goal])
    (children_ : ∀ qs ∈ children n ws, ¬ live signedOps goal n qs.toFinset)
    : ¬ live signedOps goal (n+1) ws.toFinset := by
  intro h
  rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
  · exact done_ (singleton_list hn done)
  obtain ⟨r,hm,hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
  have go {a b : Word} (hp : ws.Perm (a :: b :: r)) (hmem : (a,b,r) ∈ pairs ws)
      (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ signedOps a b) : False := by
    obtain ⟨kept,hkeep,hnk,hfin⟩ := recover_kept hp hn hset
    have hznew : z ∉ kept := by
      intro hu
      apply hout
      rw [hset]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ List.mem_toFinset.mpr hu))
    have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
    have hraw : live signedOps goal n (z :: kept).toFinset := by simpa [hfin] using tail
    have hc := live_card hraw
    rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
    have hzws : z ∉ ws := by simpa using hout
    have hp' := ordered_perm (z :: kept)
    have mem : ordered (z :: kept) ∈ children n ws := by
      apply List.mem_flatMap.mpr
      refine ⟨(a,b,r),hmem,List.mem_flatMap.mpr ⟨z,List.mem_toFinset.mp hop,?_⟩⟩
      simpa only [hzws,ite_false] using
        (List.mem_filterMap.mpr ⟨kept,hkeep,by simp [show kept.length ≤ n by omega]⟩ :
          ordered (z::kept) ∈ ((keepChoices a b r).filterMap fun kept =>
            if kept.length ≤ n then some (ordered (z :: kept)) else none))
    exact children_ _ mem ((perm_set hp').symm ▸ hraw)
  rcases hm with direct|swap
  · exact go hp direct hs hz
  · exact go (hp.trans (.swap _ _ _)) swap (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)
end SignedProjection

namespace SignedProjection
abbrev V64 := BitVec 64

def bitAt (w : V64) (n : Nat) := w.getLsbD n
def mismatch (g : V64) (ws : List V64) (p q : Nat) :=
  (bitAt g p != bitAt g q) && ws.all (fun w => bitAt w p == bitAt w q)

theorem mismatch_sound {g : V64} {ws : List V64} {p q : Nat} (pp : p < 64) (qq : q < 64)
    (cert : mismatch g ws p q = true) (k : ℕ) : ¬ CoreSigned.live signedOps g k ws.toFinset := by
  intro h
  have parts := Bool.and_eq_true_iff.mp cert
  let D : V64 → Prop := fun w => bitAt w p ≠ bitAt w q
  have dg : D g := by simpa [D] using parts.1
  have hop (a b : V64) (z : V64) (hz : z ∈ signedOps a b) (dz : D z) : D a ∨ D b := by
    by_contra! fail
    apply dz
    obtain ⟨ea,eb⟩ := fail
    simp only [D, not_not] at ea eb
    change bitAt a p = bitAt a q at ea
    change bitAt b p = bitAt b q at eb
    simp only [signedOps, List.mem_toFinset,List.mem_cons, List.not_mem_nil,or_false] at hz
    rcases hz with rfl|rfl|rfl|rfl <;>
      simpa only [bitAt, BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not,
        pp,qq,decide_true, Bool.true_and, show a.getLsbD p = a.getLsbD q from ea,
        show b.getLsbD p = b.getLsbD q from eb]
  obtain ⟨x,hx,dx⟩ := CoreSigned.live_separates D dg hop h
  exact dx (beq_iff_eq.mp (List.all_eq_true.mp parts.2 x (List.mem_toFinset.mp hx)))

end SignedProjection

namespace SignedProjection
abbrev View := Word × Fin 64 × Word × List Word × Nat × (Nat → Nat)
abbrev Node := Nat × Nat × List Word × (Nat → Nat)
def vm (v : View) := v.1
def va (v : View) := v.2.1
def vg (v : View) := v.2.2.1
def vs (v : View) := v.2.2.2.1
def vk (v : View) := v.2.2.2.2.1
def vh (v : View) := v.2.2.2.2.2
def nv (a : Node) := a.1
def nk (a : Node) := a.2.1
def ns (a : Node) := a.2.2.1
def nh (a : Node) := a.2.2.2

def recipeRun : Nat → Nat → List Word → Option (List (Word × Word × Word) × List Word)
  | 0, code, ws => if code = 1 then some ([],ws) else none
  | fuel+1, code, ws => if code = 1 then some ([],ws) else
    let i := code % 16
    let j := (code / 16) % 16
    let o := (code / 256) % 4
    match ws[i]?, ws[j]? with
    | some a, some b => if a = b then none else
      let w := (signedList a b).getD o 0
      match recipeRun fuel (code / 1024) (ws++[w]) with
      | some (rs,ws') => some ((a,b,w)::rs,ws')
      | none => none
    | _,_ => none

theorem recipeRun_sound (fuel code : Nat) (ws : List Word) {rs out}
    (h : recipeRun fuel code ws = some (rs,out)) :
    generated signedOps ws.toFinset rs out.toFinset := by
  induction fuel generalizing code ws rs out with
  | zero =>
    simp only [recipeRun] at h
    split at h
    · cases h; rfl
    · contradiction
  | succ k ih =>
    simp only [recipeRun] at h
    split at h
    · cases h; rfl
    split at h <;> try contradiction
    rename_i a b ha hb
    split at h <;> try contradiction
    rename_i ne
    split at h <;> try contradiction
    rename_i tail end_ ht
    cases h
    set r := (code / 256) % 4
    let w := (signedList a b).getD r 0
    change a ∈ ws.toFinset ∧ b ∈ ws.toFinset ∧ a ≠ b ∧ w ∈ signedOps a b ∧ _
    refine ⟨List.mem_toFinset.mpr (List.mem_of_getElem? ha),
      List.mem_toFinset.mpr (List.mem_of_getElem? hb),ne,?_,?_⟩
    · have hr : r < 4 := Nat.mod_lt _ (by decide)
      change w ∈ (signedList a b).toFinset
      simp only [List.mem_toFinset]
      have hr' : r < (signedList a b).length := by simpa [signedList] using hr
      simpa [w, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr'] using
        (List.getElem_mem (l := signedList a b) (i := r) hr')
    · have eq : (ws++[w]).toFinset = insert w ws.toFinset := by
        ext x
        simp [or_comm]
      rw [← eq]
      exact ih _ _ ht

def ViewOK (v : View) := ¬ CoreSigned.build signedOps (vg v) (vk v) (vs v).toFinset

def cutOK (v : View) (g : Word) (k : Nat) (ws : List Word) (recipe : Nat) : Bool :=
  let p := signedPin (vm v) (va v)
  if p g != vg v || p g == 0 then false else
    match recipeRun 12 recipe (vs v) with
    | none => false
    | some (rs,out) =>
      decide (avail p ws.toFinset ⊆ out.toFinset) &&
      decide (rs.length+k ≤ vk v + lost p ws.toFinset)

theorem cutOK_sound {v : View} {g : Word} {k : Nat} {ws : List Word} {recipe : Nat}
    (hv : ViewOK v) (hc : cutOK v g k ws recipe = true) :
    ¬ CoreSigned.live signedOps g k ws.toFinset := by
  simp only [cutOK] at hc
  split at hc <;> try contradiction
  rename_i ok
  split at hc <;> try contradiction
  rename_i rs out hr
  have parts := Bool.and_eq_true_iff.mp hc
  have good : signedPin (vm v) (va v) g = vg v ∧ signedPin (vm v) (va v) g ≠ 0 := by
    simpa using ok
  apply exclude_cut (vm v) (va v) g k (vk v) ws.toFinset (vs v).toFinset out.toFinset rs good.2
    (good.1 ▸ hv) (recipeRun_sound _ _ _ hr) (of_decide_eq_true parts.1)
    (of_decide_eq_true parts.2)

end SignedProjection
namespace SignedProjection

def quickCut (v : View) (g : Word) (k : Nat) (ws : List Word) (receipt : Nat) : Bool :=
  let p := signedPin (vm v) (va v)
  if p g != vg v || p g == 0 then false else
    match recipeRun 12 receipt (vs v) with
    | none => false
    | some (rs,out) =>
      decide ws.Nodup &&
      ws.all (fun w => p w == 0 || out.contains (p w)) &&
      decide (rs.length+k ≤ vk v + ws.countP (fun w => p w = 0))

theorem quickCut_sound {v : View} {g : Word} {k : Nat} {ws : List Word} {receipt : Nat}
    (hv : ViewOK v) (ok : quickCut v g k ws receipt = true) :
    ¬ CoreSigned.live signedOps g k ws.toFinset := by
  simp only [quickCut] at ok
  split at ok <;> try contradiction
  rename_i good
  split at ok <;> try contradiction
  rename_i rs out hr
  have parts := Bool.and_eq_true_iff.mp ok
  have pp := Bool.and_eq_true_iff.mp parts.1
  have nd := of_decide_eq_true pp.1
  have gg : signedPin (vm v) (va v) g = vg v ∧ signedPin (vm v) (va v) g ≠ 0 := by
    simpa using good
  apply exclude_cut (vm v) (va v) g k (vk v) ws.toFinset (vs v).toFinset out.toFinset rs gg.2
    (gg.1 ▸ hv) (recipeRun_sound _ _ _ hr)
  · intro x hx
    obtain ⟨ne,w,hw,rfl⟩ := (avail_mem _).mp hx
    have has := List.all_eq_true.mp pp.2 w (List.mem_toFinset.mp hw)
    simp only [Bool.or_eq_true,beq_iff_eq,List.contains_iff_mem] at has
    exact List.mem_toFinset.mpr (has.resolve_left ne)
  · unfold lost
    rw [List.Nodup.card_eq_countP nd]
    exact of_decide_eq_true parts.2

end SignedProjection

namespace SignedProjection.QFast
abbrev Table (α : Type) := Nat × (Nat → Option α)
def get {α : Type} (t : Table α) (i : Nat) : Option α := if i < t.1 then t.2 i else none

def checkHint (views : Table View) (nodes : Table Node) (vID : Nat) (g : Word)
    (k : Nat) (ws : List Word) (hint : Nat) : Bool :=
  let val := hint/4
  match hint % 4 with
  | 0 => mismatch g ws (val % 64) ((val/64)%64)
  | 1 => match (get nodes val) with
    | some a => (nv a == vID) && (nk a == k) && (ns a == ws)
    | none => false
  | 2 =>
    let j := val % 1024
    if j < vID then
      match (get views j) with
      | some v => quickCut v g k ws (val/1024)
      | none => false
    else false
  | _ => (k == 0 && ws.toFinset != {g}) || decide (k+1 < ws.toFinset.card)

theorem checkHint_sound {views : Table View} {nodes : Table Node} {vID : Nat} {g : Word}
    {k : Nat} {ws : List Word} {h : Nat}
    (known : ∀ i < vID, ∀ v, (get views i) = some v → ViewOK v)
    (closed : ∀ (i : Nat) (a : Node), (get nodes i) = some a → nv a = vID → nk a = k →
      ¬ CoreSigned.live signedOps g k (ns a).toFinset)
    (ok : checkHint views nodes vID g k ws h = true) : ¬ CoreSigned.live signedOps g k ws.toFinset := by
  simp only [checkHint] at ok
  split at ok
  · exact mismatch_sound (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)) ok k
  · split at ok <;> try contradiction
    rename_i a ha
    simp only [Bool.and_eq_true,beq_iff_eq] at ok
    exact ok.2 ▸ closed _ a ha ok.1.1 ok.1.2
  · split at ok <;> try contradiction
    rename_i lt
    split at ok <;> try contradiction
    rename_i v hv
    exact quickCut_sound (known _ lt _ hv) ok
  · simp only [Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq,bne_iff_ne,decide_eq_true_eq] at ok
    intro h
    rcases ok with ⟨rfl,ne⟩|wide
    · exact ne h
    · exact (Nat.not_lt_of_ge (CoreSigned.live_card h)) wide

def scanFrom {α : Type} (f : Nat → α → Bool) : Nat → List α → Bool
  | _, [] => true
  | i, x::xs => f i x && scanFrom f (i+1) xs

theorem scanFrom_sound {α : Type} (f : Nat → α → Bool) {i : Nat} {xs : List α}
    (ok : scanFrom f i xs = true) {x : α} (hx : x ∈ xs) : ∃ j, f j x = true := by
  induction xs generalizing i with
  | nil => simp at hx
  | cons a xs ih =>
    have parts := Bool.and_eq_true_iff.mp ok
    rcases List.mem_cons.mp hx with rfl|hm
    · exact ⟨_,parts.1⟩
    · exact ih parts.2 hm

def evalNode (views : Table View) (nodes : Table Node) (a : Node) : Bool :=
  match (get views (nv a)) with
  | none => false
  | some v => decide (ns a).Nodup && (ns a != [vg v]) &&
    match nk a with
    | 0 => true
    | k+1 => scanFrom (fun i ws => checkHint views nodes (nv a) (vg v) k ws (nh a i)) 0
               (children k (ns a))

def evalRoot (views : Table View) (nodes : Table Node) (i : Nat) (v : View) : Bool :=
  scanFrom (fun q ws => checkHint views nodes i (vg v) (vk v) ws (vh v q)) 0 (vs v).sublists

theorem view_from_earlier (views : Table View) (nodes : Table Node) (vID : Nat) (v : View)
    (hv : (get views vID) = some v)
    (earlier : ∀ i < vID, ∀ w, (get views i) = some w → ViewOK w)
    (hroots : evalRoot views nodes vID v = true)
    (hnodes : ∀ (i : Nat) (a : Node), (get nodes i) = some a → evalNode views nodes a = true) :
    ViewOK v := by
  have closed (k : Nat) : ∀ (i : Nat) (a : Node), (get nodes i) = some a → nv a = vID → nk a = k →
      ¬ CoreSigned.live signedOps (vg v) k (ns a).toFinset := by
    induction k with
    | zero =>
      intro i a found owner fuel h
      have ok := hnodes i a found
      simp only [evalNode,owner,hv,fuel,Bool.and_true,Bool.and_eq_true,decide_eq_true_eq,bne_iff_ne] at ok
      exact ok.2 (singleton_list ok.1 h)
    | succ k ih =>
      intro i a found owner fuel
      have ok := hnodes i a found
      simp only [evalNode,owner,hv,fuel,Bool.and_eq_true,decide_eq_true_eq,bne_iff_ne] at ok
      apply step_no _ _ _ ok.1.1 ok.1.2
      intro ws hm
      obtain ⟨j,good⟩ := scanFrom_sound _ ok.2 hm
      exact checkHint_sound earlier ih good
  intro build_
  classical
  obtain ⟨S, sub, path⟩ := CoreSigned.compress build_
  let ws := (vs v).filter (· ∈ S)
  have eq : ws.toFinset = S := by
    ext w
    simp only [ws,List.mem_toFinset,List.mem_filter,decide_eq_true_eq,and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (sub hw)
  obtain ⟨q,hq⟩ := scanFrom_sound _ hroots (show ws ∈ (vs v).sublists from
    List.mem_sublists.mpr (List.filter_sublist ..))
  exact checkHint_sound earlier (closed _) hq (eq.symm ▸ path)

theorem whole_sound (views : Table View) (nodes : Table Node)
    (allRoots : ∀ (i : Nat) (v : View), (get views i) = some v → evalRoot views nodes i v = true)
    (allNodes : ∀ (i : Nat) (a : Node), (get nodes i) = some a → evalNode views nodes a = true)
    (i : Nat) (v : View) (hv : (get views i) = some v) : ViewOK v := by
  induction i using Nat.strong_induction_on generalizing v with
  | ind i ih => exact view_from_earlier views nodes i v hv ih (allRoots i v hv) allNodes

def checkRootAt (views : Table View) (nodes : Table Node) (i : Nat) : Bool :=
  match (get views i) with
  | some v => evalRoot views nodes i v
  | none => true

def checkNodeAt (views : Table View) (nodes : Table Node) (i : Nat) : Bool :=
  match (get nodes i) with
  | some a => evalNode views nodes a
  | none => true

def passBlock (check : Nat → Bool) (start : Nat) : Nat → Bool
  | 0 => true
  | n+1 => passBlock check start n && check (start+n)

theorem block_at (check : Nat → Bool) {s n i} (ok : passBlock check s n = true)
    (lo : s ≤ i) (hi : i < s+n) : check i = true := by
  induction n with
  | zero => omega
  | succ n ih =>
    have parts := Bool.and_eq_true_iff.mp ok
    by_cases lt : i < s+n
    · exact ih parts.1 lt
    · have eq : i = s+n := by omega
      exact eq ▸ parts.2

theorem merge_blocks {c : Nat → Bool} {s a b : Nat} (x : passBlock c s a = true)
    (y : passBlock c (s+a) b = true) : passBlock c s (a+b) = true := by
  induction b with
  | zero => simpa using x
  | succ b ih =>
    have parts := Bool.and_eq_true_iff.mp y
    change passBlock c s (a+b) && c (s+(a+b)) = true
    exact Bool.and_eq_true_iff.mpr ⟨ih parts.1,by simpa [Nat.add_assoc] using parts.2⟩

theorem certified_view (views : Table View) (nodes : Table Node)
    (roots : passBlock (checkRootAt views nodes) 0 views.1 = true)
    (states : passBlock (checkNodeAt views nodes) 0 nodes.1 = true)
    {i : Nat} {v : View} (hv : (get views i) = some v) : ViewOK v := by
  apply whole_sound views nodes _ _ i v hv
  · intro j w hw
    have hj : j < views.1 := by by_contra! lo; simp [get, Nat.not_lt_of_ge lo] at hw
    have ok := block_at _ roots (i := j) (Nat.zero_le _) (by omega)
    simpa [checkRootAt,hw] using ok
  · intro j a ha
    have hj : j < nodes.1 := by by_contra! lo; simp [get, Nat.not_lt_of_ge lo] at ha
    have ok := block_at _ states (i := j) (Nat.zero_le _) (by omega)
    simpa [checkNodeAt,ha] using ok

end SignedProjection.QFast


namespace LowerSymSix
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit :=
  ⟨[⟨.and,[3,4]⟩, ⟨.or,[2,6]⟩, ⟨.or,[3,5]⟩, ⟨.and,[1,8]⟩, ⟨.and,[7,9]⟩, ⟨.or,[0,10]⟩, ⟨.or,[2,3]⟩, ⟨.or,[4,5]⟩, ⟨.and,[12,13]⟩, ⟨.or,[1,14]⟩, ⟨.and,[11,15]⟩],16⟩

theorem size : witness.size = 11 := rfl

theorem monotone : Monotone2 witness := by
  simp [Monotone2,witness]

set_option maxRecDepth 16000 in
theorem correct : ∀ x : Fin 6 → Bool, witness.eval (List.ofFn x) =
    Nat.testBit (4008241896 * 2 ^ 32 + 4004038792) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  decide +kernel

end LowerSymSix

namespace Direct64
open PEqualNP.CircuitLowerBounds SignedProjection
abbrev W := BitVec 64
abbrev basicOps (a b : W) := signedOps a b
abbrev goal : W := ~~~0xeee8eae8eea8c888
open CoreSigned (build)
def tableB (x : Fin 6 → Bool) :=
  Nat.testBit (4008241896 * 2 ^ 32 + 4004038792) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def holds (av : Finset W) (z : W) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ ∃ a ∈ av, z = a ∨ z = ~~~a

set_option maxRecDepth 100000 in
theorem holds_insert {av : Finset W} {z a : W} (h : holds av z) : holds (insert a av) z := by
  rcases h with h|h|⟨u,hu,he⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨u,Finset.mem_insert_of_mem hu,he⟩)

set_option maxRecDepth 100000 in
theorem holds_not {av : Finset W} {z : W} (h : holds av z) : holds av (~~~z) := by
  rcases h with rfl|rfl|⟨a,ha,he⟩
  · exact .inr (.inl rfl)
  · exact .inl BitVec.not_not
  · rcases he with he|he <;> rw [he]
    · exact .inr (.inr ⟨a, ha, .inr rfl⟩)
    · exact .inr (.inr ⟨a, ha, .inl BitVec.not_not⟩)

def reachable (av : Finset W) (z : W) : Prop :=
  holds av z ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ w ∈ basicOps a b, holds (insert w av) z

set_option maxRecDepth 100000 in
theorem reachable_not {av : Finset W} {z : W} (h : reachable av z) : reachable av (~~~z) := by
  rcases h with h|⟨a,ha,b,hb,ne,w,hop,hw⟩
  · exact .inl (holds_not h)
  · exact .inr ⟨a,ha,b,hb,ne,w,hop,holds_not hw⟩

set_option maxRecDepth 100000 in
theorem and_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x &&& y) := by
  have const : holds av (0 : W) := .inl rfl
  have oldx := hx
  rcases hx with rfl|rfl|⟨a,ha,ea⟩
  · rw [show (0 : W) &&& y = 0 from BitVec.zero_and]; exact .inl const
  · change reachable av (BitVec.allOnes 64 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 64)
    rw [BitVec.and_allOnes]; exact .inl oldx
  by_cases h : a = b
  · subst b
    rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb] <;>
      simp only [BitVec.and_self, BitVec.and_not_self, BitVec.not_and_self] <;>
      first | exact .inl const | exact .inl (.inr (.inr ⟨a,ha,.inl rfl⟩)) |
        exact .inl (.inr (.inr ⟨a,ha,.inr rfl⟩))
  have add (w : W) (hw : w ∈ basicOps a b) (z : W) (hz : z = w ∨ z = ~~~w) :
      reachable av z :=
    .inr ⟨a,ha,b,hb,h,w,hw,.inr (.inr ⟨w,Finset.mem_insert_self ..,hz⟩)⟩
  rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb]
  · exact add _ (by simp [basicOps,SignedProjection.signedOps] : a &&& b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,SignedProjection.signedOps] : a &&& ~~~b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,SignedProjection.signedOps] : b &&& ~~~a ∈ basicOps a b) _ (.inl (BitVec.and_comm ..))
  · exact add _ (by simp [basicOps,SignedProjection.signedOps] : a ||| b ∈ basicOps a b) _ (.inr BitVec.not_or.symm)

set_option maxRecDepth 100000 in
theorem or_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x ||| y) := by
  simpa only [BitVec.not_and, BitVec.not_not] using reachable_not (and_reach (holds_not hx) (holds_not hy))

private def bit (k : Fin 64) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

set_option maxRecDepth 100000 in
private theorem read_bit (w : List W) (i : ℕ) (k : Fin 64) :
    (w.map (bit k)).getD i false = bit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit]

def legal (g : Gate) : Prop := (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

def action (w : List W) (g : Gate) : W := match g.op with
  | .not => ~~~(g.inputs.head?.map (fun i => w.getD i 0)).getD 0
  | .and => (g.inputs.map fun i => w.getD i 0).foldr (· &&& ·) (~~~0)
  | .or => (g.inputs.map fun i => w.getD i 0).foldr (· ||| ·) 0
  | _ => 0

set_option maxRecDepth 100000 in
theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 64) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (0#64)[k.val] = false; simp
  all_goals rcases hop with rfl|rfl|rfl <;>
    simp only [step, List.map_cons,List.map_nil,read_bit,List.map_append] <;>
    simp only [action, GateOp.eval, List.foldr_cons,List.foldr_nil,List.head?_cons,List.head?_nil,
      List.headD_cons,List.headD_nil,Option.map_some,Option.map_none,Option.getD_some,Option.getD_none,
      List.all_cons,List.all_nil,List.any_cons,List.any_nil,List.map_cons,List.map_nil,id_eq,
      Bool.and_true,Bool.or_false, bit,BitVec.getElem_and,BitVec.getElem_or,BitVec.getElem_not,
      bit0,Bool.not_false]

def isBinary (g : Gate) : Bool := match g.op with
  | .not => false
  | _ => true
def binaryCost (gs : List Gate) := (gs.filter isBinary).length

set_option maxRecDepth 100000 in
theorem available_read {av : Finset W} {w : List W} (hw : ∀ u ∈ w, holds av u) (i : ℕ) :
    holds av (w.getD i 0) := by
  by_cases h : i < w.length
  · exact hw _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt h)]
    exact .inl rfl

set_option maxRecDepth 100000 in
theorem gate_reach (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (g : Gate) (hg : legal g) :
    if isBinary g then reachable av (action w g) else holds av (action w g) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals rcases hop with rfl|rfl|rfl <;> simp only [isBinary,Bool.false_eq_true,ite_false,ite_true,
    action,List.head?_nil,List.head?_cons,List.map_nil,List.map_cons,List.foldr_nil,List.foldr_cons,
    Option.map_none,Option.map_some,Option.getD_none,Option.getD_some,
    show ∀ x : W, x ||| (0 : W) = x from fun x => BitVec.or_zero,
    show ∀ x : W, x &&& ~~~0 = x from fun x => BitVec.and_allOnes]
  all_goals first
    | exact .inl (.inl rfl)
    | exact .inl (.inr (.inl rfl))
    | exact .inr (.inl rfl)
    | exact .inl (available_read hw _)
    | exact holds_not (available_read hw _)
    | exact and_reach (available_read hw _) (available_read hw _)
    | exact or_reach (available_read hw _) (available_read hw _)

set_option maxRecDepth 100000 in
theorem compile (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (he : ∀ k, (gs.foldl step (w.map (bit k))).getD out false = bit k (~~~goal)) :
    ∃ t, (t = goal ∨ t = ~~~goal) ∧ build basicOps t (binaryCost gs) av := by
  induction gs generalizing w av with
  | nil =>
    have hv : w.getD out 0 = ~~~goal := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit, bit] using he ⟨i,hi⟩
    have h := hv ▸ available_read hw out
    rcases h with zero|ones|⟨t,ht,eq|eq⟩
    · exact False.elim ((by decide : ~~~goal ≠ 0) zero)
    · exact False.elim ((by decide : ~~~goal ≠ ~~~0) ones)
    · exact ⟨t, .inr eq.symm, ht⟩
    · exact ⟨t, .inl (by simpa only [BitVec.not_not] using congrArg (fun w : W => ~~~w) eq.symm), ht⟩
  | cons g gs ih =>
    let z := action w g
    have stepOK := action_spec w g (hg g (by simp))
    have nextEval : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false = bit k (~~~goal) := by
      intro k; simpa only [List.foldl_cons, stepOK] using he k
    have tail := ih (fun t ht => hg t (by simp [ht])) (w ++ [z])
    have cont (A : Finset W) (hold : ∀ u ∈ w, holds A u) (new : holds A z) :=
      tail A (by
        intro u hu
        rcases List.mem_append.mp hu with hu|hu
        · exact hold u hu
        · exact (List.mem_singleton.mp hu) ▸ new) nextEval
    have stepClass := gate_reach w av hw g (hg g (by simp))
    cases neg : isBinary g
    · simp only [neg,Bool.false_eq_true,ite_false] at stepClass
      simpa [binaryCost,neg] using cont av hw stepClass
    · simp only [neg,ite_true] at stepClass
      have len : binaryCost (g::gs) = binaryCost gs+1 := by simp [binaryCost,neg]
      rw [len]
      rcases stepClass with existing|⟨a,ha,b,hb,ne,new,op,rep⟩
      · obtain ⟨t,ht,run⟩ := cont av hw existing
        exact ⟨t,ht,Or.inl run⟩
      · obtain ⟨t,ht,run⟩ := cont (insert new av) (fun u hu => holds_insert (hw u hu)) rep
        exact ⟨t,ht,Or.inr ⟨a,ha,b,hb,ne,new,op,run⟩⟩


def cols : List W := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]

theorem sample64 : ∀ k : Fin 64, tableB (fun i => (cols.getD i.val 0)[k.val]) = (~~~goal)[k.val] := by
  decide +kernel

theorem zero_open (k : ℕ) {t : W} (av : Finset W) (hz : ∀ u ∈ av, u.getLsbD 0 = false)
    (h : build basicOps t k av) : t.getLsbD 0 = false := by
  induction k generalizing av with
  | zero => exact hz t h
  | succ k ih =>
    rcases h with skip | ⟨a,ha,b,hb,_,z,hop,tail⟩
    · exact ih av hz skip
    · apply ih (insert z av) _ tail
      intro u hu
      rcases Finset.mem_insert.mp hu with rfl|hu
      · simp only [basicOps,signedOps,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hop
        rcases hop with rfl|rfl|rfl|rfl <;> simp only [BitVec.getLsbD_and,BitVec.getLsbD_or,BitVec.getLsbD_not,hz a ha,hz b hb,Bool.false_and,Bool.or_self]
      · exact hz u hu

theorem low (reject : ¬ build basicOps (0xeee8eae8eea8c888 : W) 9 cols.toFinset)
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = tableB x) : 9 < binaryCost gs := by
  by_contra! low
  have width : cols.length = 6 := rfl
  have init : ∀ u ∈ cols, holds cols.toFinset u := by
    intro u hu
    exact .inr (.inr ⟨u, List.mem_toFinset.mpr hu, .inl rfl⟩)
  have evaluate (k : Fin 64) :
      (gs.foldl step (cols.map (bit k))).getD o false = bit k (~~~goal) := by
    let x (i : Fin 6) : Bool := bit k (cols.getD i.val 0)
    have same : List.ofFn x = cols.map (bit k) := by
      apply List.ext_getElem
      · simp [width]
      · intro i hi hj
        have hlt : i < cols.length := by simpa using hj
        simp only [List.getElem_ofFn, List.getElem_map, x, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hlt, Option.getD_some]
    change Circuit.eval ⟨gs,o⟩ (cols.map (bit k)) = bit k (~~~goal)
    rw [← same, he]
    exact sample64 k
  obtain ⟨t, ht, run⟩ := compile gs o hg cols cols.toFinset init evaluate

  have h0 : ∀ u ∈ cols.toFinset, u.getLsbD 0 = false := by
    intro u hu
    simp only [cols,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel
  rcases ht with rfl|rfl
  · have odd : goal.getLsbD 0 ≠ false := by decide +kernel
    exact odd (zero_open _ _ h0 run)
  · apply reject
    apply pad_build low
    exact run
end Direct64

namespace LowerSymSix
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
theorem finish
    (reject : ¬ CoreSigned.build SignedProjection.signedOps (0xeee8eae8eea8c888 : BitVec 64) 9 Direct64.cols.toFinset) :
∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008241896 * 2 ^ 32 + 4004038792) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008241896 * 2 ^ 32 + 4004038792) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  rintro s ⟨C, hg, hs, he⟩
  by_cases neg : ∃ g ∈ C.gates, g.op = .not
  · obtain ⟨g, hm, op⟩ := neg
    have lo := Direct64.low reject C.gates C.output hg he
    have proper : Direct64.binaryCost C.gates < C.gates.length := by
      apply List.length_filter_lt_length_iff_exists.mpr
      exact ⟨g, hm, by simp [Direct64.isBinary, op]⟩
    have cap : C.gates.length ≤ s := hs
    exact ⟨witness, monotone, by rw [size]; omega, correct⟩
  · refine ⟨C, ?_, hs, he⟩
    intro g hm
    obtain ⟨hop, hin⟩ := hg g hm
    refine ⟨?_, hin⟩
    rcases hop with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (neg ⟨g, hm, h⟩).elim

end LowerSymSix


namespace SignedProjection

def labBlock0 : Array Nat := #[
  1,
  5,
  9,
  12,
  13,
  17,
  21,
  25,
  28,
  29,
  33,
  37
]

def labBlock1 : Array Nat := #[
  41,
  44,
  45,
  49,
  53,
  56,
  57,
  61,
  65,
  69,
  73,
  76
]

def labBlock2 : Array Nat := #[
  77,
  81,
  84,
  85,
  89,
  93,
  97,
  100,
  101,
  104,
  105,
  109
]

def labBlock3 : Array Nat := #[
  113,
  117,
  121,
  125,
  129,
  133,
  137,
  140,
  141,
  145,
  148,
  149
]

def labBlock4 : Array Nat := #[
  152,
  153,
  157,
  161,
  164,
  165,
  169,
  173,
  177,
  181,
  185,
  189
]

def labBlock5 : Array Nat := #[
  193,
  197,
  201,
  204,
  205,
  209,
  212,
  213,
  217,
  221,
  225,
  228
]

def labBlock6 : Array Nat := #[
  229,
  233,
  237,
  241,
  245,
  249,
  253,
  257,
  261,
  265,
  268,
  269
]

def labBlock7 : Array Nat := #[
  273,
  277,
  281,
  284,
  285,
  289,
  293,
  297,
  300,
  301,
  305,
  309
]

def labBlock8 : Array Nat := #[
  313,
  317,
  321,
  325,
  329,
  332,
  333,
  337,
  340,
  341,
  345,
  349
]

def labBlock9 : Array Nat := #[
  353,
  356,
  357,
  361,
  365,
  369,
  373,
  377,
  381,
  385,
  389,
  393
]

def labBlock10 : Array Nat := #[
  396,
  397,
  401,
  404,
  405,
  409,
  413,
  417,
  420,
  421,
  425,
  429
]

def labBlock11 : Array Nat := #[
  433,
  437,
  441,
  445,
  449,
  453,
  457,
  461,
  465,
  469,
  473,
  477
]

def labBlock12 : Array Nat := #[
  481,
  485,
  489,
  493,
  497,
  501,
  505,
  509,
  513,
  517,
  521,
  524
]

def labBlock13 : Array Nat := #[
  525,
  529,
  533,
  537,
  540,
  541,
  545,
  549,
  553,
  556,
  557,
  561
]

def labBlock14 : Array Nat := #[
  565,
  568,
  569,
  573,
  577,
  581,
  585,
  588,
  589,
  593,
  597,
  601
]

def labBlock15 : Array Nat := #[
  605,
  609,
  613,
  616,
  617,
  621,
  625,
  629,
  633,
  637,
  641,
  645
]

def labBlock16 : Array Nat := #[
  649,
  652,
  653,
  657,
  661,
  664,
  665,
  669,
  673,
  677,
  681,
  685
]

def labBlock17 : Array Nat := #[
  689,
  693,
  697,
  701,
  705,
  709,
  713,
  717,
  721,
  725,
  729,
  733
]

def labBlock18 : Array Nat := #[
  737,
  741,
  745,
  749,
  753,
  757,
  761,
  765,
  769,
  773,
  777,
  781
]

def labBlock19 : Array Nat := #[
  785,
  789,
  793,
  797,
  801,
  805,
  809,
  813,
  817,
  821,
  825,
  829
]

def labBlock20 : Array Nat := #[
  833,
  837,
  841,
  845,
  849,
  853,
  857,
  861,
  865,
  869,
  873,
  877
]

def labBlock21 : Array Nat := #[
  881,
  885,
  889,
  893,
  897,
  901,
  905,
  909,
  913,
  917,
  921,
  925
]

def labBlock22 : Array Nat := #[
  929,
  933,
  937,
  941,
  945,
  949,
  953,
  957,
  961,
  965,
  969,
  973
]

def labBlock23 : Array Nat := #[
  977,
  981,
  985,
  989,
  993,
  997,
  1001,
  1005,
  1009,
  1013,
  1017,
  1021
]

def labBlock24 : Array Nat := #[
  1025,
  1029,
  1033,
  1036,
  1037,
  1041,
  1045,
  1049,
  1052,
  1053,
  1057,
  1061
]

def labBlock25 : Array Nat := #[
  1065,
  1069,
  1073,
  1077,
  1080,
  1081,
  1085,
  1089,
  1093,
  1097,
  1101,
  1105
]

def labBlock26 : Array Nat := #[
  1108,
  1109,
  1113,
  1117,
  1121,
  1125,
  1129,
  1133,
  1137,
  1141,
  1145,
  1149
]

def labBlock27 : Array Nat := #[
  1153,
  1157,
  1161,
  1165,
  1169,
  1172,
  1173,
  1176,
  1177,
  1181,
  1185,
  1189
]

def labBlock28 : Array Nat := #[
  1193,
  1197,
  1201,
  1205,
  1208,
  1209,
  1213,
  1217,
  1221,
  1225,
  1229,
  1233
]

def labBlock29 : Array Nat := #[
  1237,
  1241,
  1245,
  1249,
  1253,
  1257,
  1261,
  1265,
  1269,
  1273,
  1277,
  1281
]

def labBlock30 : Array Nat := #[
  1285,
  1289,
  1292,
  1293,
  1297,
  1301,
  1305,
  1308,
  1309,
  1313,
  1317,
  1321
]

def labBlock31 : Array Nat := #[
  1324,
  1325,
  1329,
  1333,
  1336,
  1337,
  1340,
  1341,
  1345,
  1349,
  1353,
  1356
]

def labBlock32 : Array Nat := #[
  1357,
  1361,
  1364,
  1365,
  1369,
  1373,
  1377,
  1381,
  1385,
  1389,
  1393,
  1397
]

def labBlock33 : Array Nat := #[
  1401,
  1405,
  1409,
  1413,
  1417,
  1420,
  1421,
  1425,
  1428,
  1429,
  1433,
  1437
]

def labBlock34 : Array Nat := #[
  1441,
  1445,
  1449,
  1453,
  1457,
  1461,
  1465,
  1469,
  1473,
  1477,
  1481,
  1485
]

def labBlock35 : Array Nat := #[
  1489,
  1493,
  1497,
  1501,
  1505,
  1509,
  1513,
  1517,
  1521,
  1525,
  1529,
  1533
]

def labBlock36 : Array Nat := #[
  1537,
  1541,
  1545,
  1548,
  1549,
  1553,
  1557,
  1561,
  1564,
  1565,
  1569,
  1573
]

def labBlock37 : Array Nat := #[
  1577,
  1580,
  1581,
  1585,
  1589,
  1592,
  1593,
  1597,
  1601,
  1605,
  1609,
  1612
]

def labBlock38 : Array Nat := #[
  1613,
  1617,
  1620,
  1621,
  1625,
  1628,
  1629,
  1633,
  1637,
  1641,
  1645,
  1649
]

def labBlock39 : Array Nat := #[
  1653,
  1657,
  1661,
  1665,
  1669,
  1673,
  1676,
  1677,
  1681,
  1684,
  1685,
  1688
]

def labBlock40 : Array Nat := #[
  1689,
  1693,
  1697,
  1701,
  1705,
  1709,
  1713,
  1717,
  1721,
  1725,
  1729,
  1733
]

def labBlock41 : Array Nat := #[
  1737,
  1741,
  1745,
  1749,
  1753,
  1757,
  1761,
  1765,
  1769,
  1773,
  1777,
  1781
]

def labBlock42 : Array Nat := #[
  1785,
  1789,
  1793,
  1797,
  1801,
  1805,
  1809,
  1813,
  1817,
  1821,
  1825,
  1829
]

def labBlock43 : Array Nat := #[
  1833,
  1837,
  1841,
  1845,
  1849,
  1853,
  1857,
  1861,
  1865,
  1869,
  1873,
  1877
]

def labBlock44 : Array Nat := #[
  1881,
  1885,
  1889,
  1893,
  1897,
  1901,
  1905,
  1909,
  1913,
  1917,
  1921,
  1925
]

def labBlock45 : Array Nat := #[
  1929,
  1933,
  1937,
  1941,
  1945,
  1949,
  1953,
  1957,
  1961,
  1965,
  1969,
  1973
]

def labBlock46 : Array Nat := #[
  1977,
  1981,
  1985,
  1989,
  1993,
  1997,
  2001,
  2005,
  2009,
  2013,
  2017,
  2021
]

def labBlock47 : Array Nat := #[
  2025,
  2029,
  2033,
  2037,
  2041,
  2045,
  2049,
  2053,
  2057,
  2060,
  2061,
  2065
]

def labBlock48 : Array Nat := #[
  2069,
  2073,
  2077,
  2081,
  2085,
  2089,
  2092,
  2093,
  2097,
  2101,
  2104,
  2105
]

def labBlock49 : Array Nat := #[
  2109,
  2113,
  2117,
  2121,
  2125,
  2129,
  2133,
  2137,
  2141,
  2145,
  2148,
  2149
]

def labBlock50 : Array Nat := #[
  2152,
  2153,
  2157,
  2161,
  2165,
  2168,
  2169,
  2173,
  2177,
  2181,
  2185,
  2189
]

def labBlock51 : Array Nat := #[
  2193,
  2197,
  2201,
  2205,
  2209,
  2212,
  2213,
  2217,
  2221,
  2225,
  2229,
  2233
]

def labBlock52 : Array Nat := #[
  2237,
  2241,
  2245,
  2249,
  2253,
  2257,
  2261,
  2265,
  2269,
  2273,
  2277,
  2281
]

def labBlock53 : Array Nat := #[
  2285,
  2289,
  2293,
  2297,
  2301,
  2305,
  2309,
  2313,
  2316,
  2317,
  2321,
  2325
]

def labBlock54 : Array Nat := #[
  2329,
  2332,
  2333,
  2337,
  2341,
  2345,
  2348,
  2349,
  2353,
  2357,
  2360,
  2361
]

def labBlock55 : Array Nat := #[
  2364,
  2380,
  2404,
  2444,
  2452,
  2468,
  2572,
  2588,
  2604,
  2616,
  2636,
  2664
]

def labBlock56 : Array Nat := #[
  2700,
  3084,
  3100,
  3116,
  3128,
  3156,
  3220,
  3340,
  3356,
  3372,
  3384,
  3404
]

def labBlock57 : Array Nat := #[
  3412,
  3428,
  3468,
  3476,
  3492,
  4098,
  4102,
  4106,
  4108,
  4110,
  4114,
  4118
]

def labBlock58 : Array Nat := #[
  4122,
  4126,
  4130,
  4134,
  4138,
  4142,
  4146,
  4150,
  4154,
  4158,
  4162,
  4166
]

def labBlock59 : Array Nat := #[
  4170,
  4172,
  4174,
  4178,
  4180,
  4182,
  4186,
  4190,
  4194,
  4196,
  4198,
  4200
]

def labBlock60 : Array Nat := #[
  4202,
  4206,
  4210,
  4212,
  4214,
  4364,
  4380,
  4428,
  4436,
  4452,
  4556,
  4564
]

def labBlock61 : Array Nat := #[
  4620,
  4636,
  4664,
  4684,
  4700,
  4712,
  4812,
  5132,
  5148,
  5176,
  5196,
  5204
]

def labBlock62 : Array Nat := #[
  5224,
  5332,
  5336,
  5644,
  5660,
  5676,
  5688,
  5708,
  5716,
  5736,
  5752,
  5772
]

def labBlock63 : Array Nat := #[
  5784,
  5836,
  5848,
  6156,
  6188,
  6220,
  6228,
  6244,
  6248,
  6376,
  7224,
  7252
]

def labBlock64 : Array Nat := #[
  7268,
  7272,
  7284,
  7288,
  8204,
  8332,
  8340,
  8344,
  8356,
  8460,
  8492,
  8588
]

def labBlock65 : Array Nat := #[
  8596,
  8612,
  8652,
  8660,
  8676,
  8716,
  8748,
  8760,
  8844,
  8856,
  8876,
  8908
]

def labBlock66 : Array Nat := #[
  9228,
  9244,
  9356,
  9364,
  9368,
  9428,
  9432,
  10252,
  10284,
  10296,
  10380,
  10388
]

def labBlock67 : Array Nat := #[
  10392,
  10404,
  10764,
  10780,
  10796,
  10808,
  10828,
  10856,
  10892,
  10904,
  10916,
  10936
]

def labBlock68 : Array Nat := #[
  10956,
  10984,
  11320,
  11412,
  11416,
  11428,
  11444,
  11448,
  12372,
  12388,
  12620,
  12628
]

def labBlock69 : Array Nat := #[
  12644,
  12684,
  12692,
  12708,
  12748,
  12756,
  12772,
  12876,
  12904,
  12940,
  12952,
  13004
]

def labBlock70 : Array Nat := #[
  13016,
  13032,
  13396,
  13460,
  13464,
  13524,
  13528,
  14436,
  14440,
  14564,
  14568,
  4259922
]

def labBlock71 : Array Nat := #[
  4259926,
  4259930,
  4259934,
  4259938,
  4259946,
  4325402,
  4325458,
  4325474,
  4325482,
  4329510,
  4329554,
  4329570
]

def labBlock72 : Array Nat := #[
  4329578,
  4390942,
  4390994,
  4395090,
  4399146,
  4399158,
  5308498,
  5308502,
  5308506,
  5308510,
  5308514,
  5308522
]

def labBlock73 : Array Nat := #[
  5373990,
  5374018,
  5374034,
  5374038,
  5374042,
  5374046,
  5374050,
  5374058,
  5378074,
  5378130,
  5378138,
  5378146
]

def labBlock74 : Array Nat := #[
  5378154,
  5439570,
  5439574,
  5439578,
  5439582,
  5443614,
  5443666,
  5443674,
  5443694,
  5447706,
  5447710,
  5447718
]

def labBlock75 : Array Nat := #[
  5447746,
  5447762,
  5447766,
  5447770,
  5447774,
  5509222,
  6357074,
  6357078,
  6357082,
  6357086,
  6357090,
  6357098
]

def labBlock76 : Array Nat := #[
  6422554,
  6422610,
  6422618,
  6422626,
  6422634,
  6426662,
  6426690,
  6426706,
  6426710,
  6426714,
  6426718,
  6426722
]

def labBlock77 : Array Nat := #[
  6426730,
  6488094,
  6488146,
  6488154,
  6488174,
  6492242,
  6492246,
  6492250,
  6492254,
  6496282,
  6496338,
  6553702
]

def labBlock78 : Array Nat := #[
  7405650,
  7405654,
  7405658,
  7405662,
  7405666,
  7405674,
  7471142,
  7471186,
  7471202,
  7471210,
  7475226,
  7475282
]

def labBlock79 : Array Nat := #[
  7475298,
  7475306,
  7536722,
  7540766,
  7540818,
  7544862,
  7544914,
  4364238930,
  4364238938,
  4365287506,
  4365287514,
  4640014418
]

def labBlock80 : Array Nat := #[
  4640014426,
  4644208722,
  4644208730,
  4648403026,
  5435883602,
  5435883610,
  5437980754,
  5437980762,
  5439029330,
  5439029338,
  5712707666,
  5712707674
]

def labBlock81 : Array Nat := #[
  5716901970,
  5716901978,
  5721096274,
  5721096282,
  6786449490,
  6786449498,
  6790643794,
  6790643802,
  6794838098,
  7585464402,
  7861239890,
  7861239898
]

def labBlock82 : Array Nat := #[
  7865434194,
  7865434202,
  7869628498,
  7869628506
]

def labGet (i : Nat) : Option Nat :=
  if i < 492 then
    if i < 240 then
      if i < 120 then
        if i < 60 then
          if i < 24 then
            if i < 12 then
              labBlock0[(i-0)]?
            else
              labBlock1[(i-12)]?
          else
            if i < 36 then
              labBlock2[(i-24)]?
            else
              if i < 48 then
                labBlock3[(i-36)]?
              else
                labBlock4[(i-48)]?
        else
          if i < 84 then
            if i < 72 then
              labBlock5[(i-60)]?
            else
              labBlock6[(i-72)]?
          else
            if i < 96 then
              labBlock7[(i-84)]?
            else
              if i < 108 then
                labBlock8[(i-96)]?
              else
                labBlock9[(i-108)]?
      else
        if i < 180 then
          if i < 144 then
            if i < 132 then
              labBlock10[(i-120)]?
            else
              labBlock11[(i-132)]?
          else
            if i < 156 then
              labBlock12[(i-144)]?
            else
              if i < 168 then
                labBlock13[(i-156)]?
              else
                labBlock14[(i-168)]?
        else
          if i < 204 then
            if i < 192 then
              labBlock15[(i-180)]?
            else
              labBlock16[(i-192)]?
          else
            if i < 216 then
              labBlock17[(i-204)]?
            else
              if i < 228 then
                labBlock18[(i-216)]?
              else
                labBlock19[(i-228)]?
    else
      if i < 360 then
        if i < 300 then
          if i < 264 then
            if i < 252 then
              labBlock20[(i-240)]?
            else
              labBlock21[(i-252)]?
          else
            if i < 276 then
              labBlock22[(i-264)]?
            else
              if i < 288 then
                labBlock23[(i-276)]?
              else
                labBlock24[(i-288)]?
        else
          if i < 324 then
            if i < 312 then
              labBlock25[(i-300)]?
            else
              labBlock26[(i-312)]?
          else
            if i < 336 then
              labBlock27[(i-324)]?
            else
              if i < 348 then
                labBlock28[(i-336)]?
              else
                labBlock29[(i-348)]?
      else
        if i < 420 then
          if i < 384 then
            if i < 372 then
              labBlock30[(i-360)]?
            else
              labBlock31[(i-372)]?
          else
            if i < 396 then
              labBlock32[(i-384)]?
            else
              if i < 408 then
                labBlock33[(i-396)]?
              else
                labBlock34[(i-408)]?
        else
          if i < 456 then
            if i < 432 then
              labBlock35[(i-420)]?
            else
              if i < 444 then
                labBlock36[(i-432)]?
              else
                labBlock37[(i-444)]?
          else
            if i < 468 then
              labBlock38[(i-456)]?
            else
              if i < 480 then
                labBlock39[(i-468)]?
              else
                labBlock40[(i-480)]?
  else
    if i < 744 then
      if i < 612 then
        if i < 552 then
          if i < 516 then
            if i < 504 then
              labBlock41[(i-492)]?
            else
              labBlock42[(i-504)]?
          else
            if i < 528 then
              labBlock43[(i-516)]?
            else
              if i < 540 then
                labBlock44[(i-528)]?
              else
                labBlock45[(i-540)]?
        else
          if i < 576 then
            if i < 564 then
              labBlock46[(i-552)]?
            else
              labBlock47[(i-564)]?
          else
            if i < 588 then
              labBlock48[(i-576)]?
            else
              if i < 600 then
                labBlock49[(i-588)]?
              else
                labBlock50[(i-600)]?
      else
        if i < 672 then
          if i < 636 then
            if i < 624 then
              labBlock51[(i-612)]?
            else
              labBlock52[(i-624)]?
          else
            if i < 648 then
              labBlock53[(i-636)]?
            else
              if i < 660 then
                labBlock54[(i-648)]?
              else
                labBlock55[(i-660)]?
        else
          if i < 708 then
            if i < 684 then
              labBlock56[(i-672)]?
            else
              if i < 696 then
                labBlock57[(i-684)]?
              else
                labBlock58[(i-696)]?
          else
            if i < 720 then
              labBlock59[(i-708)]?
            else
              if i < 732 then
                labBlock60[(i-720)]?
              else
                labBlock61[(i-732)]?
    else
      if i < 864 then
        if i < 804 then
          if i < 768 then
            if i < 756 then
              labBlock62[(i-744)]?
            else
              labBlock63[(i-756)]?
          else
            if i < 780 then
              labBlock64[(i-768)]?
            else
              if i < 792 then
                labBlock65[(i-780)]?
              else
                labBlock66[(i-792)]?
        else
          if i < 828 then
            if i < 816 then
              labBlock67[(i-804)]?
            else
              labBlock68[(i-816)]?
          else
            if i < 840 then
              labBlock69[(i-828)]?
            else
              if i < 852 then
                labBlock70[(i-840)]?
              else
                labBlock71[(i-852)]?
      else
        if i < 924 then
          if i < 888 then
            if i < 876 then
              labBlock72[(i-864)]?
            else
              labBlock73[(i-876)]?
          else
            if i < 900 then
              labBlock74[(i-888)]?
            else
              if i < 912 then
                labBlock75[(i-900)]?
              else
                labBlock76[(i-912)]?
        else
          if i < 960 then
            if i < 936 then
              labBlock77[(i-924)]?
            else
              if i < 948 then
                labBlock78[(i-936)]?
              else
                labBlock79[(i-948)]?
          else
            if i < 972 then
              labBlock80[(i-960)]?
            else
              if i < 984 then
                labBlock81[(i-972)]?
              else
                labBlock82[(i-984)]?

def hint (s d code i : Nat) : Nat :=
  let k := (code >>> (s*i)) % (2^s)
  (labGet ((d >>> (10*k)) % 1024)).getD 3

def viewBlock0 : Array View := #[
  ⟨0xff00000000,⟨32,by decide⟩,0xe800000000,[0xaa00000000, 0xcc00000000, 0xf000000000],3,hint 3 0x314c330b0ac00 0x111711⟩,
  ⟨0xff000000000000,⟨48,by decide⟩,0xe8000000000000,[0xaa000000000000, 0xcc000000000000, 0xf0000000000000],3,hint 3 0x347d07400fc01 0x111711⟩,
  ⟨0xf0f0000,⟨16,by decide⟩,0xe080000,[0xa0a0000, 0xc0c0000, 0xf000000],3,hint 3 0x2dfb66d705c02 0x111711⟩,
  ⟨0xf0f000000000000,⟨48,by decide⟩,0xe08000000000000,[0xa0a000000000000, 0xc0c000000000000, 0xf00000000000000],3,hint 3 0x347d0b400fc04 0x111711⟩,
  ⟨0xf000f00,⟨8,by decide⟩,0xe000800,[0xa000a00, 0xc000c00, 0xf000000],3,hint 3 0x29ca5a8e03405 0x111711⟩,
  ⟨0xf0000000f0,⟨4,by decide⟩,0xe000000080,[0xa0000000a0, 0xc0000000c0, 0xf000000000],3,hint 3 0x1b86516f02006 0x111711⟩,
  ⟨0xffff0000,⟨16,by decide⟩,0xeea80000,[0xaaaa0000, 0xcccc0000, 0xf0f00000, 0xff000000],4,hint 3 0xb7ed9b62d7acc17 0x350750950750⟩,
  ⟨0xffff00000000,⟨32,by decide⟩,0xeae800000000,[0xaaaa00000000, 0xcccc00000000, 0xf0f000000000, 0xff0000000000],4,hint 3 0xc530dc330bac42b 0x350750950750⟩,
  ⟨0xffff000000000000,⟨48,by decide⟩,0xeee8000000000000,[0xaaaa000000000000, 0xcccc000000000000, 0xf0f0000000000000, 0xff00000000000000],4,hint 3 0xd1f42d0740ac83f 0x350750950750⟩,
  ⟨0xff00ff00,⟨8,by decide⟩,0xee00c800,[0xaa00aa00, 0xcc00cc00, 0xf000f000, 0xff000000],4,hint 3 0xada9da7296a380d 0xac88c84c88c8⟩,
  ⟨0xff000000ff,⟨0,by decide⟩,0xe800000088,[0xaa000000aa, 0xcc000000cc, 0xf0000000f0, 0xff00000000],4,hint 3 0x30cac59426c7b14803 0xac8cc88c84c8⟩,
  ⟨0xff000000ff00,⟨8,by decide⟩,0xea000000c800,[0xaa000000aa00, 0xcc000000cc00, 0xf0000000f000, 0xff0000000000],3,hint 3 0xa769ca668e03407 0x111b11711b11⟩
]

def viewBlock1 : Array View := #[
  ⟨0xff000000ff0000,⟨16,by decide⟩,0xe8000000a80000,[0xaa000000aa0000, 0xcc000000cc0000, 0xf0000000f00000, 0xff000000000000],4,hint 3 0xbdadfb62d7ac817 0x310710b10710⟩,
  ⟨0xf0f0f0f,⟨0,by decide⟩,0xe080808,[0xa0a0a0a, 0xc0c0c0c, 0xf000f00, 0xf0f0000],4,hint 3 0x2d9ace9626c6d14803 0xac8cc88c84c8⟩,
  ⟨0xf0f0f0f0,⟨4,by decide⟩,0xe0a0c080,[0xa0a0a0a0, 0xc0c0c0c0, 0xf000f000, 0xf0f00000],3,hint 3 0x705b86096f02408 0x310b10710b10⟩,
  ⟨0xf0f0f0f00000000,⟨32,by decide⟩,0xe080a0800000000,[0xa0a0a0a00000000, 0xc0c0c0c00000000, 0xf000f0000000000, 0xf0f000000000000],4,hint 3 0xcc714c370bad42b 0x310710b10710⟩,
  ⟨0xf0f00000f0f0,⟨4,by decide⟩,0xe0e00000c080,[0xa0a00000a0a0, 0xc0c00000c0c0, 0xf0000000f000, 0xf0f000000000],4,hint 3 0xaddc16e1945bc08 0xac88c84c88c8⟩,
  ⟨0xf000f000f000f0,⟨4,by decide⟩,0xe000e000a00080,[0xa000a000a000a0, 0xc000c000c000c0, 0xf0000000f00000, 0xf000f000000000],4,hint 3 0xaddb8651825bc08 0xb08508708508⟩,
  ⟨0xf000f000f000f00,⟨8,by decide⟩,0xe000a000e000800,[0xa000a000a000a00, 0xc000c000c000c00, 0xf0000000f000000, 0xf000f0000000000],4,hint 3 0xada9ca6696a380d 0xb08508708508⟩,
  ⟨0x4444444444444444,⟨2,by decide⟩,0x4440404044004000,[0x4040404040404040, 0x4400440044004400, 0x4444000044440000, 0x4444444400000000],3,hint 3 0xa7e9d77dc10440a 0x111b11711b11⟩,
  ⟨0xffffffff,⟨0,by decide⟩,0xeea8c888,[0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],7,hint 3 0xa75c1608a926c5202c03 0x2d0ed0cd08d0ad0ed0cd08d0⟩,
  ⟨0xffffffff00000000,⟨32,by decide⟩,0xeee8eae800000000,[0xaaaaaaaa00000000, 0xcccccccc00000000, 0xf0f0f0f000000000, 0xff00ff0000000000, 0xffff000000000000],6,hint 3 0x331c530dc330b3ac2b 0x350750950750d50750950750⟩,
  ⟨0xffff0000ffff,⟨0,by decide⟩,0xeae80000c888,[0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000],7,hint 3 0xa75c1650f42a49b14803 0x888e88c88688a88e88c88688⟩,
  ⟨0xffff0000ffff0000,⟨16,by decide⟩,0xeee80000eea80000,[0xaaaa0000aaaa0000, 0xcccc0000cccc0000, 0xf0f00000f0f00000, 0xff000000ff000000, 0xffff000000000000],6,hint 3 0x2f6b7ed9b62d773017 0x350750950750d50750950750⟩
]

def viewBlock2 : Array View := #[
  ⟨0xff00ff00ff00ff,⟨0,by decide⟩,0xe800e800a80088,[0xaa00aa00aa00aa, 0xcc00cc00cc00cc, 0xf000f000f000f0, 0xff000000ff0000, 0xff00ff00000000],6,hint 3 0xb61d66518226c6814803 0xcc8ec88c84c8ac8ec88c84c8⟩,
  ⟨0xff00ff00ff00ff00,⟨8,by decide⟩,0xee00ea00ee00c800,[0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],5,hint 3 0x2bba769ca6696a380d 0xd08b08508b08708b08508b08⟩,
  ⟨0xf0f0f0f0f0f0f0f,⟨0,by decide⟩,0xe080a080e080808,[0xa0a0a0a0a0a0a0a, 0xc0c0c0c0c0c0c0c, 0xf000f000f000f00, 0xf0f00000f0f0000, 0xf0f0f0f00000000],6,hint 3 0xb6699a59e226c6d14803 0x8c8ec8ac84c8cc8ec8ac84c8⟩,
  ⟨0xf0f0f0f0f0f0f0f0,⟨4,by decide⟩,0xe0e0e0e0e0a0c080,[0xa0a0a0a0a0a0a0a0, 0xc0c0c0c0c0c0c0c0, 0xf000f000f000f000, 0xf0f00000f0f00000, 0xf0f0f0f000000000],5,hint 3 0x2c2705b8651825bc08 0xd08b08508b08708b08508b08⟩,
  ⟨0xcccccccccccccccc,⟨2,by decide⟩,0xccc8c8c8cc88c888,[0x8888888888888888, 0xc0c0c0c0c0c0c0c0, 0xcc00cc00cc00cc00, 0xcccc0000cccc0000, 0xcccccccc00000000],4,hint 3 0x2c6a7e9d77dc104403 0xc20408a20408620408a20408⟩,
  ⟨0x5555555555555555,⟨0,by decide⟩,0x4440404044004000,[0x4444444444444444, 0x5050505050505050, 0x5500550055005500, 0x5555000055550000, 0x5555555500000000],4,hint 4 0xb1aa4a7e9d929df705302a411 0x98653210786532104865321078653210⟩,
  ⟨0xffffffffffffffff,⟨0,by decide⟩,0xeee8eae8eea8c888,[0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000],9,hint 4 0x29d7adc1651822a49b14803 0x7210821062103210421082106210321052108210621032104210821062103210⟩
]

def viewGet (i : Nat) : Option View :=
  if i < 12 then
    viewBlock0[(i-0)]?
  else
    if i < 24 then
      viewBlock1[(i-12)]?
    else
      viewBlock2[(i-24)]?

def nodeBlock0 : Array Node := #[
  ⟨0,3,[0xaa00000000, 0xcc00000000, 0xf000000000],hint 3 0xc731bc5714c330b0b82b 0x5576fda9a8e6a7372cc84e225be⟩,
  ⟨1,3,[0xaa000000000000, 0xcc000000000000, 0xf0000000000000],hint 3 0xd3b4dd2347d07401083f 0x5576fda9a8e6a7372cc84e225be⟩,
  ⟨2,3,[0xa0a0000, 0xc0c0000, 0xf000000],hint 3 0xbf2fbb86dfb66d707c17 0x5576fda9a8e6a7372cc84e225be⟩,
  ⟨3,3,[0xa0a000000000000, 0xc0c000000000000, 0xf00000000000000],hint 3 0xd4b51d2747d0b4011c3f 0x5576fda9a8e6a7372cc84e225be⟩,
  ⟨4,3,[0xa000a00, 0xc000c00, 0xf000000],hint 3 0xbf2fba7e9ca5a8e07c0d 0x5576fda9a8e6a7372cc84e225be⟩,
  ⟨5,3,[0xa0000000a0, 0xc0000000c0, 0xf000000000],hint 3 0xc731b77db86516f0b808 0x5576fda9a8e6a7372cc84e225be⟩,
  ⟨11,3,[0xaa000000aa00, 0xcc000000cc00, 0xf0000000f000, 0xff0000000000],hint 4 0x335ccb29ca2a9a929da7299a38340440d 0x64a634b33183529556c50037⟩,
  ⟨14,3,[0xa0a0a0a0, 0xc0c0c0c0, 0xf000f000, 0xf0f00000],hint 4 0x2ffbfaeebb2a8a91c16e1825bc1a04408 0x64a634b33183529556c50037⟩,
  ⟨19,3,[0x4040404040404040, 0x4400440044004400, 0x4444000044440000, 0x4444444400000000],hint 4 0x346d132bca6eeb869fa75df7043008411 0x64a634b33183529556c50037⟩,
  ⟨20,7,[0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],hint 6 0x2eeb9edfb72d9b62d7b56bfaeeb8adab3a929fa769ca6a96a3a84705b86cd825bd6a390dd354ce2fcbb2d8af2b4a9294a02789b24c862087d1d06819c65170571484103003 0xb61921b3279eb329366e17a1aa77a7b31908b3179eba7927af1852b67c92b67861bb1cb1683a03b30786b30a2f643783603843b63c85b638625c3c83b839c359dc4455d9dcb83c434ce78eb34a14b347b33cea0e34ec8eb66851b66ca530e84eb8ec4e2e09d02a0c5fb8e9ce2750c01cea4008e0c3075a69⟩,
  ⟨20,6,[0x88888888, 0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],hint 6 0xbfefebf2fbbbae7b66d8b22c0afebbae2aaa929fa7696929c1609384c0a926c68148400f83d0f0390d8350cc320c42c0a827098230781b050130481003c0e 0x1e81eadd76b82d79d7a1761aa062a75d86086a79a86b6a179eaabaa38a3bdd76f8b08dd8d679b8eb6e379e56baef85f8ea7e3861beaa9475cb2272c75d4e28acaecb9e7aeaf1b1e7aeaa9b2186caaaba186c0ac0238d246440f3a575d94d94c75d2ca26679e98898779e9c69e8861a051278610c25e58d7040665b19⟩,
  ⟨20,5,[0x22222222, 0x88888888, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],hint 5 0x2ffbfaeeb9edcb66d8b22b8aaaa4a7e9da6a4a705b3609384c0af2a4a52809b1a003 0x169c2dc14b8a55d209cc0e75d58c75046b084468843508004212fbaf4b9ba8e8c242⟩
]

def nodeBlock1 : Array Node := #[
  ⟨20,5,[0x22222222, 0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],hint 5 0x2febbae7b72d9b62a4a7e9da6a4a705b3609302bca9294a026c6814803 0x2d355b849718cb8c1368210b9318e88cf318cad18c8a180704bd2f92e4b8ba2e08683⟩,
  ⟨20,5,[0x44444444, 0x88888888, 0xaaaaaaaa, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],hint 5 0x2ffbfaeeb9ed9b62d5b22b8aaaa4a7e9da124a705825a9384c0a91a0651705714803 0x16ac2dc5538c65d50853eebd2e6eab824a0423684224840082b3039d76631d58c241⟩,
  ⟨20,5,[0x44444444, 0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],hint 5 0x2ffbbae7b66d8b56c8a929fa7684705825a9382a49b1a0651705714803 0x2d555b4aa69ceb904910846c084490a10a751765c1b268034729ca5cd736c9b2784c6⟩,
  ⟨20,5,[0xaaaaaaaa, 0xcccccccc, 0xf8f8f8f8, 0xff00ff00, 0xffff0000],hint 5 0x2ffbfafcbeeefbbaebb9ed9b62a9a9ea4a7e9da59c7705bd6cd825fd745a9232a49b1a052 0x5b5744228dbad0b721d368668439ae9ac6ea0dcb5ce932bcba41f4fd95052acb2a1a4b89685d3805980ae2ea734a1387b308b25e94d1395ab34e2569ccc49709334e5cea9489811252d610⟩,
  ⟨20,5,[0x88888888, 0xaaaaaaaa, 0xcccccccc, 0xf8f8f8f8, 0xff00ff00, 0xffff0000],hint 5 0x2ffbfaeeb9ed9b62c8afeaaa929fa764a705b36096a4e1302a4680641805815 0xb4d96d225a52ae6f4dde632e8c636673a5d55e1726cdb57c0691242b02e2d4214a⟩,
  ⟨20,4,[0xaaaaaaaa, 0xcccccccc, 0xf8f8f8f8, 0xff88ff88, 0xffff0000],hint 5 0xbfefebbad9b62aba9ea4a869fa769aa11c16cd825a9382a468 0x3122648089084cf6ba4d18db039daf1088a29666421e95adac⟩,
  ⟨20,4,[0x77007700, 0xaaaaaaaa, 0xcccccccc, 0xf8f8f8f8, 0xffff0000],hint 5 0xbfefebbaebb62a7a929d71dc16cd825fd6a4c1232a49b1a052 0x6050c31e46000cf4ae091092c210cd5222a18d4f299c652669⟩,
  ⟨20,4,[0xaaaaaaaa, 0xcccccccc, 0xf8f8f8f8, 0xff00ff00, 0xffff8888],hint 5 0xbfefebbaedbaee3b72d9b62d5a929fa75c16cd825a9302a468 0x3122638087084cb18e49108cc528eb295e87c26f6b5e7739e9⟩,
  ⟨20,4,[0x77770000, 0xaaaaaaaa, 0xcccccccc, 0xf8f8f8f8, 0xff00ff00],hint 5 0xbfefebbaebb62a7a929d705bd6cd825d16a4e1232a49b1a052 0x18d6f31dc6000cf4aa691092c210cd42e2b0b10c41a462a609⟩,
  ⟨20,5,[0x70707070, 0x88888888, 0xaaaaaaaa, 0xcccccccc, 0xff00ff00, 0xffff0000],hint 5 0x2ffbfaeeb9ed9b62c8b02b6aceaaa929fa764a705824e1302a49b1a0520741c 0x94592d45da6326873a1954e1356b8287a009824422116342ca54cd4a5cd729ae2b⟩,
  ⟨20,4,[0x70707070, 0x77007700, 0xaaaaaaaa, 0xcccccccc, 0xffff0000],hint 5 0x2eeb72d8b56a4a769aa124a705b36096a4c0af2a49b1a06514803 0x8a2121a64000305a68b385a1591c478d2f605017914429572⟩,
  ⟨20,4,[0x70707070, 0x77770000, 0xaaaaaaaa, 0xcccccccc, 0xff00ff00],hint 5 0x2eeb72d8b56a4a769aa124a705b36096a4e0a92949b1a05c14803 0x89a1215c4000304ae8b486213926431972605017914478d2f⟩
]

def nodeBlock2 : Array Node := #[
  ⟨20,5,[0x88008800, 0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],hint 5 0x2eeb72d8b56c0afeb8a929da729aa3a84705b36096a4c0af2a4a026c68194571482208003 0x1ede3e866d1297e865c8c6b80c6460cead9cef91ce871c001d44db342fbd31488e67⟩,
  ⟨20,4,[0x77007700, 0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xffff0000],hint 5 0xbbadcb62d5a929da6a84705b36096a4c0af2a4a026c681945714803 0x8117008e41089412a28529985000316aead39db3485c1695e5⟩,
  ⟨20,4,[0x77ff0000, 0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00],hint 5 0x2eeb72d8b56a4a769aa11c16cd825a8af2a4a52809b1a0651705714803 0x4a5d408de1089613220631da60003263ace2c5912066151aa6⟩,
  ⟨20,5,[0x88888888, 0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff88ff88, 0xffff0000],hint 5 0x2ffbfaeeb9ed9b62c8adaaaa929fa769aa124a705824e1302a4680942408015 0x94592d221a52a66f45de63268a536673a1d54e1326cdb57c068120298b40d5ad8c⟩,
  ⟨20,4,[0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff88ff88, 0xffff8888],hint 5 0xbfefebdeeeb72d9b62d5b22aaa929fa769aa124a705822a468 0x18a03380470846d296496306e210ed318487be6359da78c549⟩,
  ⟨20,4,[0x77770000, 0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff88ff88],hint 5 0x2febbad9b62a7a929da6e9aa26848f5c1609382a49b1a052 0x18ccf00110425c81094652dea39d0d29a260b0ac2a248228aa⟩,
  ⟨20,5,[0x77007700, 0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xffff0000],hint 5 0x2fbbbae7b7edcb66d8b5ed5a929fa769aa5a84705b86cd825bd6a4c0af2a4a026c681945714803 0x9b2788930c64e330d03760ef4b05810cc2bc0973507012b0bba236cd16852e0ae999d869665e0405a80a10f2b57c5f963331ebd8fcccefc1df37e718cd52f085f5864217f9f92973e93ca5⟩,
  ⟨20,5,[0x77007700, 0x88888888, 0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xffff0000],hint 5 0x2ffbfaeeb9ed9b62c8aeeaaa929fa764a705824e1302a49b1a0520a42807016 0xd2a9af55dec636694a9d26cdb57c06a1282d034843196ab2ce75cd085d175c2e2b⟩,
  ⟨20,4,[0x77007700, 0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xffff8888],hint 5 0x2ffbbaebb76dcb62d6b56b4a929fa75c1609302a49b1a052 0x384a7001695b0eb109c873e0e529693162618ccd22ccb33a4e⟩,
  ⟨20,4,[0x77007700, 0x77770000, 0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0],hint 5 0x2eeb72d8b56a4a769aa11c16cd825a9384c0a92809b1a05714803 0x892121564000301bd4f506214126431992385a1611c462a8c⟩,
  ⟨20,5,[0x77007700, 0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],hint 5 0x2fbb72d8b56a4a769ca5a8e705b36096a2bca52809b1a0651705714803 0x1eb7ae255c6918d0249842390422504c9a98c8b18c7618000c9eb7adad8d234905c1b1a06⟩,
  ⟨20,5,[0x88880000, 0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],hint 5 0x2eeb7edcb62d7b56c0afebba929da6a84705b36096a4e0a9294a026c68170571482f0b403 0x1ede3e466c94a7e46db8c6580c6460cebd1ce989ce871c001cc4d0be8facad2c0f67⟩
]

def nodeBlock3 : Array Node := #[
  ⟨20,4,[0x7700ff00, 0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xffff0000],hint 5 0x2eeb72d8b56a4a769aa11c16cd825a8af2a4a52809b1a0651705714803 0x89591092610896132aa631da600032732ce4a5d4185e141a06⟩,
  ⟨20,4,[0x77770000, 0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00],hint 5 0xbbadcb62d5a929da6a84705b36096a4e0a9294a026c681705714803 0x421b308dc10894129de529985000315b6ad241705864149685⟩,
  ⟨20,5,[0x88888888, 0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff8888],hint 5 0x2ffbfaeeb9edcb66d8b56c8aceaaa929fa764a705824e1302a4680bc2809018 0x94592b221652a64d45da63266a52e473a1954e1305c9756b868124297ac0b8c694⟩,
  ⟨20,5,[0x77770000, 0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00],hint 5 0x2fcbbae7b72d9b62d5a929fa769ca6a96a3a84705b86cd825bd6a4e0a9294a026c681705714803 0xcbd15d22af7e7590bc31d0e2f807410d42bc8975507212e8b479e9a995e52e4aea99d9696a5e0405b80a10f2f7669927be5aeb1ef9648cad59964ab567996086dec3021b712c2959cdd8a5⟩,
  ⟨20,5,[0x77770000, 0x88888888, 0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00],hint 5 0x2ffbfaeeb9ed9b62c8ae2aaa929fa764a705824e1302a49b1a0520a42507419 0x73ae6842e8c636755e1726cdb57c06b12c2d034843194bb2cad5354fbbd2953a2a⟩,
  ⟨20,5,[0x77770000, 0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],hint 5 0xbf2e7b7ed9b62d7a929da6a84705b36096a2bca9294a026c651705714803 0x1b4a36139c1086cc24b842370422504a9b14a7794a6614000c56ba368d9c270b8641b16a5⟩,
  ⟨20,5,[0x88888888, 0xaaaaaaaa, 0xeeeeeeee, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],hint 5 0x2febf2f0bbae7b62d5aaaa4a7692a1258929ca705825e16a4c0a926c681945c15c520e037 0x1accb66664d086de90e5129685ef9eeae6574d5aef394b14116c21122210d42008e2⟩,
  ⟨20,4,[0x66666666, 0xaaaaaaaa, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],hint 5 0xbfaeeb62d5ad2a4a76848f5c16096a48ca91a05c15c5205c0d02003 0x62e8c79d6f4219300e20009a00052024aa4238c4228a480080⟩,
  ⟨20,4,[0x88888888, 0xaaaaaaaa, 0xee00ee00, 0xf0f0f0f0, 0xffff0000],hint 5 0x2e7b96d8b56c8aaa9da4a84609785a9384c0681945c15c5204403 0x1c65b8eb99c213c9e85be0e6b68751c45888434884460800⟩,
  ⟨20,5,[0x88888888, 0xcccccccc, 0xeeeeeeee, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],hint 5 0xbeef0bbae7b72d8b36c8aaaa4a769aa49ca705b3609784e0af2a4a52809b1a0520ec3a 0x1abcb6235c4e76d929585b56e2348ee6b74d4a6e9ef8da52222e421a042158401042⟩,
  ⟨20,4,[0x66666666, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],hint 5 0x2eeb72d8ad2a4a769a8f5c16cd8248caf2a4a52809b1a05205c0d02003 0x732ce895914a5d400e60009e0005603554634106334e690080⟩,
  ⟨20,4,[0x88888888, 0xcccccccc, 0xeeee0000, 0xf0f0f0f0, 0xff00ff00],hint 5 0xbc2eeb72d8a929da6a4a729c16cd384c0af2a4a52809b06803 0xa55410a9282e438e754d8c741e85bc44688434884688800⟩
]

def nodeBlock4 : Array Node := #[
  ⟨20,5,[0x88888888, 0xaaaa0000, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],hint 5 0xbfefebc2eeb9edfb72d9b62c8ae2a4a7e9da6a58929c16cd384c0a9294a026c03 0x44ac86462c2111172b0e295124a59131aa8ca20c8b2aebb82d9842358422384000d1e1⟩,
  ⟨20,5,[0x55550000, 0x88888888, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],hint 5 0x2fcbeee7b7ed9b62cdb22b8a96a4a7e9da6a4a729c16cd384c0af2a4a52809b06803 0x1488a9c1438a5556085c0e75598c754469084468843488007a30aa2b2e9bb10d42e2⟩,
  ⟨20,5,[0x88888888, 0xaaaaaaaa, 0xcc00cc00, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],hint 5 0x2ffbfae7b66d8b56cdb22bbab2aaa929fa768ea124a6096a4e1301b4681945714803 0x2a6296912db35b67a72f3194a6d8e74bb14d626db370f83c23a8437584224042c90400⟩,
  ⟨20,5,[0x33003300, 0x88888888, 0xaaaaaaaa, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],hint 5 0x2febf2fbb9ee5b66d8b56c8aeeaaa929fa7696a3a4a609785a9384c0681945c15c5204403 0xebc1de65bc213d9085c32751e8fb3c45a884498843488008f1d1b9f6f63232d45a2⟩,
  ⟨20,6,[0xaaaaaaaa, 0xcccccccc, 0xeeeeeeee, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],hint 6 0xbbae7b7edcb66d8b5ed5b02bfaeeb8aaaa4a7e9da729aa5a8ea11c16e1b36096f5a8af2a4a52809b1a065190621846017c5d1705815c5614c521444c12c48114430e4360480f 0x22962cdf7f397789f8a87e8ca55f27dfa25a3289ba336e88a2cb3c957dfb14b2c7df4d24508a2b4eb6d8a230b26ea28bc81efa28b86b8aa4ac5f5b1a7029f28a88a9333e48a32b328aa0a7b235ea1d2b228402a2ac2987d8d697357f4629618cd89e26a7ce6622618c98868661ca062860507662c60528a6046030ab⟩,
  ⟨20,5,[0x22222222, 0xaaaaaaaa, 0xeeeeeeee, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],hint 5 0x2febf2eeb72d8b56b8aaaa4a769aa1258929c16cd825a9302bca9294a026c681945c15c5211003 0x20ee42a67554a86ad2f598c80631af4ebd9ce9a1ce879c00164a214c8213462c0ae2⟩,
  ⟨20,4,[0x22222222, 0xaaaaaaaa, 0xee00ee00, 0xf0f0f0f0, 0xffff0000],hint 5 0xb96d8b56b4aaa9da6a846096a4c1231a06517057148170440d02003 0x2096c16daac635d0049000150002780b3414ac314ae39620⟩,
  ⟨20,5,[0x44444444, 0xcccccccc, 0xeeeeeeee, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],hint 5 0xbeeeeb9edcb62d5b36c8ae2aaa769aa11c16cd825a9382bca9294a026c681945c15c5211803 0x20ee426674d4a8658c7061786e769f445c084488843688003e9673c9273bd07a9e82⟩,
  ⟨20,4,[0x44444444, 0xcccccccc, 0xeeee0000, 0xf0f0f0f0, 0xff00ff00],hint 5 0xbbadcb62d5a929da6a3d705b34e1232bca9294a026c1a05c0d02003 0x1086cd6dab4905c0027000150003900af394ac314b449620⟩,
  ⟨20,5,[0xaaaaaaaa, 0xcccccccc, 0xe0e0e0e0, 0xeeeeeeee, 0xff00ff00, 0xffff0000],hint 5 0x2fcbeeeeb72d8b56c0adab3aaa9da6a84705b36096a2bca9294a026c681945c15c5212849 0xf6e9eda342fabc123364a53f16908b710890170421b0475e4e74c4fb39d0e388f3⟩,
  ⟨20,4,[0xaaaaaaaa, 0xcccccccc, 0xe0e0e0e0, 0xee00ee00, 0xffff0000],hint 5 0x2eeb72d8b56aaa769aa11c16cd825a8af2a4a52809b1a0651705714803 0x732ce895914a5d40926108de10896132aa63220631da600032⟩,
  ⟨20,4,[0xaaaaaaaa, 0xcccccccc, 0xe0e0e0e0, 0xeeee0000, 0xff00ff00],hint 5 0x2eeb72d8b56aaa769aa11c16cd825a8af2a4a52809b1a0651705714803 0x63ace4a5d48959108de109261089613220632aa631da600032⟩
]

def nodeBlock5 : Array Node := #[
  ⟨20,5,[0xe0e0e0e, 0xaaaaaaaa, 0xcccccccc, 0xff00ff00, 0xffff0000],hint 5 0xbbadfb72d9b62d7b56c8a7e9da729aa5a8ea124a705b86cd825bd6a2bca9294a026c681945c15c52 0x7cdfc63393fbd8f05c1a60f57c818003c12e0a4f883802b0beba7cce96e52f0b579ebca15e5c0005814a006210b4edb6337325996df3767bedc46de8d80165aac006d61b14bb737652d9c6⟩,
  ⟨20,5,[0xe0e0e0e, 0xaaaaaaaa, 0xcccccccc, 0xeeeeeeee, 0xff00ff00, 0xffff0000],hint 5 0x2eeb72d8b56c8afeaaa769aa124a705b36096a2bca9294a026c681945c15c521404f1384d 0x117f22f1bc510c4043e48434c92225bb4a5744e1244daaf45751632f5238854c12a⟩,
  ⟨20,4,[0xe0e0e0e, 0xaaaaaaaa, 0xcccccccc, 0xee00ee00, 0xffff0000],hint 5 0xbbadcb62d5aaa9da6a84705b36096a2bca9294a026c681945c15c52 0x6aead00e40009c02a68529de50141182c909b508028012b0a6⟩,
  ⟨20,4,[0xee00ee, 0xe0e0e0e, 0xaaaaaaaa, 0xcccccccc, 0xffff0000],hint 5 0xbbadcb62d5a769aa11c16cd825a8af2a4a52809b1a0651705714811 0x924132a86098208b0b10ac22334c77558e0bc23340c84a66e⟩,
  ⟨20,4,[0xe0e0e0e, 0xaaaaaaaa, 0xcccccccc, 0xeeee0000, 0xff00ff00],hint 5 0xbbadcb62d5a769aa124a705b36096a2bca9294a026c681945c15c52 0x5b6ad009e000e4029e052a6850140e9b5088ac91028012b0a6⟩,
  ⟨20,4,[0xeeee, 0xe0e0e0e, 0xaaaaaaaa, 0xcccccccc, 0xff00ff00],hint 5 0xbbadcb62d5aaa9da6a84705b36096a2bca9294a026c681945c15c52 0x9c029de5014119b508028012b0a66d5ab048032d0a98120b⟩,
  ⟨20,5,[0xaaaaaaaa, 0xcccccccc, 0xee00ee00, 0xf0f0f0f0, 0xffff0000],hint 6 0x2eeb9edfb72d9b62d7b56aaa7e9da729aa5a8ea11c16e1b36096f5a8af2a4a52809b1a06517057148440e003 0x60f61d54774f3d855849549e3cf7958923d27982d274b49849e75d0d90dc3c67196c33c30d80ce7443983437430d20d47855124c378320f22064c80f7c864821d21160945d40860821e21748a5de5884888430080802030e105a⟩,
  ⟨20,5,[0xaaaaaaaa, 0xcccccccc, 0xee00ee00, 0xeeeeeeee, 0xf0f0f0f0, 0xffff0000],hint 5 0x2eeb9edcb62d5aeeaaa769aa11c16cd825a8af2a4a52809b1a06517057154541484d12444 0x154c2b02c095154328724d6cb3790d1818ccf180633cc6a7694a5c55b5299450d56⟩,
  ⟨20,4,[0xaaaaaaaa, 0xcccccccc, 0xee00ee00, 0xeeee0000, 0xf0f0f0f0],hint 5 0x2eeb72d8b56aaa769aa11c16cd825a8af2a4a52809b1a0651705714803 0x2c5914a5d4732ce089610926108de131da632aa63220600032⟩,
  ⟨20,4,[0xeeee, 0xaaaaaaaa, 0xcccccccc, 0xee00ee00, 0xf0f0f0f0],hint 5 0xbbadcb62d5aaa9da6a84705b36096a2bca9294a026c681945c15c52 0x421b300540009c02998529de50141182e046d5ab048032d0a9⟩,
  ⟨20,5,[0xaaaaaaaa, 0xcccccccc, 0xee00ee00, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],hint 5 0xb72d8b56aaa769ca5a8e705b36096a2bca026c681945714803 0x1a96a5e44be4f7c9a96a56b7c9f208e210b181089010b18129e652b9c5299452b9c500030⟩,
  ⟨20,5,[0xee00ee, 0xaaaaaaaa, 0xcccccccc, 0xeeeeeeee, 0xf0f0f0f0, 0xffff0000],hint 5 0x2eeb72d8b56cdadaaaa769aa11c16cd825a9302bca9294a026c681945c16c5a164571484e 0x15442b02c095056e13e42113c2e0a5bb4a5514e1214da5c84b52630720cc264d12b⟩
]

def nodeBlock6 : Array Node := #[
  ⟨20,4,[0xaaaaaaaa, 0xcccccccc, 0xee00ee00, 0xf0f0f0f0, 0xffff0000],hint 5 0x2eeb72d8b56aaa769aa11c16cd825a8af2a4a52809b1a0651705714803 0x89591732ce4a5d4092610896108de132aa631da63220600032⟩,
  ⟨20,4,[0xee00ee, 0xaaaaaaaa, 0xcccccccc, 0xeeee0000, 0xf0f0f0f0],hint 5 0xbbadcb62d5a769aa11c16cd825a9302bca9294a026c681945c15c52 0x245910056000e40299a52a6850140a9b9087558e03c022c0a7⟩,
  ⟨20,4,[0xeeee, 0xee00ee, 0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0],hint 5 0xbbadcb62d5aaa9da6a84705b36096a2bca9294a026c681945c15c52 0x54029985014119b508038022bca782e04048032d0a96adb5⟩,
  ⟨20,5,[0x11001100, 0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],hint 5 0xbeeeeb72d8b56c0afeb8aaaa4a769aa11c16cd825a8af2a4a52809b1a0651785c1645714803 0x20ee426774d6b86826c8424884226850cda10a921097a0000d4aeb3870bcf13a07a8⟩,
  ⟨20,4,[0xaaaaaaaa, 0xcccccccc, 0xeeff0000, 0xf0f0f0f0, 0xff00ff00],hint 5 0x2eeb72d8b56a4a769aa11c16cd825a8af2a4a52809b1a0651705714803 0x4a5d463ace2c59108de108961092613220631da632aa600032⟩,
  ⟨20,5,[0xaaaaaaaa, 0xcccccccc, 0xeeee0000, 0xf0f0f0f0, 0xff00ff00],hint 6 0xbbadfb72d9b62d7b56a4a7e9da729aa5a8ea11c16e1b36096f5a8af2a4a52809b1a06517057148460ec03 0x7522d878b61249d79d3de3d549255e84f49255d1cf6183dd3d56180d20d47855124c37830d80ce7443983437430d90dc3c67196c33c321e21748a5de58848821d21160945d40860820f22064c80f7c86480830086802030c169a⟩,
  ⟨20,5,[0xaaaaaaaa, 0xcccccccc, 0xeeee0000, 0xeeeeeeee, 0xf0f0f0f0, 0xff00ff00],hint 5 0x2eeb72d8b56b8aaaa4a769aa11c16cd825a8af2a4a52809b1a0651705a15c541484f12846 0xd6cb52348951543097249ac2b880cf318caf1d8634646a6514a5c540529db50d57⟩,
  ⟨20,5,[0xaaaaaaaa, 0xcccccccc, 0xeeee0000, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],hint 5 0x2feb7ed9b62d7a929da6a84705b36096a2a4a52809b1705714803 0x17292dd18b8e75c52992e4b8ba2e0c28108d81089010c20124e64219a42154424e640002f⟩,
  ⟨20,5,[0xeeee, 0xaaaaaaaa, 0xcccccccc, 0xeeeeeeee, 0xf0f0f0f0, 0xff00ff00],hint 5 0x2eeb72d8b56b3aaa9da6a84961c16cd825a9382bca9294a026c68194631705b15c5514850 0xc64b522485605b012d0211bc330a5754a5514b9214de5c942d0b20d00e4274ed2d⟩,
  ⟨20,4,[0xaaaaaaaa, 0xcccccccc, 0xeeee0000, 0xf0f0f0f0, 0xff00ff00],hint 5 0x2eeb72d8b56a4a769aa11c16cd825a8af2a4a52809b1a0651705714803 0x4a5d463ace2c59108de108961092613220631da632aa600032⟩,
  ⟨20,5,[0x11110000, 0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],hint 5 0xbf2eeb9edcb62d5b02bfaeea4a769aa11c16cd825a8af2a4a52809b1a066194631705714803 0x20ee426774d6b86425c0423884226850cd210a921097a0000d08e342b0b4ef3e8768⟩,
  ⟨20,4,[0xaaaaaaaa, 0xcccccccc, 0xee00ff00, 0xf0f0f0f0, 0xffff0000],hint 5 0x2eeb72d8b56a4a769aa11c16cd825a8af2a4a52809b1a0651705714803 0x89591732ce4a5d4092610896108de132aa631da63220600032⟩
]

def nodeBlock7 : Array Node := #[
  ⟨20,6,[0x22222222, 0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],hint 6 0xbfafcbbae7b7edcb66d8b02bfaeeb8a929fa769ca6a96929c16e1b3609302bca9294a026c731c8711c06f1b86c1ac6a1a4681484303803 0x186989555656a961561d55d91a12455575a76461276549d61892591f79fa9556a7ab7d57ce6147e551f61836596a7597e465f75daa490f54f9de4e75663de3cf94f71845c95b3d83cf90f5dd4179163dd3cc2c03c23c17df29556079e81554979e2259616188659476188a492375d8e492275d1820e07c3141a203cf⟩,
  ⟨20,5,[0x88888888, 0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],hint 5 0xbfefebbae7b66d8b22c0afebbae2aaa929fa764a705824e1302a49b1a0520bc20 0x25174ac68594a9a3518698c9aa94ba1ce8659394cd745d9ae0a1e8026098ae4b10884⟩,
  ⟨20,5,[0xaaaaaaaa, 0xcccccccc, 0xeeeeeeee, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],hint 5 0xbbae7b72d8b56c0afebbae2aaa929da6a84705b36096a2bca9294a026c68194631705915c52 0x3dbd7c8cd9294fd36ad23ecf14b12b80b9000700002c04c075ece74c4e7438fc380f4⟩,
  ⟨20,5,[0x22002200, 0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],hint 5 0xbeeeeb72d9b62d5b02bfa929da6a96a39c16cd825a8af2a4a52809b1a0651705714803 0x1ccd3a456492975c24b042370422584cac98c8898c7698000ce0c8330ea4ab278766⟩,
  ⟨20,5,[0xaaaaaaaa, 0xcccccccc, 0xdd00dd00, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],hint 5 0x2dcb62d5ab2a4a7e9da728ea11c16cd825a8af2809b1b4681945714803 0xaa9aa04542b08562a8a98c8561508e810c9a1089210ba41322c633de631d6633de600032⟩,
  ⟨20,5,[0x22220000, 0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],hint 5 0x2febbae7b72d9b62d7a929da6a84705b36096a2bca9294a026c651705714803 0x1b4bb6139c1086cc24c042370422504a9a94a7794a6614000c56ba368d9c270906c5⟩,
  ⟨20,5,[0xaaaaaaaa, 0xcccccccc, 0xdddd0000, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],hint 5 0x2fcb86dfb62d7b56c0afeaca929fa769aa11c16cd825a8a9294a026c681705714803 0x18a931e453d0865e0acb32c9be8f0aaa108da1089210db412e30529dc5299652e30500031⟩,
  ⟨20,5,[0x22222222, 0x44444444, 0xaaaaaaaa, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],hint 5 0x2febbae7b66d8b56b4a929da124a8f5c16096a4c1232a49b1a065170571483705c0d02003 0x20fdc2897d16b86003b000288001602afe55ad86652a61402dd052cce52b8c5d0085⟩,
  ⟨20,5,[0x22222222, 0x44444444, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],hint 5 0x2ffbbae7b72d8b22b4a929fa769a8f5c16cd824e1232bca9294a026c681483a05c0d02003 0x20edc26674d4a86003b000288001600f959cf249cef41ea06b5d4d4390bcf1328087⟩,
  ⟨20,5,[0x22222222, 0xaaaaaaaa, 0xcc00cc00, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],hint 5 0x2feb9ed9b62d5ad2aca929da728ea124a91a3d6096a4c1231b468194571481702003 0xeba2e465caf295e6bd4d2973a5700aa00458000500036201d8a31bf031a88380f20⟩,
  ⟨20,5,[0x22222222, 0x33003300, 0xaaaaaaaa, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],hint 5 0xbfafcb9ee5b66d8b56bbad2a4a769aa5a8e92a466096a4c1231a06517057148170440d02003 0x5b74b9a5b318d78012a000a4000540a7634caf937be80700b7414ab394ac317602c2c5⟩,
  ⟨20,6,[0x44444444, 0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],hint 6 0xbfefbbbae7b66d8b5ed5b22c0afebbae2a4a7e9da5a8ea11c16096f5a9382a49b1f07a1e4771d8751c4701a8691a065170571484504003 0x186d89d75e76e961761c5dc99b1e65d771b7266137274dc6189a79837439571a57640d70c36036a715a6190e70c37035a61167150e60d15d4a1d5285d741d7689e8a9862a9eba1862a9a3a1c7289a6a9c70b2800830e80683dd75f5d77dd74e5d73586209e781860c9e785c7229a689c7219a620179f0c324249fa12⟩
]

def nodeBlock8 : Array Node := #[
  ⟨20,5,[0x44004400, 0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],hint 5 0xbfee7b72d8b56aca929fa769ca11c16cd825a8af294a026c6d1a0651705714803 0xcca3225646d18d824a842378422584eab9ce9c9ce869c000e24c931ce8da3698607⟩,
  ⟨20,5,[0xaaaaaaaa, 0xbb00bb00, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],hint 5 0x2fbbbae7b72d9b62d5b02bfa769ca6a96a39c16cd825a8af2a4a026c681945714803 0x18acb224544e765423a042d68422485ca72acc94671685a12a2e52b1e529965000382c345⟩,
  ⟨20,5,[0x44440000, 0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],hint 5 0xbf2e1b7ed8b56c0afeaca929fa769aa11c16cd825a8af2a4a52809b1a0651705714803 0x1cca3a256452976024b842378422584ca618c8818c7698000ce4cd3b4eac6d1d8726⟩,
  ⟨20,5,[0xaaaaaaaa, 0xbbbb0000, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],hint 5 0x2eeb9edfb72d9b62d7a929da6a84705b36096a2a4a52809b1705714803 0x172b2dd18b8e75c43080423604224052992e4b8ba2e8060125664219a4215440002f252a4⟩,
  ⟨20,5,[0x44444444, 0xaaaa0000, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],hint 5 0x2ffbbae7b7edcb66d8b5ec8b16b4a929fa769a8f5c16cd3848ca9294a026c0d02003 0x155ca9b4a34c655013800025800138108c2b4a9368d882601d9c31b0a31a483782e3⟩,
  ⟨20,5,[0x44444444, 0x55550000, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],hint 5 0x2fbb9edfb62d5b36c8b16b8a96a4a7e9da6a3d705b34e1232bca9294a026c1a05c0d02003 0x6ae6d81170421b900f00009c0005408af6dbb790b4360a80ab494af394ac316402ea85⟩,
  ⟨20,6,[0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xfafafafa, 0xff00ff00, 0xffff0000],hint 6 0xdb302bfefcbbaecb9ee1b66d8b5ed5b02bfaeeb8adab3a929fa7696a3a84705b86cd825bd6a4e12826c811f8681945c15c52 0xf48f7cc31f4a33cc3d630c61451830c5945173cf6608193cf5e081630479211e30c69249e3cf9df7e73cf79f79b6937984c050074c0dd51c00c0003c045f0913d001f0241a401b0006c09059006802de04b6ca01e00e30e85426132239438e7ce98f3e67e538f39a6873981da79e39b39a68d84000e548380021555⟩,
  ⟨20,5,[0xaaaaaaaa, 0xc8c8c8c8, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],hint 5 0xc06ffbf2eebb2e7b66d8b22c0ae29fa7696961c16e1b36093826c7f1a052 0x105a20212a9114412561511446b0bc045695114456b74000392673a2c779cc691cf218cf2⟩,
  ⟨20,4,[0x37370000, 0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00],hint 5 0xb72d8b56aca929da6a84705b36096a4e0a9294a026c681705714803 0x421b408dc10894129de529985000315b64d2417058661496a5⟩,
  ⟨20,5,[0x32323232, 0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],hint 5 0x2eeb9edcb66d8a7e9da6a58929c16cd822bca9294a026c6814803 0x148a29c2438c6541887a1515456b7406790c6568c6448c001cd0f43e2a8aa0e8382198e63⟩,
  ⟨20,6,[0xa0a0a0a, 0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],hint 6 0xe4302bfeeebb2e7b66d8b5ed5b02bfaeeb8adab3a929fa7696a3a84705b86096f4e1282a4a026c8520c6517052 0xd40d74b2dd42034b3512d18d04232cb45045534745d1d134d61d7404806cb09b49a00b0003403dd04f34e01d00044029928a44a01800c2cc79225e2df31230c74c88d36276130d31860631931845178000c4c830001e4d35104162cb5904142cb55d75734d5dd75534d61971645110001928a0c001928a618156305⟩,
  ⟨20,5,[0xaaaaaaaa, 0xcccccccc, 0xcececece, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],hint 5 0xbbae7b72d9b62d5b02bba769aa5a84705b36096f2bca9294a026c841945c15c52 0x1abcb62f5c5086d9eb7adb2692338d403a000270001881402a6e529e0529985c14b801418⟩
]

def nodeBlock9 : Array Node := #[
  ⟨20,4,[0xaaaaaaaa, 0xcccccccc, 0xce00ce00, 0xf0f0f0f0, 0xffff0000],hint 5 0x2eeb9edcb62d5a769aa11c16cd825a8af2a4a52809b1a0651705714803 0x89591732ce4a5d3092410896108de132a8631da63220600035⟩,
  ⟨20,5,[0xaaaaaaaa, 0xc4c4c4c4, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],hint 5 0xbfeeebb2e7b66d8b569fa7684705b86096f5a9382a4a026c681945c14803 0x1abb35e45bce76c82388422704324860b82db36cdf27c941622ac636ec3198f00034a30a5⟩,
  ⟨20,6,[0xaa00aa00, 0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],hint 6 0x2eeb9ee1b7edcb66d8b5ed5afebbae2b6a929fa769ca6a96a39c16e1b36096f5a8af2a4a026c922448e2348c2248821c6b1a06515c5207803 0x18698a9556a6ac61561d55d99a16655575a76661176a45d6189aa9827829551257a409508260266265961908e0827425260d47530a608f54fa5e4a95683de3cf2cf89862289b3e63d77505e658f74fac200f7c03c20ab7df35a6a155585a68c55588b9e16188e08e075d80a26375d2196460821d96410828a27213cf⟩,
  ⟨20,5,[0xaaaaaaaa, 0xcccccccc, 0xeecceecc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],hint 5 0x2eeb9edcb66d8aaaa9a7e9da6a96a528ea11c16cd822bca9294a026c6816452 0x148c2a02440c6551c87215550614851888b14c5ad8d9300019ec3195e319123b8c7760c73⟩,
  ⟨20,5,[0x44cc44cc, 0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],hint 5 0x2eeb9edcb66d8aa69fa769ca6a94a3a46705b3608af2a4a026c6817052 0x127b25e23bca54c96782c215cd6c8ac66a0c6968c6440d431d60781d334cdf27c8001d46e⟩,
  ⟨20,5,[0xaaaaaaaa, 0xcccccccc, 0xfaf0faf0, 0xff00ff00, 0xffff0000],hint 6 0x36cc02eeb9ee1b7edcb62d7b56a4a7e9da6a96a4a8ea25c16f5b86cd825d16f5a8af2a4a026c8b228681945714803 0x4964a038e81689239260e61d64474e39865875225880961249d81d05905c3837196c138105205490d5124c118105804c7423182c17411ce1df64a7ce7876471c51e34918e45c74871dd1d060841d3c76078410076801c1061695⟩,
  ⟨20,4,[0x55005500, 0xaaaaaaaa, 0xcccccccc, 0xfaf0faf0, 0xffff0000],hint 5 0x2eeb72d8b56a4a769a705b36096a4c0af2a4a026c681945714803 0x1e45bc2388422504a8994a6614000c1aba34e76c921685c5⟩,
  ⟨20,4,[0xaaaaaaaa, 0xcc00cc00, 0xcccccccc, 0xfaf0faf0, 0xffff0000],hint 5 0xbbae7b72d8b569da69c16f5b3609745a8af2a4a026c681945714803 0x2045c02388422485cbab8e7749412a26529985000342b5e5⟩,
  ⟨20,5,[0xaa00aa00, 0xaaaaaaaa, 0xcccccccc, 0xfaf0faf0, 0xff00ff00, 0xffff0000],hint 5 0x3aec02eeb72d8b56a4a769aa5a8e705b36096a2bca92809b228681945714803 0xd5d9b122e28436811cc2173821128264d4c66c0c7618000c9eb7acadc45c1706e6⟩,
  ⟨20,5,[0x55005500, 0xaa00aa00, 0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xffff0000],hint 5 0x2eeb72d9b62d5ae2aca929da6a84705b36096a4c0af2a4a52809b2286d1a0651705714803 0x2857d024c04227050cda109820000d4cfb3f543d061905488bf915ae39686219a2f1⟩,
  ⟨20,5,[0xaa000000, 0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],hint 5 0xbeeeeb72d9b62d5b02bfa929da6a96a11c16cd825a8af2a4a52809b2408f1a0651705714803 0x20ee42857516b86424c0423884226850cda10a9a1097a0000d64ed42d4bd0e1307a8⟩,
  ⟨20,4,[0xaaaaaaaa, 0xeecccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],hint 5 0x2eeb72d8b56a4a769aa11c16cd825a8af2a4a52809b1a0651705714803 0x732ce895914a5d40926108de10896132aa63220631da600032⟩
]

def nodeBlock10 : Array Node := #[
  ⟨20,4,[0x44cccccc, 0xaaaaaaaa, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],hint 5 0x2eeb72d8b56a4a769aa11c16cd825a8af2a4a52809b1a0651705714803 0x732ce895914a5d432aa63220631da60926108de10896100032⟩,
  ⟨20,5,[0x55ff0000, 0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],hint 5 0x2e1b7ed9b62d7a929da6a96a11c16cd825a8a9294a026c6d1705714803 0x184732139c10864c329042368422484b5a94a7794a6594000c54ab328c9c27090641a96a5⟩,
  ⟨20,5,[0xaa00aa00, 0xaaaaaaaa, 0xcc00cc00, 0xcccccccc, 0xf0f0f0f0, 0xffff0000],hint 5 0xbbae7b72d9b62d5ab29da729aa3a84705b36096a2bca92809b22c6d1a0651645714803 0xa15b4092c1089817b76f529f78850bca109720000e90f920cdab7143d3018070f1be68⟩,
  ⟨20,6,[0x55005500, 0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],hint 6 0x2e7b7edcb66d8b5ed5afebbae2b6ab2a4a7e9da7296a3a84705b86cd825bd6a2bca52809c26c992609725494234751b4681945d1705714803 0x24707a565a972141659e59ea1c1a859679c7a88a87a979e91ea29a017c19d61677e60560413816e90db91a06904178156809579406804f58fadf4eb5aa3df3e4912929a4f24f3e83d87916285cf78fb0100f8003c106c82035f7e35968df7cc596909663a5995e7a2a2889e7a5a282e08040412a08080419247633cf⟩,
  ⟨20,5,[0xaaaaaaaa, 0xcccccccc, 0xddccddcc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],hint 5 0xbfaeeb9edcb66d8a929fa769a92a46705b3608af2a4a52809b1a052 0x127a25a13b4a54c1c771d314c5b06c1e7abd2f4c56b6c00011a421118210d02988535084f⟩,
  ⟨20,5,[0x88cc88cc, 0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],hint 5 0x2ffbfae7b72d9b62c0afeb8ab2a4a769c929c16cd824c0af294a026c961b46814820 0x6a8a9e253eaf7d60acc129859ad7d4a8b94a7d14a6597052c08a928166326fa3c212b8b8⟩,
  ⟨20,4,[0x77330000, 0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00],hint 5 0x2d8b56aca929da6a84705b36096a4e0a9294a026c681705714803 0x421b408dc10894129de529985000315b64d241705866149565⟩,
  ⟨20,5,[0x55000000, 0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],hint 5 0x2fcbeeeeb86dcb62d5b02bfa929fa769aa11c16cd825a8af2a4a52809b1a0651705714803 0x1ccd3a256452975c24b042378422584cac18c8818c7698000ce4ccba91ac781e0766⟩,
  ⟨20,5,[0xaaaaaaaa, 0xaaff0000, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],hint 5 0x2feb7ed9b62d7a929da6a84705b36096a2a4a52809b1705714803 0x17292dd18b8e75c430a0423604224052992e4b8ba2e8060124e64219a4215440002f24e64⟩,
  ⟨20,5,[0x33003300, 0x55005500, 0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xffff0000],hint 5 0xbbae7b72d9b62d5b36aca769aa11c16cd825a9302bca92809b2686d1a06515c5208003 0x995d3112c210da242f28425e80005a83b7052a1760a02920cea3b133ce22aa308c4030⟩,
  ⟨20,4,[0x55005500, 0xaaaaaaaa, 0xcccccccc, 0xf3f0f3f0, 0xffff0000],hint 5 0x2eeb72d8b569da6a4a705b36096a4c0af2a4a026c681945714803 0x2045c02388422504a8994a6614000b9aba34e76c921685e5⟩,
  ⟨20,5,[0x55005500, 0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff000000, 0xffff0000],hint 5 0x2fcbbadcb66d8b56cdae2a4a769a705b36096a4c0af2a4a02749b1b4681945714803 0x2b6246c6373c423a8437d0422604cac18d4b98c8718000c9edcbdf79bd297d96178606⟩
]

def nodeBlock11 : Array Node := #[
  ⟨20,4,[0x55005500, 0xaaaaaaaa, 0xcccccccc, 0xfff0f0f0, 0xffff0000],hint 5 0x2eeb72d8b56a4a769a705b36096a4c0af2a4a026c681945714803 0x1e45bc2388422504a8994a6614000c1aba34e76c921685c5⟩,
  ⟨20,6,[0xaaaa0000, 0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],hint 6 0x2febbadfb72d9b62d7afebbae2b3a929fa769ca6a8ea11c16e1b36096f5a8aa2a4a7294a428ca22809f26c8e1e86e170571483c0b003 0x187989a19a67a961261d81d95e96586575e76561176645d6189669437839219247aa0d00c36036a615a6190e60c37435251147530e50c938985e7a186726625c60f7266c960926525774b5e55897491c30097c02430c27df84e5617953669a26188a69886188e596075d82596375d3249060c32a49010c3861a21249⟩,
  ⟨20,5,[0xaaaaaaaa, 0xcccccccc, 0xeeeecccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],hint 5 0xbc2eeb9edcb66d8b5ed5b02bfaeeb8a7e9da69c16cd822bca9294a12809b18c52 0x155c2994a30c6551086854f51191641b39495554d9464c0011ec21156210d22b884e98859⟩,
  ⟨20,4,[0xaaaaaaaa, 0xcccccccc, 0xee00cc00, 0xf0f0f0f0, 0xffff0000],hint 5 0xbbae7b72d8b569da69c16cd825a8af2a4a52809b1a0651705714803 0x81590732ae4a5d2092210896108dc132a6631da6321e600034⟩,
  ⟨20,5,[0x4444cccc, 0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],hint 5 0xbbae7b7edcb66d8b5ec5a7e9da69c16cd824e0a9294a026c6819452 0x148aa982430c6540217a15153d9063c6790c6558c6448dc31d1a86a15154590640001d073⟩,
  ⟨20,5,[0x5500ff00, 0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],hint 5 0x2dcb66d8b56a4a7e9da7296a39c16cd825a8af2809b1b4681945714803 0xaaaaa0454290850239842d68422484c8b18cf798c7598000ca2a7298c85214685a1799e6⟩,
  ⟨20,5,[0x55550000, 0xaaaa0000, 0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00],hint 5 0xbfaeeb72d8b56b8ab2a4a7e9da6a84961c16cd825a8b72bca9298a52809b1a0651705714803 0x14a8682390422684c8998c7798000d9d0bc0b475081c856664390ad134887a1d9b0e⟩,
  ⟨20,4,[0xaaaa0000, 0xaaaaaaaa, 0xcccccccc, 0xf5f5f0f0, 0xff00ff00],hint 5 0xb62d5ab2a4a769aa11c16cd825a8af2a4a52809b1a0651705714803 0x1297542378422584c8818c7698000c98e9b8b164481a0546⟩,
  ⟨20,5,[0xaaaa0000, 0xaaaaaaaa, 0xcccc0000, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00],hint 5 0xbbadfb72d8b5ed5ab2a4a7e9da6a84705b36096a2dca92a0a52809b1a0631705714803 0x529f808e01089815bf6f9c932b84c8898c7718000d0d3c99afabcb26c9a1b05b323746⟩,
  ⟨20,4,[0xaaaa0000, 0xaaaaaaaa, 0xcccccccc, 0xfcfcf0f0, 0xff00ff00],hint 5 0xb62d5ab2a4a769aa11c7705b36097f5a8a9294a026c681705714803 0x1086d42378422484a7814a6614000c96d9b4915c541a05c5⟩,
  ⟨20,5,[0xaaaa0000, 0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff000000, 0xff00ff00],hint 5 0xbfad9b62d5aeeaca929fa769aa5a84961c16cd825a8af2b0ab2a4a52809b1a0651705714803 0xe412986eb65d42390431e8422684c8a18d6518c7798000ddd0c41d3cb8b575481d0586⟩,
  ⟨20,4,[0xaaaa0000, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffaaaaaa],hint 5 0xb62d5ab2a4a769aa11c16cd825a8af2a4a52809b1a0651705714803 0x106818e669929754000c823784225854663a6e2c59120681⟩
]

def nodeBlock12 : Array Node := #[
  ⟨20,4,[0xaaaa0000, 0xaaaaaaaa, 0xcccccccc, 0xff00ff00, 0xfff0f0f0],hint 5 0xb62d5ab2a4a769aa11c16cd825a8af2a4a52809b1a0651705714803 0x1297542258423784c7698c8818000c8b16458e9b881a0546⟩,
  ⟨20,6,[0x55550000, 0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],hint 6 0x2fcb86dfb66d8b5ed5afebbae2b3ab2a4a7e9da729aa5a8ea11c16e1b36096f5a8b52d0b32c4b02bcae2a4a5290a026c971f0771a0651905c15c520f403 0x1c7dcb5966d7e5719722662b1f1ec65989f8ac70f8ad3e271cb2db02582ad91ab9ea0990827027ad11e71d0ad08288262c0d88970ac0a79d19d964b34b2ed2e170e86d80b70b2ec2db88c6ec68b88b24200b9002c20819249cd8e765956fbe871ca2fbca71ca66a668a29944e98a24b0c05082430c080829e7ba72cb⟩,
  ⟨20,5,[0xaaaaaaaa, 0xcccccccc, 0xddddcccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],hint 5 0xbfafcbbae7b72d9b62c5ae29fa769a705b3608af2a4a52809b1a052 0x1279a5613aca54bd8761d304c16f5bd87ad5304c16f5bc0011a221114210d026885270854⟩,
  ⟨20,5,[0x8888cccc, 0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],hint 5 0x2fcb9edfb66d8ab29fa769a961c16cd822bca9294a026c681482f 0x1487a9a2434c654168a2151545b06c06740c6560c6448e631cc0872151545b06c0211c873⟩,
  ⟨20,5,[0xaaaaaaaa, 0xcccccccc, 0xf5f5f0f0, 0xff00ff00, 0xffff0000],hint 6 0xe42deb76d9b62d7b56c8a929da729aa5a8ea11c16e1b36096f5a8b22bca9298a52809b1a0651705714803 0x49549e3cf7958123d260f61d54574f3d855875229878a61249d79d04c05c3c47216c13c10520547835124c178105804e74239834174118f19a84b68f7c624619e1974885de58648619d19160745d40660668100664018105a659⟩,
  ⟨20,4,[0x33330000, 0xaaaaaaaa, 0xcccccccc, 0xf5f5f0f0, 0xff00ff00],hint 5 0x2d8b56aca929da6a84705b36096a4e0a9294a026c681705714803 0x1086d02370422504a7794a6614000c56d934905c26149565⟩,
  ⟨20,5,[0x55550000, 0xaaaaaaaa, 0xcccccccc, 0xf5f5f0f0, 0xff00ff00, 0xffff0000],hint 5 0x359bf2e1b62d5b22aca929da6a84705b36096a2bca9298a52809b1a0651705714803 0xf6d1f22b64a53ee1258211c0211302b698c8898c7718000cd2dc3f0fd4b21c86a6⟩,
  ⟨20,5,[0xaa00ff00, 0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],hint 5 0xb72d8b56a4a769ca5a8e705b36096a2bca026c681945714803 0x1a96a5e44be4f7c8238842c60422404a7994ae714a6514000c1a96a56b7c9f260581715c5⟩,
  ⟨20,5,[0x33330000, 0x55550000, 0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00],hint 5 0xbbadcb62d5ab2a4a7e9da6a84961c16cd825a9382dcb22a4a52809b1a05c15c520bc03 0x4a6191124210da23226631de6000565c370ad15488aa2d19d0bc0b475302619c67542e⟩,
  ⟨20,6,[0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xfcfcfcfc, 0xff00ff00, 0xffff0000],hint 6 0x374c0efebeeeeb9edfb72d9b62c0afebbae2b6acea8a929fa769ca6a96705b86cd825bd6a4c1282e8b82bca9294a026c52 0xf40f78c31e4223cc3d730c65041930c5d04183cf69e79a3cf61e79331399042630c4d04d83c44de1133cf6de79c6dd4d94cb50b94c3255242cc2cb3cb55e2553d62de2db6c02d901b4d32dc2db6ca04c06050580c7c150105e0523c349e4413c18c78c170105c0631a305b04e4c239c3414c184b20154104b061555⟩,
  ⟨20,5,[0xa8a8a8a8, 0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],hint 5 0x300bfafbbbad9b62cdb02bbaa2a4a7e9da5a56929c16096f5a9302e4a926c52 0x107aa18b3b042450c7b98c479926294ea3b648a22ccc30ce338eb3ac688226c8b00033821⟩,
  ⟨20,4,[0x57005700, 0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xffff0000],hint 5 0xbbadcb62d5a929da6a84705b36096a4c0af2a4a026c681945714803 0x8117008e41089412a28529985000316aead39db3485c1695e5⟩
]

def nodeBlock13 : Array Node := #[
  ⟨20,5,[0x54545454, 0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],hint 5 0xbbad9b62d5b36c8a929fa7684959c16096a2a49b1a0651705714803 0x149aa9a54b4e754c2490423604224052b4ba2aa2a0d9b4000bdc972554551b36cde1784c6⟩,
  ⟨20,6,[0xc0c0c0c, 0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],hint 6 0x395c0efebbae7b86dfb72d9b62c0afebbae2b6acea8a929fa769ca6a96705b86096f4c1282f8bc2bca526c6815c52 0xd38d70b2dc3a134b3552c26ce09b2cb64e39b34d91c72434d6dc6ca48a8cb2e34a228b28a34a4dc25335429c29964129a2996db0cb0de48578b7434830dc0d034441c3c33430db0cc68c31b30364380a2034c30ca0e04d35524972cb5d24952cb59f7d834d61f7d634d65a4576d16590172801c30da30c1830da30c⟩,
  ⟨20,5,[0xaaaaaaaa, 0xaeaeaeae, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],hint 5 0xbbadcb66d8b56c0ae2a4a769aa5a84705b86096a2f4af294a026c681945c15c52 0x1abcb4845bdb76d803a800270001501735a6edbb6d48c412048a8c14a7814a6b140504985⟩,
  ⟨20,4,[0xaaaaaaaa, 0xaeae0000, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00],hint 5 0x2dcb62d5ab2a4a769aa11c16cd825a8af2a4a52809b1a0651705714803 0x4a5d508de10896163a6e2c591206813220631da60003232ac6⟩,
  ⟨20,5,[0xa2a2a2a2, 0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],hint 5 0xbfaeeb72d9b62a8a929fa769a705b86cd825bd302bca92949b1a05714803 0x1aab35e353cc66cd2aba528924424cc87a90857108f59000245505428da366f9bd3108584⟩,
  ⟨20,6,[0xaaaaaaaa, 0xcc00cc00, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],hint 6 0xb9edfb72d9b62d7b56bfaeeb8adaaca7e9da7296a3a84705b86cd825bd6a32cca31cc430cc02bca026c921d4721b468194571483e07803 0x23707a165a87204d659e59e9dc1a759679c7a78677a879e8de9e89c37c39961667e50d60c34038e8a238da0de0d59c455e5039c349f7e259689f7d15968d0662a1991e7a19e785e7a49e78e36e20c32d62ea7cda96a4b7cb2e82dd8dd76874b28b2e72d878c6275cb78bac300b2002c30eb0ab2c92dd3dd74e74b04b⟩,
  ⟨20,5,[0xaaaaaaaa, 0xcccccccc, 0xeeaaeeaa, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],hint 5 0x2d9b62d5b02bfaeeb8ab2aaa929fa769ca6a84705825a8c226c6d1a0651705915c52 0xca9a9e553f2f7e5545216bd09f77d804c00036000148220055d053b4e6b5cfcb8e703812⟩,
  ⟨20,4,[0xaaaaaaaa, 0xcccccccc, 0xeeaa0000, 0xf0f0f0f0, 0xff00ff00],hint 5 0xb62d5ab2a4a769aa11c16cd825a8af2a4a52809b1a0651705714803 0x4a5d563a6e2c59108de108961092813220631da63298600032⟩,
  ⟨20,5,[0x22aa22aa, 0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],hint 5 0xbbad9b62d5a929fa769ca3a84919c16096a4c0a92949b1a06515c52 0x149aa9e34bcc654c029000760001401d04b8a5729cf9b80b045304c28aa2a6f9bc1103484⟩,
  ⟨20,5,[0x33003300, 0xaaaaaaaa, 0xcc00cc00, 0xcccccccc, 0xf0f0f0f0, 0xffff0000],hint 5 0xbfeeeb9edcb66d8b56cdae2aca769aa11c16cd825a8c62bca9294a026c6d1a0651705714803 0x26574c24b84226860ee414a860613af473a1e70003b3a64733a8eccd93886b0b1fa7⟩,
  ⟨20,4,[0xaaaaaaaa, 0xcc00cc00, 0xcccccccc, 0xf3f0f3f0, 0xffff0000],hint 5 0xbbae7b72d8b569da69c16cd825a8af2a4a52809b1a0651705714803 0x2056402488422585ccab9297486132a6631da600034321e6⟩,
  ⟨20,5,[0xaaaaaaaa, 0xcc000000, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],hint 5 0xbf2eeb86dcb62d5b02bfa929fa769aa11c16cd825a8c9320af2a4a52809b1a0651705714803 0x20ee426574d2986424c0423884226868edc2d3bcfa132b463224631de60003533166⟩
]

def nodeBlock14 : Array Node := #[
  ⟨20,4,[0xcccccccc, 0xeeaaaaaa, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],hint 5 0x2eeb72d8b56a4a769aa11c16cd825a8af2a4a52809b1a0651705714803 0x732ce895914a5d432aa63220631da60926108de10896100032⟩,
  ⟨20,4,[0x22aaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],hint 5 0x2eeb72d8b56a4a769aa11c16cd825a8af2a4a52809b1a0651705714803 0x732ce895914a5d40926108de10896132aa63220631da600032⟩,
  ⟨20,5,[0x33ff0000, 0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],hint 5 0xb7ed9b62d7a929da6a84705b36096a2a4a52809b1705714803 0x17292dd18b8e75c4308042360422404939908669085510000bd2992e4b8ba2e8060199264⟩,
  ⟨20,5,[0xaaaaaaaa, 0xcc00cc00, 0xcccccccc, 0xf0f0f0f0, 0xff000000, 0xffff0000],hint 5 0x2ffbbae7b72d9b62d5b36b8a769a705b36096a334cc2bca9294a026c6d1a0651705714803 0x33e657ce786cc24b0438604227062fdc638a454a8dc613af273d7873a2070003a3a647⟩,
  ⟨20,4,[0xaaaaaaaa, 0xcc00cc00, 0xf0f0f0f0, 0xffcccccc, 0xffff0000],hint 5 0xbbae7b72d8b569da69c16cd825a8af2a4a52809b1a0651705714803 0x248860564041585ccab8614a5d232a660003431da6321e6⟩,
  ⟨20,4,[0xaaaaaaaa, 0xcc00cc00, 0xcccccccc, 0xfff0f0f0, 0xffff0000],hint 5 0xbbae7b72d8b569da69c16cd825a8af2a4a52809b1a0651705714803 0x2056402488422585ccab9297486132a6631da600034321e6⟩,
  ⟨20,6,[0x33003300, 0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],hint 6 0x2fbbbae7b86dfb72d9b62d7b56bfaeeb8ada9fa769ca6a96a39c16e1b36096f5a8d434cd2344d033cc42bca9294a026c991cc6b1a0651745c15c5210003 0x1c79cb5966d7af719721661a5e1e965985e86970e86d3a171ca6da42882a191a88a70990a594495c7024020a1098a436215c2a422d92ec88fb19acb88b2ca2e070d8257cb70b2e92db84c6e968b84bb8200b2402c20ae06e59e7a465991e795659950aa471c9a39a38618d44e68619657640824b0c052cb470c082cb⟩,
  ⟨20,5,[0xaaaaaaaa, 0xbbaabbaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],hint 5 0x2ffbeeeeb66d8b56bba929fa768495a46705825a8a926c681945c15c52 0x128a25a4434c64c80388002600013810e43a699a64d9341003d0b43a69b264d9340a054a5⟩,
  ⟨20,5,[0x88aa88aa, 0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],hint 5 0x2fbbbad9b62d5b36a4a7e9da5a8e959c16096a2a49b1a0651705714820 0x149aa9c54b8e754c2490423504224052b4be2ab2a6e9b8300c12d4b40aa2a6e9b82c0c0c6⟩,
  ⟨20,5,[0xaaaaaaaa, 0xcccccccc, 0xf3f0f3f0, 0xff00ff00, 0xffff0000],hint 6 0x395bbae7b86dfb72d8b5ed5a7e9da729aa5a89929c16e1b36096f5a8c62bca9294a026c9a1a0651705714803 0x49549f3cf7d58523d260f61c64570f3d86587122987ca61249c7dc05905b3c46d96813c10520538834d250130105804e7023983417011cf1de64b78f7476471c61d74895e25874871dc1d160845c4076078010074c01c10604d3⟩,
  ⟨20,5,[0x33003300, 0xaaaaaaaa, 0xcccccccc, 0xf3f0f3f0, 0xff00ff00, 0xffff0000],hint 5 0x35dbeeeeb9edcb62d5a769aa5a4a705b36096a318af2a4a52809b1a0651705714803 0xf6e1f32b6694bea12502378422604cab18c8918c7718000de2d8b56fd4e01c9b26⟩,
  ⟨20,5,[0x33000000, 0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],hint 5 0x2fcbeeeeb72d9b62d5b02bfa929da6a96a11c16cd825a8af2a4a52809b1a0651705714803 0x1ccd3a456492975c24b042378422584cac98c8898c7698000ce0cc3a92acb81d9b66⟩
]

def nodeBlock15 : Array Node := #[
  ⟨20,5,[0xaaaaaaaa, 0xcccccccc, 0xccff0000, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],hint 5 0xbfae1b7ed9b62d7a929da6a96a11c16cd825a8a9294a026c6d1705714803 0x184732139c10864d4ab328c9c2700cae108da1089210ca412d6a529de5299652d6a500031⟩,
  ⟨20,6,[0xaaaaaaaa, 0xcccc0000, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],hint 6 0x2e7b86dfb66d8b5ed5afebbae2b3ab2a4a7e9da729aa5a8ea11c16e1b36096f5a8dc36cda360d7358c72a4a7294a026c771a05c15c520b003 0x186d8a555696e161561e55ea1b16855579b7a860b7a92de618a29a024828d55638e609809aa44698642a4209e094a0351e4c2a028d27e355546bae461892bacc61896296279e8903e579e8e39e30821d51ea8eaa95a872871e91dd6097697076071e81d77885e8587787b020078001c20ac8201c61ea3aaa8da87047⟩,
  ⟨20,5,[0xaaaaaaaa, 0xcccccccc, 0xeeeeaaaa, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],hint 5 0xbbedfb72d9b62d5ab2a4a7e9da11c16096a2a49b1a06518c5c15c52 0x1497a9854b0e75452d48e4a92a2c8b0048000258001401c0039349ce8a92a8cab0c60380e⟩,
  ⟨20,5,[0x2222aaaa, 0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],hint 5 0xbbeeeb7ed9b62d5a929fa7684705825a8af2a49b1a05c15c52 0x1289256342ca54bc087000250001380c68b2298262b9ac0d0350c43209825eb7ac0d03484⟩,
  ⟨20,5,[0xaaaaaaaa, 0xcccccccc, 0xfcfcf0f0, 0xff00ff00, 0xffff0000],hint 6 0x374c06e7b7edeb76d9b62d5a929da729aa5a8ea11c7705b86cd825fd6f5a8d92a4a8294a026c681705714803 0x45545c38e71579139160e61b5446ce3985586d125870961145b71b04a06138d8626813810510547035114c170105804c6c23182c16c114e15f8927ce74520515c1574475dc58544515b15060641b3c5605801005640141060659⟩,
  ⟨20,4,[0x33330000, 0xaaaaaaaa, 0xcccccccc, 0xfcfcf0f0, 0xff00ff00],hint 5 0x2d8b56aca929da6a84705b36096a4e0a9294a026c681705714803 0x1086d02370422504a7794a6614000c56d934905c26149565⟩,
  ⟨20,5,[0xaaaaaaaa, 0xcccc0000, 0xcccccccc, 0xfcfcf0f0, 0xff00ff00, 0xffff0000],hint 5 0x3b2c06e1b7ed8b56aca929da6a84705b36096a364a9294a026c681705714803 0xd5c9b022e08436815cc23704225052bb36cdc42e12d6a529de529985000312d6a5⟩,
  ⟨20,5,[0x3300ff00, 0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],hint 5 0xb72d8b56a4a769ca5a8e705b36096a2bca026c681945714803 0x1a96a5e44be4f7c8238842c60422404a7994ae714a6514000c1a96a56b7c9f260581715c5⟩,
  ⟨20,5,[0x33330000, 0xaaaaaaaa, 0xcccc0000, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00],hint 5 0x2eeb72d8b56b8ab2a4a7e9da6a84705b36096a4e0d92dcaf2a4a52809b1a0651705714803 0x1298e8239042270571e46b4650813226631e060003632b667c6f12d1f4c870f699e6⟩,
  ⟨20,6,[0x33330000, 0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],hint 6 0x2eeb9edfb72d9b62d7afebbae2b3a929fa769ca6a8ea11c16e1b36096f5a8e2384df378dc34cb52bca9294a026c6e194641705714803 0x187989a19a67aa61261d81d95e96586575e76560a76629d61896696184585e78138105805a98369864198105d05494251d4c19411cc1e878ba219c77871e61dc6097266c76071e51d77485e5587747a410077c01c10697df84e5617954669a26188a698d6188e596075d82596375d861921041429a441c73e9a461c7⟩,
  ⟨20,5,[0xaaaaaaaa, 0xbbbbaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],hint 5 0x2ffbbae7b66d8b56c8a929fa7684705825a8a926c681945c15c52 0x1289a56442cc64c00378002500013810c432298a60b82c0d0351243249a25cb82c0d034a5⟩,
  ⟨20,5,[0x8888aaaa, 0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],hint 5 0xbfefebbae7b66d8b22c0afebba929fa7684705825a938380a926c65170571482f 0x175badb4a34c65d024c04236042248508b3acbcae6da342f0bc0e528eb82e2d9342f0bca5⟩
]

def nodeBlock16 : Array Node := #[
  ⟨20,4,[0x77005500, 0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xffff0000],hint 5 0x2eeb72d8b56a4a769a705b36096a4c0af2a4a026c681945714803 0x7916f08e21089412a26529985000306ae8d39db2485a1695c5⟩,
  ⟨20,5,[0xaaaaaaaa, 0xcc00ff00, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],hint 5 0x2dcb66d8b56a4a7e9da7296a39c16cd825a8af2809b1b4681945714803 0xaaaaa0454290850239842d684224862a7298c85214685a1322c633de631d660003233de6⟩,
  ⟨20,5,[0x33330000, 0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff000000, 0xff00ff00],hint 5 0xbeed9b62d5aeeaca929fa769aa5a84961c16cd825a93838ca9294a026c681705714803 0xd3908766744cc238042fa0422584a7914bbd94a6694000d58eb3991bb09364f0151585⟩,
  ⟨20,4,[0x33330000, 0xaaaaaaaa, 0xcccccccc, 0xff00ff00, 0xfff0f0f0],hint 5 0x2d8b56aca929da6a84705b36096a4e0a9294a026c681705714803 0x1086d02250423704a6614a7794000c4905c16d9366149565⟩,
  ⟨20,6,[0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff000000, 0xff00ff00, 0xffff0000],hint 6 0x365bf2fbbbae7b7edcb66d8b5ed5afebbae2b3a929da729aa5a8ea11c16e1b36096f5a8ea3a4e839ce6394e234ccb31caf2a8a9294a02709b25c8e1a0651705714803 0x1ea1e9db6e79f19e88676db9e7b6779e91b92c9c5b1b6e4d24b1e324a0c91e7acd2c926926a696265e4a6405206b6c4ae7a816c105e060a0381e7c14010510735b3cd5cc13c106405ab026a4641b0121b22f9cebdbb8834820922378b8e8888788207232532c93c8818822c21d90a76c708908c01008940201070965⟩,
  ⟨20,5,[0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffaaaaaa, 0xffff0000],hint 5 0xbfefbbbad9b62d5aeea4a7e9da11c16096a2aca926c681945c15c52 0x12d4bd499a952929844b1918b0c654403801c003802580014013449ca592aaa8b22c0380e⟩,
  ⟨20,5,[0xaaaaaa, 0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],hint 5 0x2fbbbad9b62d5b36b8a929fa7696a1256705825a8a926c681945c15c52 0x128aa5a4434c64cc0390002580013810a43a29b266d9b40f03d0e43209a266d9b40f03ca5⟩,
  ⟨20,5,[0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffcccccc, 0xffff0000],hint 5 0x2febf2eeb9edcb66d8ae29fa769aa59c16cd82330af2a4a52809b1a052 0x16872148a2a2a53da14360d6c0a5541c8b5800555476c1b011a42988531118210d2298853⟩,
  ⟨20,5,[0xcccccc, 0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],hint 5 0x2fcbbae7b72d9b62bba7e9da6a58705b3608af2a4a52809b1a052 0x1279a5813b0a54bd47a1d304c18f63c46888445884340a42149c769d304c18f63c0014852⟩,
  ⟨20,5,[0xaaaaaaaa, 0xcccccccc, 0xff00ff00, 0xfff0f0f0, 0xffff0000],hint 6 0xe0f81bc6eeb9edfb72d8b5ed5ab6a4a769ca6a8ea11c16e1b36096f5a8e3334af2b0a9294a02749b1a0651705714803 0x65165e90579145995951b5234518db89445495929478a51952479e04e05d4447647014410590507824193c17810540569435945413411911a090c8117c62c619e1936484de4866461871985096255c650684100668018106169a⟩,
  ⟨20,5,[0xaaaaaaaa, 0xcccccccc, 0xff000000, 0xff00ff00, 0xfff0f0f0, 0xffff0000],hint 5 0xe96fcbeef1bbadcb62d5ab6a4a769aa11c16cd825a8af2a4a52809b1a0651705714803 0x112b22e65d297566cdc70e092810896108de10eb4132ac631da6322063672600032⟩,
  ⟨21,6,[0xaaaaaaaa00000000, 0xcccccccc00000000, 0xf0f0f0f000000000, 0xff00ff0000000000, 0xffff000000000000],hint 6 0xd2747d1742d0740cff3ecf737cd331cbf2dcb325c731bc5f15c5310c3f0ec370cc2ec1aeab9ac4f33c8ef3b0340b82b 0x20d68d22225022269f20d20d20c20c22168f22125e20c68c28c28c29934d29929828c34c20b68b22024e22069d20b20b1cb94b1dc34d1dc95b1cb34b28b48b29530c29549228b30b2112112246932242632116911d13511d69421d63571d195129131129448129430c2914911942c01515401112cb0d4554⟩
]

def nodeBlock17 : Array Node := #[
  ⟨21,5,[0x8888888800000000, 0xaaaaaaaa00000000, 0xcccccccc00000000, 0xf0f0f0f000000000, 0xff00ff0000000000, 0xffff000000000000],hint 5 0x34cd2f3fcfb34ccf31cbb2dc7b1dc731bc5714c430fc370cc2ec1aeab9ac4ee3b4340c02e 0x2dba5a999529745467c8c5788854f5425b840578000a7c235358f62ac8b4286a4a5ce⟩,
  ⟨21,4,[0xaaaaaaaa00000000, 0xcccccccc00000000, 0xf8f8f8f800000000, 0xff00ff0000000000, 0xffff000000000000],hint 5 0x34cd2f3fcfb34ccf2ecb71ec771cc6f1ac5714c430fc370cc2c34 0x196431122210da25328a50e0a084e24ae69481e931847421c9⟩,
  ⟨21,4,[0xaaaaaaaa00000000, 0xcccccccc00000000, 0xf0f0f0f000000000, 0xff88ff8800000000, 0xffff000000000000],hint 5 0x34cd2f3fcfb34cc32dcb322c7b1cc6f15c5310c3f0dc330b0c02e 0x21a4419623191c352e8a10a0a08d036be6d39da96806d631a9⟩,
  ⟨21,5,[0xaaaaaaaa00000000, 0xcccccccc00000000, 0xeeeeeeee00000000, 0xf0f0f0f000000000, 0xff00ff0000000000, 0xffff000000000000],hint 5 0x349d173fcfb3dcc72ecb72cc731bc5f16c5714c430fc3b0dc330bb06baae6b13c4f0 0x217841d5739d133d4951a02811c07299363191a318ed344cc7e58c7498c69d9061994⟩,
  ⟨21,4,[0xe0e0e0e00000000, 0xaaaaaaaa00000000, 0xcccccccc00000000, 0xff00ff0000000000, 0xffff000000000000],hint 5 0xd173fcfb3dcb72cc9317c5b14c430fc3b0dc330b0c02e 0x21e04115c21116242a2842588120401bcc31b4831044340100⟩,
  ⟨21,4,[0xee00ee00000000, 0xaaaaaaaa00000000, 0xcccccccc00000000, 0xf0f0f0f000000000, 0xffff000000000000],hint 5 0x345cff3ecf72dcb31cc5f15c5310c3f0ec370cc2c34 0x115c2091a1089013a6073a04709c201bcc3130430a8233ace0⟩,
  ⟨21,5,[0x2222222200000000, 0xaaaaaaaa00000000, 0xcccccccc00000000, 0xf0f0f0f000000000, 0xff00ff0000000000, 0xffff000000000000],hint 5 0x34cd2745cff3ecd331cb72cc7b1cc6f17c5b15c5310c3f0dc330baeab90c02b 0x1915314f4294d12b9f8738d3704aa2a5964a5704a5454812e1487235cd72a8aa211a9⟩,
  ⟨21,5,[0x4444444400000000, 0xaaaaaaaa00000000, 0xcccccccc00000000, 0xf0f0f0f000000000, 0xff00ff0000000000, 0xffff000000000000],hint 5 0xd2f49cff3ecf733cc72dc771cc6f15c5310c3f0ec370cc2ebaae4340b82b 0x1d5539934318f031513294f6294cc2b5f76b45268426600ad89223b1ec7619867156b⟩,
  ⟨22,7,[0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000],hint 6 0xca71bc5311c370cc2f09b0abcae6b7ac6afa929da729aa668ea11df70dc16e9b86cdb06b1a86859464d8a5f1765c56f5a9655615050d1f3d4c12a4a52809b1ec781705714803 0xae0960b73618b7396aba0620be8628b72945b72637868968bb2809b28cc9be8820bb2cf27c1881b71604b718b0701601b818016e4cc36a4823b81cc1641a01bd2c82bd2a115c1c81586606b7588ab75634546886b86cc65278084e7ce6b86806406c86bdea07bdec9d3c6a063b6040346a403060412f6a69⟩,
  ⟨22,6,[0x888800008888, 0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000],hint 6 0x333ccb29c971cc6f0dc3306b0abdaf2b9abeaaa929da664a77dc1651494c11e4751c46d184551444d124450e4310942107409013f4fa3e4f83dcf62a49b1ec52 0x1e85eb1d76c86579d7a2762ae106b7708a18ab7838ac0e279eaecae37e3b9d76e7f18dd8ee79b8ec6e379ebacb9a8a08eb8238a266bad875cb5f72d75d5df7edb2dbde7afb32b5e7afaeab628adaebbe28ad1ad1238d65645134a675d99199075d9cf9e879ea0e36779e30b2a98a2a49a488a21c60268c01440a6b42⟩,
  ⟨22,5,[0x222200002222, 0x888800008888, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000],hint 5 0xccf32ca71cc6f11c3306ae6afaaaa4a769a929df705b3651494c0c12a4a52809b1ec03 0x16992de1cbca55d609d40e75e1ad7d446b084470843508004212cbaf6ba3eaf8c262⟩,
  ⟨22,5,[0x222200002222, 0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000],hint 5 0x332ca71cc6f11c370cabea4a769a929df705b365130304a9294a026c7b14803 0x2d315bc57798cb941388210bb35af90cf418cae18c8a180704b12c9ae6b93e4f086a3⟩
]

def nodeBlock18 : Array Node := #[
  ⟨22,5,[0x444400004444, 0x888800008888, 0xaaaa0000aaaa, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000],hint 5 0xccf32ca71cc6f0cc2706ae6afaaaa4a7684929df705945a9494c0a91ec781705714803 0x16a92de5cbcc65d908532ebdae8fb3c24a8423704224840082b5039d786b5f68c261⟩,
  ⟨22,5,[0x444400004444, 0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000],hint 5 0xccf29c6f0dc3309c1aafa929da11df705945a9492a49b1ec781705714803 0x2d505b8b671ceb984920846d084490a10a655775c5d3700356298a5d17474dd3784c6⟩,
  ⟨22,5,[0x808000008080, 0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000],hint 5 0xca711c3309af6bcae6afa929da6a84929c16e1b36516f5a8fc3ecc12a4a526c7b1e05c14803 0x20db4284ed0e786c23d042290431584a8e14a6994b4714000d54dbb710cc134605e5⟩,
  ⟨22,4,[0x707000007070, 0xaaaa0000aaaa, 0xcccc0000cccc, 0xff000000ff00, 0xffff00000000],hint 5 0x329c470cc26afa929da6a84929c16cd945a8c12a4a526c7b1e05c14803 0x62a4c08e61089c12a2a5299e500031812d039d946852181565⟩,
  ⟨22,4,[0x7f7f00000000, 0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00],hint 5 0xca711c3309abea4a769aa11c16cd945a8c12a4a52809b1ec781705714803 0x4a5d508de1089613220631da60003263a6e2c6f12068151ac6⟩,
  ⟨22,5,[0x888800008888, 0xaaaa0000aaaa, 0xcccc0000cccc, 0xf8f80000f8f8, 0xff000000ff00, 0xffff00000000],hint 5 0xccf32ca71cc6f0cc1ab7abeaaa929d929df705b36516a52530400ff3f8fb2a47b 0xb4c56e05dc10ae8f4e1e632ecd6ba873a5955e573751d57c0a92264b1ac4e4214a⟩,
  ⟨22,4,[0xaaaa0000aaaa, 0xcccc0000cccc, 0xf8f80000f8f8, 0xff880000ff88, 0xffff00000000],hint 5 0x333ccb29c730cabeaea9ea4a869da6a8477dc16cd945a9492a47b 0x311e65024a084d06ba6d18db1421b010887296864a60a5adac⟩,
  ⟨22,4,[0xaaaa0000aaaa, 0xcccc0000cccc, 0xf8f80000f8f8, 0xff000000ff00, 0xffff00008888],hint 5 0x333ccb29c731bc6311c3309abeaaa929d77dc16cd945a9302a47b 0x3116640248084cd18e69108d16310d2948781a86739a87bd49⟩,
  ⟨22,4,[0x777700000000, 0xaaaa0000aaaa, 0xcccc0000cccc, 0xf8f80000f8f8, 0xff000000ff00],hint 5 0xccf32ca70cabea7a929d705bd6cd945d16a525232a49b1ec52 0x18d7031dc6000d04aa691092c210cd42deb0b22c41a462a509⟩,
  ⟨22,5,[0x707000007070, 0xaaaa0000aaaa, 0xcccc0000cccc, 0xff000000ff00, 0xffff00000000],hint 5 0x329c6f14c470dc330bc26afa929da729aa668ea124a77dc16cd945a8c12a4a526c7b1e05c14803 0x6459a52b51b314c0b43850f0db85410b030d0a0c787412a8bc6a38ad95a52e8b361a7a91585e8405a80a10f6b5a2a998932af5234cb0f4d1e8c66759cd5d4086954e421a76992973d5d0a5⟩,
  ⟨22,5,[0x707000007070, 0x888800008888, 0xaaaa0000aaaa, 0xcccc0000cccc, 0xff000000ff00, 0xffff00000000],hint 5 0xccf32ca71cc6f0cc1ac2abeaaa929d929df705945253041905411032a49b1ec52 0xb5456f561e842ec94a9955e5757c0ea328ab22c00109c1bb8635d1ad751d3a3a4e⟩,
  ⟨22,4,[0x707000007070, 0xaaaa0000aaaa, 0xcccc0000cccc, 0xff880000ff88, 0xffff00000000],hint 5 0x332ca726c730cabea7a92a0a769aa5e8492a3d705942a49b1ec52 0x291e542688001115324a109453190d5866b18cb03a1c85aa0a⟩
]

def nodeBlock19 : Array Node := #[
  ⟨22,4,[0x707000007070, 0x770000007700, 0xaaaa0000aaaa, 0xcccc0000cccc, 0xffff00000000],hint 5 0xca711c3309abea4a769aa124a705b36516a4c0c12a49b1ec7814803 0x8a4121a84000305a62b385a1591c478eaf605017914429573⟩,
  ⟨22,4,[0x707000007070, 0xaaaa0000aaaa, 0xcccc0000cccc, 0xff000000ff00, 0xffff00008888],hint 5 0x329c9b12c470cc2b09c12afa929d929df705942a49b1ec52 0x2914500189634ac109e67c22f5ad894064818cae3b10c43dcf⟩,
  ⟨22,4,[0x707000007070, 0x777700000000, 0xaaaa0000aaaa, 0xcccc0000cccc, 0xff000000ff00],hint 5 0xca711c3309abea4a769aa124a705b36516a524a92949b1ec5c14803 0x89a1215c4000304ae2b486413928431973605017914478eaf⟩,
  ⟨22,5,[0x707000007070, 0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000],hint 5 0x31bc470dc26afa929da6a99a11c16e1945bcc1294a026c781705714803 0x18a9314e53994650249842368422884a8a94a7794a6b14000c54e539946521088521b1565⟩,
  ⟨22,5,[0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff880000ff88, 0xffff00000000],hint 5 0xccb2cca726c731bc370cabea8a9ea4a829da6e9aa6697a26848f5df705942a49b1ec52 0x2acb5212ab99485711d458684cb96ea146ea8dc52d2b44191722ae6da088b9408a810545eb743912a264e8a2886119a33f44c30ccb544c28995658a565196736d4a31ccb20ec81d8845a10⟩,
  ⟨22,5,[0x888800008888, 0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff880000ff88, 0xffff00000000],hint 5 0xccf32ca71cc6f0cc1abcabeaaa929da6a84929df705945253042d0a40cfe2a47b 0x94452e05dc10a68f461e6326cb5ba873a1554e533751d57c0a8222491b84e631ad⟩,
  ⟨22,4,[0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff880000ff88, 0xffff00008888],hint 5 0xccb29c9f26c7f1cc470cc26afa929da6a84929df705942a47b 0x18943402480846c31a695ac6e2950c39e046b603845907be09⟩,
  ⟨22,4,[0x777700000000, 0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff880000ff88],hint 5 0x332ca726c730cabea7a929da6e9aa26848f5c1651492a49b1ec52 0x18cd000111425c81094652e0a39d0d299e60b26c2a28822a4a⟩,
  ⟨22,5,[0x770000007700, 0x888800008888, 0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xffff00000000],hint 5 0xccf32ca71cc6f0cc1abdadeb1abeaaa929d929df7059452530435042a49b1ec52 0xc0dd8d461ab5b2873a153651956b8a88208c8b000109287a4634d0c64d935ca649⟩,
  ⟨22,4,[0x770000007700, 0x777700000000, 0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0],hint 5 0xca711c3309abea4a769aa11c16cd945a9494c0a92809b1ec5714803 0x892121564000301beaf506414128431993385a1611c462a2c⟩,
  ⟨22,5,[0x888800000000, 0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000],hint 5 0xca714c470cc2f09b0abdaf2afa929da6a84705b36516a5251043ca9294a026c7b1705714803 0x1eda3e44ec9087e82dc042380422604abd94a7894a6714000cd4dabecf4caf2c8785⟩,
  ⟨22,4,[0x70700000f0f0, 0xaaaa0000aaaa, 0xcccc0000cccc, 0xff000000ff00, 0xffff00000000],hint 5 0xca711c3309abea4a769aa11c16cd945a8c12a4a52809b1ec781705714803 0x7326e0928108de132ac63220600032896f14a5d510561399a6⟩
]

def nodeBlock20 : Array Node := #[
  ⟨22,4,[0x777700000000, 0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00],hint 5 0x329c470cc26afa929da6a84705b36516a524a9294a026c7b1705714803 0x421b408dc10894129de529985000315b64d242d058661496a5⟩,
  ⟨22,5,[0x888800008888, 0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00008888],hint 5 0xccf32ca71cc6f11c3309c1ab1abeaaa929d929df70594525304410a414ff2a47b 0x943d2c05d810a66d461a6326cb5b2673a1554e53164d956b8a8824891b04c94a94⟩,
  ⟨22,5,[0x777700000000, 0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00],hint 5 0xca71cc6f11c370cc26afa929da729aa668ea11df705b86cd945bd6a524a9294a026c7b1705714803 0xd3d16da2cf7eb7a0bc32d8e4f887610d82bd0976507412ecb579ebba15e52e8aeb19da696c5e8405b80a10f6f766d937be7bc31ef9e88cb599afced6679900861ecb0218752c2959de40a5⟩,
  ⟨22,5,[0x777700000000, 0x888800008888, 0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00],hint 5 0xccf32ca71cc6f0cc1ab9abeaaa929d929df70594525304350b419002a49b1ec52 0x31ae8842ecd6ba955e573751d57c0eb32cae238001094b8ac2ebb94fc3d295324a⟩,
  ⟨22,5,[0x777700000000, 0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000],hint 5 0xc731bc530dc330ba929da6a84705b36516a304a9294a026c781705714803 0x1b4a36139c1086cc24b842370422504a9b14a7794a6614000c56ba368d9c270b8641b16a5⟩,
  ⟨22,5,[0x888800008888, 0xaaaa0000aaaa, 0xeeee0000eeee, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000],hint 5 0xccb29c731bc370cc26afaaaa4a7692a124a775c1651785a94b4c117458a926c7b1e05c15c52 0x1cdb3a64e4cc67628aed12976e109a2af6d72e6331394b5400ee000a2000560380a0⟩,
  ⟨22,4,[0x666600006666, 0xaaaa0000aaaa, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000],hint 5 0x332ca70cc2704abea4a76848f5c16516a48ca91ec5c15c520ac0d02003 0x62e2c79eaf4219400e40009a00052024ec4238c4228a480080⟩,
  ⟨22,4,[0x888800008888, 0xaaaa0000aaaa, 0xe0e00000e0e0, 0xff000000ff00, 0xffff00000000],hint 5 0xc870cc2708c1aafaaa92a124a775c1651785a87b1e05c15c5204403 0x14982986ab021551eb4be4a4222c73045988446884338800⟩,
  ⟨22,5,[0x888800008888, 0xcccc0000cccc, 0xeeee0000eeee, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000],hint 5 0x329c971bc470dc3308c1aafaaaa4a769aa49dd705b3651785251a464c12a4a52809b1ec52 0x1aba3621e44a56dd295a1b66ea358ee6b74d4a6e1ef8de5211b221120210d8238800⟩,
  ⟨22,4,[0x666600006666, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000],hint 5 0xca711c3304abea4a769a8f5c16cd9448cc12a4a52809b1ec520ac0d02003 0x7326e896f14a5d500e80009e0005603594634106334e690080⟩,
  ⟨22,4,[0x888800008888, 0xcccc0000cccc, 0xeeee00000000, 0xf0f00000f0f0, 0xff000000ff00],hint 5 0x329c470dc32a6a929da6a4a775c16cd494c0c12a4a52809b0b803 0xa55450a8282ea38e75498c745e85bc44688434884698800⟩,
  ⟨22,5,[0x888800008888, 0xaaaa00000000, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000],hint 5 0x333ccb2eca71cc6f14c470dc3306ae6a4a769a929df705b352d494c0a9294a026c03 0x4aa496c6ed2113171f2e295365adb131aa9d260d8b6aec382a9842360422404000d1e1⟩
]

def nodeBlock21 : Array Node := #[
  ⟨22,5,[0x555500000000, 0x888800008888, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000],hint 5 0xc731bc5714c3308c1ab9a9aa4a769a929df775c16cd494c0c12a4a52809b0b803 0x1488a9e143ca5556085c0e7565ad7d4469084470843488006230aa2aef9bf10cc2c2⟩,
  ⟨22,5,[0x888800008888, 0xaaaa0000aaaa, 0xc0c00000c0c0, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000],hint 5 0xccf32c971cc6f0dc3309c1ac2abeaaa9299a124a77dc16516f5a9494c07b1e05c14803 0x5262a2112e559557a74f29558630c64aeeadaa73ae6ef83c23a0422684353842890400⟩,
  ⟨22,5,[0x303000003030, 0x888800008888, 0xaaaa0000aaaa, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000],hint 5 0x333ccb25c871cc6f0cc2707b0aafaaaa4a4a84929df705945bd494c078170571483004403 0x16a92da2cb4215d108532ebe2f4d7b466a8c6570c6498c0086d50c2ce7b3611bc123⟩,
  ⟨22,6,[0xaaaa0000aaaa, 0xcccc0000cccc, 0xeeee0000eeee, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000],hint 6 0x329c6f14c470dc330bc26c2af6bcae6afaaaa4a769ca6a99a3a8477dc16e1b36516f5a9414fd3e4f53c4e5374d5334b52c4992548920461153e4f7304a9294a026c7b1e05c15c52 0x229a2d1f7f49ac89f8a97e9ce61337f8a66a73888a742298a2cf4cdc7dfb5bb6d7df69962e8a2bd75af8a2b95b94a69c13c30a694914008c0c9f0f28f101f0008809740a58a4034000a407b305ea5d03300e2aa02d0057c5da32767f5163145d05a221e8d27162145cc58691a1ce016914f2f716d14f00014e14d32b⟩,
  ⟨22,5,[0x222200002222, 0xaaaa0000aaaa, 0xeeee0000eeee, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000],hint 5 0xccb29c7311c3309ae6afaaaa4a769aa124a705b36516a52d30484c12a4a52809b1ec781705714803 0x22fc46a5f55298eecdfd98c8f652aaccae18c8a18c7818000e8810cc610b841c86e1⟩,
  ⟨22,4,[0x222200002222, 0xaaaa0000aaaa, 0xe0e00000e0e0, 0xff000000ff00, 0xffff00000000],hint 5 0x321c3309c12afaaa8492a3d705b36516a1ec78170571482b0440d02003 0x1ab935e9b3c636d4049800270001600b4414b0394aa31620⟩,
  ⟨22,5,[0x444400004444, 0xcccc0000cccc, 0xeeee0000eeee, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000],hint 5 0x329c971bc470cc2708c1ab9abeaaa769aa11c16cd945a949490c12a4a52809b1ec781705714803 0x20eac265f4d298698c72e18872779f424c8423884226840036d463490633ce6b1a81⟩,
  ⟨22,4,[0x444400004444, 0xcccc0000cccc, 0xeeee00000000, 0xf0f00000f0f0, 0xff000000ff00],hint 5 0x329c470cc26a6a929da6a3d705b352523304a9294a026c2e0ac0d02003 0x1086d16d93490b40027000150003980af394ac314b549620⟩,
  ⟨22,5,[0xaaaa0000aaaa, 0xcccc0000cccc, 0xe0e00000e0e0, 0xff000000ff00, 0xffff00000000],hint 6 0xca725c5311c370cc2f09abeaaa769ca6a99a3a8477dc16e1b36516f5a92145cc12a4a52809b1ec781705714803 0x49649f3cf7d66d23d264f65e58578f8d95997922597c965249e7de05305d3c47537013c10520557c35525017c105904e78239934178118f1a14ca84f8064c619f19848861f5c648619e19164745e4066468810063001810622da⟩,
  ⟨22,5,[0xaaaa0000aaaa, 0xcccc0000cccc, 0xe0e00000e0e0, 0xeeee0000eeee, 0xff000000ff00, 0xffff00000000],hint 5 0xca725c470cc26c2abeaaa769aa11c16cd945a92b4a92949d21304a9294a026c7b1e05c15c52 0x1285e50741b264975276a844b58a807900053028000bc054eca53d0bc294d1280b6⟩,
  ⟨22,4,[0xaaaa0000aaaa, 0xcccc0000cccc, 0xe0e00000e0e0, 0xee000000ee00, 0xffff00000000],hint 5 0xca711c3309abeaaa769aa11c16cd945a8c12a4a52809b1ec781705714803 0x7326e896f14a5d50928108de10896132ac63220631da600032⟩,
  ⟨22,4,[0xee000000ee, 0xaaaa0000aaaa, 0xcccc0000cccc, 0xe0e00000e0e0, 0xffff00000000],hint 5 0x329c470cc26afaaa9da6a84705b36516a304a9294a026c7b1e05c15c52 0x812d000e60005402a6a529985014116c96da3508038022bca7⟩
]

def nodeBlock22 : Array Node := #[
  ⟨22,4,[0xaaaa0000aaaa, 0xcccc0000cccc, 0xe0e00000e0e0, 0xeeee00000000, 0xff000000ff00],hint 5 0xca711c3309abeaaa769aa11c16cd945a8c12a4a52809b1ec781705714803 0x63a6e4a5d5896f108de109281089613220632ac631da600032⟩,
  ⟨22,4,[0xeeee, 0xaaaa0000aaaa, 0xcccc0000cccc, 0xe0e00000e0e0, 0xff000000ff00],hint 5 0x329c470cc26afaaa9da6a84705b36516a304a9294a026c7b1e05c15c52 0x421b4009c00054029de529985014116c9ab85a0404c032d4a9⟩,
  ⟨22,5,[0xaaaa0000aaaa, 0xcccc0000cccc, 0xe0e00000e0e0, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000],hint 5 0xc470dc26afaaa9da6a99a11c16e1945bcc12949b1e05c14803 0x1488290c431525490c43152549ce08e210896109ce109ce121a64215a422524225240002f⟩,
  ⟨22,5,[0xe0e00000e0e, 0xaaaa0000aaaa, 0xcccc0000cccc, 0xeeee0000eeee, 0xff000000ff00, 0xffff00000000],hint 5 0xca711c3309c1ab7abeaaa769aa124a705b36516a4c9314bd2e304a9294a026c7b1e05c15c52 0x117de2f6bd915c7001e80014c120153c294f42e4a02dabd2577142155038012c0a6⟩,
  ⟨22,4,[0xaaaa0000aaaa, 0xcccc0000cccc, 0xe0e00000e0e0, 0xff000000ff00, 0xffff00000000],hint 5 0xca711c3309abeaaa769aa11c16cd945a8c12a4a52809b1ec781705714803 0x7326e896f14a5d50928108de10896132ac63220631da600032⟩,
  ⟨22,4,[0xee000000ee, 0xe0e00000e0e, 0xaaaa0000aaaa, 0xcccc0000cccc, 0xffff00000000],hint 5 0x329c470cc26afa769aa11c16cd945a8c12a4a52809b1ec781705714811 0x926132aa6098208d8b10ac22334c77498e0bc23340c84a68e⟩,
  ⟨22,4,[0xe0e00000e0e, 0xaaaa0000aaaa, 0xcccc0000cccc, 0xeeee00000000, 0xff000000ff00],hint 5 0x329c470cc26afa769aa124a705b36516a304a9294a026c7b1e05c15c52 0x5b64d009e000e6029e052a6a50140ea35088d891028012b0a6⟩,
  ⟨22,4,[0xeeee, 0xe0e00000e0e, 0xaaaa0000aaaa, 0xcccc0000cccc, 0xff000000ff00],hint 5 0x329c470cc26afaaa9da6a84705b36516a304a9294a026c7b1e05c15c52 0x9c029de501411a3508028012b0a66c9ab04c032d4a981216⟩,
  ⟨22,5,[0x101000001010, 0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000],hint 5 0x329c6f11c3309af6bcae6afaaaa4a769aa11c16cd945a9344b8c12a4a52809b1ec781705714803 0x20eb4265f4d2986c24d042388422684cae18c8918c7798000d58ebbb10cc173a07a6⟩,
  ⟨22,4,[0xaaaa0000aaaa, 0xcccc0000cccc, 0xefef00000000, 0xf0f00000f0f0, 0xff000000ff00],hint 5 0xca711c3309abea4a769aa11c16cd945a8c12a4a52809b1ec781705714803 0x4a5d563a6e2c6f108de108961092813220631da632ac600032⟩,
  ⟨22,5,[0xaaaa0000aaaa, 0xcccc0000cccc, 0xee000000ee00, 0xeeee0000eeee, 0xf0f00000f0f0, 0xffff00000000],hint 5 0xca71cc6f11c3309af6b7ac6afaaa9da6a84705b36516a4d927304a9294a026c7b1e05c15c52 0x122764dab572b494f6d1e843f37780780002c07000140054e8a5338bb294f1280b3⟩,
  ⟨22,4,[0xaaaa0000aaaa, 0xcccc0000cccc, 0xee000000ee00, 0xeeee00000000, 0xf0f00000f0f0],hint 5 0xca711c3309abeaaa769aa11c16cd945a8c12a4a52809b1ec781705714803 0x2c6f14a5d57326e089610928108de131da632ac63220600032⟩
]

def nodeBlock23 : Array Node := #[
  ⟨22,5,[0xee000000ee, 0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xffff00000000],hint 6 0x329c5311c370cc2f09c22afa769ca6a99a3a8477dc16e1b36516f5a930304a9294a026c7b1e05c15c52 0x5cd5dc50470d81751701101b3436d168034001700c7013172c070014d15f4497cd78544515c14f5c63dc3855c564000528514001928a40d41d51874d35051075c7105d041c21d5c87400104d240001d4c240515d595745150587⟩,
  ⟨22,5,[0xee000000ee, 0xaaaa0000aaaa, 0xcccc0000cccc, 0xeeee0000eeee, 0xf0f00000f0f0, 0xffff00000000],hint 5 0xca711c3309c22bcabeaaa769aa11c16cd945a93b4e9304bd29304a9294a026c7b1e05c15c52 0x15276b0741b55d5401e8000bc0c0153c294d12e4a02da5784b724231204c022d0a7⟩,
  ⟨22,4,[0xee000000ee, 0xaaaa0000aaaa, 0xcccc0000cccc, 0xeeee00000000, 0xf0f00000f0f0],hint 5 0x329c470cc26afa769aa11c16cd945a930304a9294a026c7b1e05c15c52 0x246d10056000e60299a52a6a50140aa39087498e03c022c0a7⟩,
  ⟨22,4,[0xeeee, 0xee000000ee, 0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0],hint 5 0x329c470cc26afaaa9da6a84705b36516a304a9294a026c7b1e05c15c52 0x5402998501411a3508038022bca785a0404c032d4a96adb2⟩,
  ⟨22,5,[0xaaaa0000aaaa, 0xcccc0000cccc, 0xeeee00000000, 0xf0f00000f0f0, 0xff000000ff00],hint 6 0x329c5311c370cc2f09abea4a769ca6a99a3a8477dc16e1b36516f5a924468c12a4a52809b1ec781705714803 0x7922597c965249e7de3df3d649259f6cf49259e14f6593de8966590520557c35525017c105904e78239934178105305d3c47537013c119f19848861f5c648619e19164745e40664618f1a14ca84f8064c630100668018104b69a⟩,
  ⟨22,5,[0xaaaa0000aaaa, 0xcccc0000cccc, 0xeeee00000000, 0xeeee0000eeee, 0xf0f00000f0f0, 0xff000000ff00],hint 5 0xca711c3309ae6afaaaa4a769aa11c16cd945a93a4d9314a924304a9294a026c7b1e05c15c52 0x844b72749b56557096244af6b9800530002f058001e8053d0a5344aa2953c280b7⟩,
  ⟨22,5,[0xaaaa0000aaaa, 0xcccc0000cccc, 0xeeee00000000, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000],hint 5 0x332c530dc330ba929da6a84705b36516a2a4a52809b1705714803 0x17292dd18b8e75c52992e4b8ba2e0c28108d81089010c20124e64219a42154424e640002f⟩,
  ⟨22,5,[0xeeee, 0xaaaa0000aaaa, 0xcccc0000cccc, 0xeeee0000eeee, 0xf0f00000f0f0, 0xff000000ff00],hint 5 0xca711c3309ac6afaaa9da6a84705b36516a52d495013b4c92b304a9294a026c7b1e05c15c52 0x844f7364f365d940150000c00f014f5294d22b8a02de789c6ddb11b1068032f0a9⟩,
  ⟨22,4,[0xaaaa0000aaaa, 0xcccc0000cccc, 0xeeee00000000, 0xf0f00000f0f0, 0xff000000ff00],hint 5 0xca711c3309abea4a769aa11c16cd945a8c12a4a52809b1ec781705714803 0x4a5d563a6e2c6f108de108961092813220631da632ac600032⟩,
  ⟨22,5,[0x111100000000, 0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000],hint 5 0x329c731bc470cc26c2af6bcabea4a769aa11c16cd945a942500c12a4a52809b1ec781705714803 0x20eac265f4d2986824c842388422684cad98c8918c7798000d16eb42f064f13e8786⟩,
  ⟨22,4,[0xaaaa0000aaaa, 0xcccc0000cccc, 0xe0e00000f0f0, 0xff000000ff00, 0xffff00000000],hint 5 0xca711c3309abea4a769aa11c16cd945a8c12a4a52809b1ec781705714803 0x7326e896f14a5d50928108de10896132ac63220631da600032⟩,
  ⟨22,6,[0x222200002222, 0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000],hint 6 0x332ca71cc6f14c470dc32c2af6bcae6afa929da729aa664a77dc16e1b36514f5394d5314a521475194551130480f6304a9294a026c7b14803 0x186d89955666e061561e55e95b0a556b79b7a56067a619e61896695f65fa9556a66c7d57ea60a7e629f618aa6a9479a7e569f79e4e5943543a191e85670d90c398375815d99c0d80c39435de1179560de0d24400c90c87df41556165985554f6598a69a36188e69a26183a596479e92594d79e3090617c12c8a610c3⟩
]

def nodeBlock24 : Array Node := #[
  ⟨22,5,[0x888800008888, 0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000],hint 5 0x333ccb29c731bc3306b0abdaf2b9abeaaa929d929df7059452530440fb2a49b1ec52 0x250f4b03860c69ab519698c9bad6ca9ce85593a4d195659ae2a2088a6492326c00042⟩,
  ⟨22,5,[0xaaaa0000aaaa, 0xcccc0000cccc, 0xeeee0000eeee, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000],hint 5 0x329c6f11c3309b0abdaf2b9abeaaa929da6a84705b36516a5012e304a9294a026c7b1e05c15c52 0x3db57c89e9210fdb6cd5bf0fbcb325007a000500002c04c054f0a53c4a5338bd280b4⟩,
  ⟨22,5,[0x202000002020, 0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000],hint 5 0x329c6f15c470cc26bdaf2afa929da6a8477dc16cd945bcc5304a9294a026c781705714803 0x1cca3a4ae490876824b842380422904a9c94a7894a6694000cd8f63eaeb3b1258765⟩,
  ⟨22,5,[0xaaaa0000aaaa, 0xcccc0000cccc, 0xd0d00000d0d0, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000],hint 5 0xc470dc3309abea4a769aa668477dc16e1945bd6a304a526c7b1e05c14803 0x18a9b08453d96655aa6a99665a3108e81089c10c9010a64129ee529a052ad652ad6500032⟩,
  ⟨22,5,[0x222200000000, 0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000],hint 5 0xccb29c6f11c370cc2ea4a769aa11df705b36516a304a9294a026c781705714803 0x1aeab634c45086d024c842378422504a9b14a7814a6614000c96bab6ada4691986e5⟩,
  ⟨22,5,[0xaaaa0000aaaa, 0xcccc0000cccc, 0xdddd00000000, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000],hint 5 0x31cc5714c330bc26bdaf2afa929da6a8477dc16cd945a8a9294a026c7b1705714803 0x18a932045410865daa9b28ccc3300aaa108dc1089210db412e30529de5299652e30500031⟩,
  ⟨22,5,[0x222200002222, 0x444400004444, 0xaaaa0000aaaa, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000],hint 5 0xccb29c731bc3309c12afa929da124a8f5c16516a4c123458a926c7b1e05c15c520ac0d02003 0x20fb4288e514a86403b800288001602afed5ad86e52a6520260e424cc4238a4d0164⟩,
  ⟨22,5,[0x222200002222, 0x444400004444, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000],hint 5 0xccf29c6f11c3306c12afa929da6a3d77dc16cd9452523464c12a4a52809b1ec520ac0d02003 0x20eb4285e512986403b800290001600da518d3418cf39aa06b5d1dc3b0c533420166⟩,
  ⟨22,5,[0x222200002222, 0xaaaa0000aaaa, 0xc0c00000c0c0, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000],hint 5 0xccb1cc6f0dc3309c12afa9299a124a8f5c16e1945bd6a4c12848c7b1e05c1482b03403 0x1cca38c6649d875e6cdcd2976a1000aa0005e0034e0021a01d8a31c4831aae358f20⟩,
  ⟨22,5,[0x222200002222, 0x303000003030, 0xaaaa0000aaaa, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000],hint 5 0xccb21c731bc3309c1f04b0aafa928492a3d705b36516f4c1281e05c15c520c02b0440d02003 0x7b68f8979118df7012c000a00005c09f5b3dbd6bcc660500d8498d2418d139b40332a6⟩,
  ⟨22,6,[0x444400004444, 0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000],hint 6 0x333ca725c6f0dc330bc2706b0abdaf2b9abea4a7699a3a8477dc16516f5a9575595554d525454d5314951544488f82a49b1ec781705714803 0x18718a175e871f61761d5dd9dc1675eb75c7676077681dd6189e89c16419971266650570416016e80db61a0680417415a70967550670545cca593295d74d9669a29a9862aa2ca5862a9e4a5d7699e7a9d74e3402410692294996605d78196515d7858622a28898621a2841d7639e78dd74f9e72887a00412c91a0a46⟩,
  ⟨22,5,[0x404000004040, 0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000],hint 5 0xc6f11c370cc26afa929da6a99a11df705b86516a304a52809b1ec781705714803 0x1aba34a55c1b76d824a842378422504c9c18c8898c7b18000e5cb72db76de5298586⟩
]

def nodeBlock25 : Array Node := #[
  ⟨22,5,[0xaaaa0000aaaa, 0xb0b00000b0b0, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000],hint 5 0x329c6f15c470cc26bdaf2afa769aa11df705b86cd945bcc5304a92949b1e05c14803 0x1aa93628d44c66e023a8422784294854e53a6da36d14852121ee421604245640003923324⟩,
  ⟨22,5,[0x444400000000, 0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000],hint 5 0xc7315c530cc26bdaf2afa929da6a8477dc16cd945a8c12a4a52809b1ec781705714803 0x1cca3a456492976024b842380422584ca618c8898c7698000cdecabaced4b52d8726⟩,
  ⟨22,5,[0xaaaa0000aaaa, 0xbbbb00000000, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000],hint 5 0xca71bc5311c370cc2ea4a769aa11df705b36516a2a4a52809b1705714803 0x16c9adf2bbce75c8318842368422405299ae6b93e4f8862125a84219c42154400030256c4⟩,
  ⟨22,5,[0x444400004444, 0xaaaa00000000, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000],hint 5 0x333ca71bc5311c370cc2f06c1704a929da6a3d77dc16cd4948ca9294a026c0d02003 0x14baa9d4cb8c655013800026000138108c2b4a93a8e882601d9631b4a31a483782e3⟩,
  ⟨22,5,[0x444400004444, 0x555500000000, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000],hint 5 0x31bc5714c3309c2306c16b9a9aa4a769a8f5df705b352523304a9294a026c2e0ac0d02003 0x6ae6d89171421b900f00009e00054072f8dbb771b4780a80ab494b0394ac316402ea85⟩,
  ⟨22,6,[0xa0a00000a0a0, 0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000],hint 6 0xca725c5714c470dc330bc26c2af2b9adeafa929da729aa668ea11df705b86cd945bd6458d6057d5d56d5a565463e8c5304a92949b1e05c14803 0x176d7a145286e05d45de51eadb22b52d79b7ab5c67a819e5d7ae8ac16019940e66250540415c16a809a5d90680417814e44d3793052044504a981ea529118104a0475715da1c11710434491e7a4915b010047c010106c7df4545226188945106188e18e15d784f3a35d790d9e279e3134ca0412d34c90419245a2104⟩,
  ⟨22,5,[0xaaaa0000aaaa, 0xcccc0000cccc, 0xecec0000ecec, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000],hint 5 0xca725c6f15c470dc32afaaaa8a769aa65df705b36517a5bd6a4b8c5304a9294a026c52 0x1aba3626dc4846e16f5bdb66da3589d2b7252a9262942000096e108e0108981c843a48433⟩,
  ⟨22,5,[0x4c4c00004c4c, 0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000],hint 5 0xca71bc470dc32afaa29da69df705b86cd945e96f4a0c12a4a526c7b15c52 0x1aa93602bc0a56cd0a721098a02144c66a8c6478c7058ce31d9ca729b46d21384c001d86c⟩,
  ⟨22,5,[0x505000005050, 0xa0a00000a0a0, 0xaaaa0000aaaa, 0xcccc0000cccc, 0xff000000ff00, 0xffff00000000],hint 5 0x329c5711c3309ae6afa929da6a84929df705b36516a570c12a4a52809b1ec781705714803 0x1edb3c24c0423904cad18c8998000d4a56c32f5bc41604e6a37944a5fb8868171af4⟩,
  ⟨22,4,[0x505000005050, 0xaaaa0000aaaa, 0xcccc0000cccc, 0xffa00000ffa0, 0xffff00000000],hint 5 0x329c470cc26a4a769a929c16cd945a8c12a4a026c7b1e05714803 0x1845302388422484a8994a6714000c1eaa3ce7649a178565⟩,
  ⟨22,5,[0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xffa00000ffa0, 0xffff00000000],hint 5 0xdb733ca715c5311c370bc26a4a769ca6e9aa6698a11df705b86cd945e16f5795c304a926c7814803 0x6a9b973b2a535cdaaabc8c38aed635e3495c92ad6f33c0b83850b0eb85410b428ca10d787210d428fa115404e11a87b7176ad0dc31e4746b29990da31987eacfdf58ea3f0403b00610fac9⟩,
  ⟨22,4,[0xaaaa0000aaaa, 0xc0c00000c0c0, 0xcccc0000cccc, 0xffa00000ffa0, 0xffff00000000],hint 5 0xca723c470cc269da6e9a705b86cd945bd6a304a926c7b1e05c14803 0x1a453423884224060aac0c66c92129e652b1c5000342bd65⟩
]

def nodeBlock26 : Array Node := #[
  ⟨22,5,[0xa0a00000a0a0, 0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xffa00000ffa0, 0xffff00000000],hint 5 0xccf29c5711c26bca929da6a8477dc16cd945bd5c314c12a4a526c7814803 0xc6a9903da052b2a114c214b8214a4233506323c6382c000c54d5364c44121486e3⟩,
  ⟨22,5,[0xa0a000000000, 0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000],hint 5 0x329c6f15c470cc26bdaf2a4a769aa668477dc16cd945a962584c5304a9294a026c781705714803 0x2119c2aaf550887024c842390422684a9d94a7a14a6794000d9cebc310d5581587a5⟩,
  ⟨22,4,[0xaaaa0000aaaa, 0xecec0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000],hint 5 0xca715c4709a929da6a99a11df705b35a8c5304a9294a026c781705714803 0x6ba0d92af2421b60928108de1089612a6a529e252998500033⟩,
  ⟨22,4,[0x4c4c0000cccc, 0xaaaa0000aaaa, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000],hint 5 0xca711c3309abea4a769aa11c16cd945a8c12a4a52809b1ec781705714803 0x7326e896f14a5d532ac63220631da60928108de10896100032⟩,
  ⟨22,5,[0x5f5f00000000, 0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000],hint 5 0xc5714c370cc2eafa929da6a8477dc16cd945a8a9294a026c7b1705714803 0x18a932045410865c339842370422484b6b14a7794a6594000c5aaab2acbc29098661b16c5⟩,
  ⟨22,5,[0xa0a00000a0a0, 0xaaaa0000aaaa, 0xc0c00000c0c0, 0xcccc0000cccc, 0xff000000ff00, 0xffff00000000],hint 5 0xca725c5711c3309abe9da6a8477dc16e1b36516f5a95e4b8c12a4a526c7b1e05c14803 0x836b008ec108a41a377439e19604a8c14a6994000e8b4714846c6f0542e1586f44d1e5⟩,
  ⟨22,6,[0x505000005050, 0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000],hint 6 0xc9714c470dc330bc26c2af2b9adeafa929da729aa668ea11df705b86516f5b96c5ad6a5a5675995b54533304a52809b1ec781705714803 0x176d7a155686e05d55e45459db1675554db6e75d7868a245d79e89c16019951266250550415c16a80da5d9068041481527094910067046546a9826a569198186a0675721da1c1971a49079279c6306ac10067c018106b7df45862255589860f5558d75e1a288575e3a2890c7a29de39f7ca04135f7cb0419245a2186⟩,
  ⟨22,5,[0xaaaa0000aaaa, 0xcccc0000cccc, 0xdcdc0000dcdc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000],hint 5 0x332ca725c731bc470dc32afa929da69df705b3651304a0c12a4a52809b1ec52 0x16982dc1bb8a55c589625725c9d1745e9c3d085d5cf7440011a62111a210d42b08543884f⟩,
  ⟨22,5,[0x8c8c00008c8c, 0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000],hint 5 0x332c731bc470dc32bdaf2b9abea4a769aa664a705b8651684c0fb304a52809b1ec52 0x1698ac214b5765d609d40e75e58c85445b884470843a8b02141099266ba2cd57bc0012858⟩,
  ⟨22,4,[0x737300000000, 0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00],hint 5 0x30cc26afa929da6a84705b36516a524a9294a026c7b1705714803 0x421b408dc10894129de529985000315b64d241705866149565⟩,
  ⟨22,5,[0x505000000000, 0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000],hint 5 0xca71cc6f15c470cc26bdaf2afa929da6a8477dc16cd945a8c12a4a52809b1ec781705714803 0x1cca3a45ec92976024b842380422584cac98c8898c7698000cdecabaced4b81e0766⟩,
  ⟨22,5,[0xaaaa0000aaaa, 0xafaf00000000, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000],hint 5 0xccb14c370cc2ea4a769aa11df705b36516a2a4a52809b1705714803 0x16c9adf293ce75c831a842368422405299ae6b93e4f8862125284219c4215440003025284⟩
]

def nodeBlock27 : Array Node := #[
  ⟨22,5,[0x303000003030, 0x505000005050, 0xaaaa0000aaaa, 0xcccc0000cccc, 0xff000000ff00, 0xffff00000000],hint 5 0xca725c5711c3309c1aafa769aa124a77dc16cd945b56a3ecc12a4a526c7b1e05c14803 0x7328e08ec108a212a30529a450003a9b37339dd9806616948463eee5b941a96e5bcd33⟩,
  ⟨22,4,[0x505000005050, 0xaaaa0000aaaa, 0xcccc0000cccc, 0xff300000ff30, 0xffff00000000],hint 5 0xca711c3309a769a705b36516a4c0c12a4a526c7b1e05c14803 0x1a45b42380422504a8914a6714000a5eb9bce76c52148585⟩,
  ⟨22,5,[0x505000005050, 0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f000000000, 0xff000000ff00, 0xffff00000000],hint 5 0x329c7311c370cc2706ae6a4a769aa6684929c16cd70304a92949b2007b1e05c14803 0x615ec212cc53023a842270436c84c9c18c7818d4b18000ca2fd450865e369c5a188566⟩,
  ⟨22,4,[0x505000005050, 0xaaaa0000aaaa, 0xcccc0000cccc, 0xfff00000ff00, 0xffff00000000],hint 5 0x329c470cc26a4a769aa6284929c16ccc12a4a526c7b1e05c14803 0x1446a82388422604a8994a6714000c1eda3ce75496178525⟩,
  ⟨22,6,[0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffaa0000ffaa, 0xffff00000000],hint 6 0xdb736ca728c971cc570dc330bc26c2af6bcae6b7ac6afa929da729aa668ea124677dc1651755c96f5a89b2007b1e05c15c52 0x172cb64d3592cb5cd35744580b2e045668b2db68c8193142d47d111f2e551152172151851471485885f69f5205149d47e07c034078b0de35d00b0222a201b0006c08898806804200906cf02000050021f04850701f0132d38cd3632e44cd4da6864d919a8204db4da6924df4e651499f7d35138c001354e4c0023555⟩,
  ⟨22,5,[0xaaaa0000aaaa, 0xcc880000cc88, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000],hint 5 0x334ca728c731bc370caf6b9abe9da729a77dc16517352d4926c801ec52 0x4769d81ab20c640a749e71b4d90640c771d087c590640005928b92d4a5b20b92d7218d72⟩,
  ⟨22,4,[0x337700000000, 0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00],hint 5 0xc470cc26afa929da6a84705b36516a524a9294a026c7b1705714803 0x421b408dc10894129de529985000315b64d2417058661496a5⟩,
  ⟨22,5,[0x332200003322, 0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000],hint 5 0xca725c731bc470dc32afa769a77dc16cd9452d30304a9294a026c7b14803 0x18a831e2bbcc66452a6a908655f17c46798c6570c6458c001d54d5364c9322f8bc21a0ec3⟩,
  ⟨22,6,[0xaa000000aa, 0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000],hint 6 0x39dcdb29ca325c370cc2f09b0abdaf2b9adeb1a929da7299a3a4677dc16517b5dd6f5a8a92949b1ec7815c52 0xc40c88b2e241030b3122d27100dc2e049049c30649519230c7177003406cb09b35a00b0003003d83cf30f01700048021c04848701c0112d178d35e2df44d4575c545845730c45c46149285c7114917800114ce44001e4d350b2d634d58b2d434d5d875630c55c71949265c7154922800183cf2400183cf5d7116444⟩,
  ⟨22,5,[0xaaaa0000aaaa, 0xcccc0000cccc, 0xccee0000ccee, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000],hint 5 0xca725c6f11c370cc26c2af69da6a99a39c16cd945e56a304a9294a026c7b1e05c15c52 0x1cc83a44dc90875990641d375e5492c03a800270001501e02a70529e25299a5c94ba0141a⟩,
  ⟨22,4,[0xaaaa0000aaaa, 0xc0e00000c0e0, 0xcccc0000cccc, 0xff000000ff00, 0xffff00000000],hint 5 0xca725c470cc269da6a99a11c16cd945a8c12a4a52809b1ec781705714803 0x7320e0926108de1916f24a5d41056132aa6322260003631da6⟩,
  ⟨22,5,[0xaaaa0000aaaa, 0xcc440000cc44, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000],hint 5 0xca728c6f0dc3309abe9da728ea11df705945a9492a4a526c7b1e05714803 0x16a8ae04bc0e75cc2390434684224858a629745d21384dc17a2cf319eb7c26f00035abca5⟩
]

def nodeBlock28 : Array Node := #[
  ⟨22,6,[0xaaaa00000000, 0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000],hint 6 0x332ca714c470dc330bb0abcae6b1a929da729aa3a8477dc16e1b36518761583605805f56f5a9605594846d0e2a4a52809b1705714803 0x1881899966686661961e65e9619656697947a56077a61de61896694164192192466a0530416016e60db61a0660417813a508e78d06504448485966186712611d6067667046041251177855e55847842c10047c01010497df8525616558a69a06188269a261846596379e8e594c79e42490a0413e4908041861a21104⟩,
  ⟨22,5,[0xaaaa0000aaaa, 0xcccc0000cccc, 0xeeee0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000],hint 5 0xcbb29c6f11c370cc2f09b0abdaf2b9a769a77dc16cd945f940304a9294a026c52 0x14baa9b4c3484551085995053db169d739495554db46cc00096c108d8108921b842e98439⟩,
  ⟨22,4,[0xaaaa0000aaaa, 0xcccc0000cccc, 0xe0e00000c0c0, 0xff000000ff00, 0xffff00000000],hint 5 0x329c9711c3309a769aa668477dc16ccc12a4a52809b1ec781705714803 0x635ec896d14a5930924108dc108a2132a863220631d6600035⟩,
  ⟨22,5,[0x44440000cccc, 0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000],hint 5 0x329c6f14c470dc330bc16afa769a77dc16cd94524a9294a026c7b1e052 0x148729a2b34c65442182152541b16c06798c6560c6448de31d5685a152549b16c4001d474⟩,
  ⟨22,5,[0x50500000f0f0, 0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000],hint 5 0xc470dc3309a929da6a99a11df705b86516f304a526c7b1e05c14803 0x16c72c849b9745cc239042268428404a7a94a6794aa514000c58e4a5745d2104050151545⟩,
  ⟨22,5,[0x555500000000, 0xaaaa00000000, 0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00],hint 5 0xccb29c470cc26b9abea4a769aa11df705b3651845a94b314c12a4a52809b1ec781705714803 0x1298e82398422684c8a18c7818000d9f1bc4b57d481c8546945d15d795607a1d9b0f⟩,
  ⟨22,4,[0xaaaa00000000, 0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff550000ff00],hint 5 0xc3309abea4a769aa11c16cd945a8c12a4a52809b1ec781705714803 0x1297542378422584c8818c7698000c98e9b8b164481a0546⟩,
  ⟨22,5,[0xaaaa00000000, 0xaaaa0000aaaa, 0xcccc00000000, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00],hint 5 0xca714c470cc2f09abea4a769aa11df705b3651865a940314a9294a026c7b1705714803 0x421f808e210896183d8f4cf73b84a7914a6714000d0b0c95afabc936cda1b05b053745⟩,
  ⟨22,4,[0xaaaa00000000, 0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xffcc0000ff00],hint 5 0xc3309abea4a829da6a97a11c16cd945a8a9294a026c7b1705714803 0x1086542368422484a7794a6594000c94c9b090541c1a0625⟩,
  ⟨22,5,[0xaaaa00000000, 0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f000000000, 0xf0f00000f0f0, 0xff000000ff00],hint 5 0xccb0dc3309b0ab0a929da6a99a11df705b3651896216a52cc12a4a52809b200781705714803 0x4a63c945d1dd823984226042be84c8a98c7818d2698000dcb1a4696c59efcc881d0546⟩,
  ⟨22,4,[0xaaaa00000000, 0xcccc0000cccc, 0xf0f00000f0f0, 0xfafa0000aaaa, 0xff000000ff00],hint 5 0xc3309abea4a769aa11c16cd945a8c12a4a52809b1ec781705714803 0xc881929754e669823784000c8225858e9b9462c59120681⟩,
  ⟨22,4,[0xaaaa00000000, 0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xfff00000ff00],hint 5 0xc3709abea4a769aa6284705b36516a304a9294a026c781705714803 0x1086d42370422504a7814a6614000c96d9b5f19c481a0525⟩
]

def nodeBlock29 : Array Node := #[
  ⟨22,6,[0x555500000000, 0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000],hint 6 0x31cc5714c370cc2f09b0abcae6b1abea4a769ca6a99a3a8477dc16e1b3651926418e6358c62d835bd6a5a55754d41470c12a4a52809b1ec781705714803 0x1c81cb5966d825719723663b2016c6598e08ec7098ed26371cb2db01601ad912b9ea0590417017ed0df71e06d0418c146c0918d006c0679ca9d96464861ad1a27088ad8467061ac19b8c76ec6868c638100690018104b9249d2767659a26a2671c9975a871c56fbe98e3a6fbcf8e3530c0c0414f0c0d0419e7ba7186⟩,
  ⟨22,5,[0xaaaa0000aaaa, 0xcccc0000cccc, 0xdddd0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000],hint 5 0x332ca71cc6f11c370cc16b9abe9da69df705b3650c12a4a52809b1ec52 0x1276a581ab0a54c14751d314c59064147b59314d1906400011a421116210d027085378854⟩,
  ⟨22,5,[0x88880000cccc, 0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000],hint 5 0x31cc6f14c370cabe9da69df705b36514b440c12a4a52809b1ec52 0x1697adc14b8a55c109a25715d1d074046488446884350a6214ce9625715c5d07400014853⟩,
  ⟨22,5,[0xa0a00000f0f0, 0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000],hint 5 0x315c470dc26afa929da6a99a11df705b86516f314c12949b1e05c14803 0x16992d274b9745d823984226842840486a90857908a510000c52e4b1745d2104050151144⟩,
  ⟨22,5,[0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff550000ff00, 0xffff00000000],hint 6 0x39dc4f12c370cc2f09c22afa929da729aa668ea11c16e1b36518f6116f5a8c12a4a52809b1ec781705714803 0x49549f3cf7d56923d260f61e54578f8585587922587c961249e7de04e05d3c47627013c10520547c35124c17c105804c7823182c178118f19b88a6cf80634619f1974885df58648619e19160745e4066066c100664018105b659⟩,
  ⟨22,4,[0x333300000000, 0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff550000ff00],hint 5 0x30cc26afa929da6a84705b36516a524a9294a026c7b1705714803 0x1086d02370422504a7794a6614000c56d934905c26149565⟩,
  ⟨22,5,[0x555500000000, 0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff550000ff00, 0xffff00000000],hint 5 0x361c7315c3309c22afa929da6a84705b3651845a8c12a4a52809b1ec781705714803 0xf6d1f22b6494bee1258211c02112c2a698c8898c7718000cd8dd3f12c4b21c86a6⟩,
  ⟨22,5,[0x333300000000, 0x555500000000, 0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00],hint 5 0xca711c3309abea4a769aa11df705b36518f5a94b52510314a9294a026c7b1705714803 0x4223908e61089a129e8529a0500036945d14d77560641d15f1bc4957d701595e57c94f⟩,
  ⟨22,6,[0xaaaa0000aaaa, 0xc0c00000c0c0, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000],hint 6 0x31bc5311c370cc2f09b0abcae6b7abe9da729aa668ea11df705b86799d6699865d956516f5a9645454e474fa304a526c7b1e05c14803 0x176d79cf3e76df5cf5e33c499b1263cf55b6e65d78279e35d79a798160194f0e562404f0415c16a709a5d90670414818e69a38cd5186213cf8586133cf8975e09e78175e29e78d27a199e8e33a104114f169607a4fa0560516715d5c67677055c51661568d65a6585305a8100528014106a26a14b156456590585205⟩,
  ⟨22,5,[0xaaaa0000aaaa, 0xcccc0000cccc, 0xeaea0000eaea, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000],hint 5 0x30dc3309b0abdaf2b9abeaaa929da668477dc16e1b3659945a92e26c7b1e05c15c52 0x1889b08443d9a665144259665610c9803c0002700013822005d6d42d6cd2f2b528a502c12⟩,
  ⟨22,4,[0xaaaa0000aaaa, 0xcccc0000cccc, 0xeaea00000000, 0xf0f00000f0f0, 0xff000000ff00],hint 5 0xc3309abea4a769aa11c16cd945a8c12a4a52809b1ec781705714803 0x4a5d563a6e2c59108de108961092813220631da63298600032⟩,
  ⟨22,5,[0x2a2a00002a2a, 0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000],hint 5 0x329c370cc26afa929da124a77dc16e1945bd6a4a0a92809b1ec7817052 0x18a93203b40c665002980017800e4016d52d6caaca55c0070454d536acab290a401102484⟩
]

def nodeBlock30 : Array Node := #[
  ⟨22,5,[0x303000003030, 0xaaaa0000aaaa, 0xc0c00000c0c0, 0xcccc0000cccc, 0xff000000ff00, 0xffff00000000],hint 5 0x329c6f15c470cc2706ae6afa769aa11df705b3665945a8c12a4a52809b1ec781705714803 0x1eca3c24b84238866ce4d297e84132b26322460003b31dc629590c3daf586b3b1b06⟩,
  ⟨22,4,[0xaaaa0000aaaa, 0xc0c00000c0c0, 0xcccc0000cccc, 0xff300000ff30, 0xffff00000000],hint 5 0xca71bc470cc269da69c16cd945a8c12a4a52809b1ec781705714803 0x1c563824884235860cac1297484132a66321e60003431da6⟩,
  ⟨22,5,[0xaaaa0000aaaa, 0xc0c000000000, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000],hint 5 0x329c7315c470cc26bdaf2afa929da6a8477dc16cd9c66d945a8c12a4a52809b1ec781705714803 0x20cb4285f512986824c8423904225862cbc310e53a132b663226631de600035339a6⟩,
  ⟨22,4,[0xcccc0000cccc, 0xeaea0000aaaa, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000],hint 5 0xca711c3309abea4a769aa11c16cd945a8c12a4a52809b1ec781705714803 0x7326e896f14a5d532ac63220631da60928108de10896100032⟩,
  ⟨22,4,[0x2a2a0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000],hint 5 0xca711c3309abea4a769aa11c16cd945a8c12a4a52809b1ec781705714803 0x7326e896f14a5d50928108de10896132ac63220631da600032⟩,
  ⟨22,5,[0x3f3f00000000, 0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000],hint 5 0x314c370cc2ea4a769aa11df705b36516a2a4a52809b1705714803 0x16c9adf293ce75c831884236842240494a108671085510000c1299ae6b93e4f88621a1284⟩,
  ⟨22,5,[0xaaaa0000aaaa, 0xc0c00000c0c0, 0xcccc0000cccc, 0xf0f000000000, 0xff000000ff00, 0xffff00000000],hint 5 0xca71bc470dc3309c1ab9a769aa6684705b36819f304a9294a026c801ec781705714803 0x79a2f296ef6bc24b04238043760671dcd4a7e277a4c413af273a6473d6e70003a3a1c7⟩,
  ⟨22,4,[0xaaaa0000aaaa, 0xc0c00000c0c0, 0xfcfc0000cccc, 0xff000000ff00, 0xffff00000000],hint 5 0x329c9715c4709a769aa668477dc16ccc5304a9294a026c781705714803 0x18d7b024904237062ab4508650412a66529e050003529965⟩,
  ⟨22,4,[0xaaaa0000aaaa, 0xc0c00000c0c0, 0xcccc0000cccc, 0xfff00000ff00, 0xffff00000000],hint 5 0xca71bc470cc269da6a98a11c16ccc12a4a52809b1ec781705714803 0x18573024884236860eac1296484132a66321e60003431d66⟩,
  ⟨22,6,[0x303000003030, 0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000],hint 6 0x329c6f15c5311c370cc2f09b0abcae6b7abe9da729aa668ea11df705b86cda7699a5691a3689986516f5b14f51933478c5304a9294a026c781705714803 0x1b7dbad146b7e36d16e2462b9f2ae47089f8ae6c88ab2226dbbabb81701a511297280510416c17ab0de6dd06b0679c29e288148115116d709b51b0570516b1616c786b8056c514f15a8866a7645885bc100538014106f2ef61146571c95145771c9a49a46db9165666db9d2aa58a29e742504152fbcc1454efbcd145⟩,
  ⟨22,5,[0xaaaa0000aaaa, 0xbaba0000baba, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000],hint 5 0xccf29c6f0dc3309b0aafa929da11df705945a9494a0a926c7b1e05c15c52 0x16a82dc4b38c65cc0390002680014814c5328ba2e6e9b81103d08532abbae6e9b807054a5⟩,
  ⟨22,5,[0x8a8a00008a8a, 0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000],hint 5 0xccf29c6f15c370cc2706abea4a7699a11df705945bd493ecc52a49b1e05c15c52 0x16a8ade6c3ca55d803980026800178108532ebcae4fbbc10041ca72aabaacefa3c0904084⟩
]

def nodeBlock31 : Array Node := #[
  ⟨22,5,[0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff300000ff30, 0xffff00000000],hint 6 0x396ca71bc5714c470dc2f09a769ca6a99a628ea11df705b86cd99651745b530304a9294a026c781705714803 0x44d45c49270d35149164d65f5957cd8595997d121970865145f71f05205b3446d26813410510547035114c170105904a88229930138114d15e48978d74548515c15844761c5c544514b1506464223c564580100528014106028a⟩,
  ⟨22,5,[0x303000003030, 0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff300000ff30, 0xffff00000000],hint 5 0xca71bc5711c26bca769aa11df705b3665944c0c5304a9294a026c781705714803 0xf831f35666843ee1254211c422984a9b14a7914a6714000e1906428f6cd61c1705⟩,
  ⟨22,5,[0x303000000000, 0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000],hint 5 0xca71cc6f15c470cc26bdaf2a4a769aa668477dc16cd945a8c5304a9294a026c781705714803 0x1cf8ba6aecd0876824b842380422584a9c94a7914a6694000d18cabacec4f81d9765⟩,
  ⟨22,5,[0xaaaa0000aaaa, 0xcccc0000cccc, 0xcfcf00000000, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000],hint 5 0x332c5714c370cc2eafa929da6a8477dc16cd945a8a9294a026c7b1705714803 0x18a932045410865daaab2acbc2900cf0108dc1089210ce612dac529de5299652dac500031⟩,
  ⟨22,6,[0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffcc0000ffcc, 0xffff00000000],hint 6 0x37dcdf32ca71bc5311c370cb0abdaf2b9adeb1aa6a4a769ca6a99a3a8492a4677dc16e1b36ada9650c12a4a52809b1ec52 0x1834d6871da34d6071cc48c9871e649230731c6df31a3151d579205e1e355255e75e55955575579979e30555915530c79b7913519471e536444745b6c045a01b30c45c45b6d045545678f5955d17910870a134684780234288988270209c0a222209b09430451c4c230209e08b5432de2825428913825820910a2596⟩,
  ⟨22,5,[0xaa880000aa88, 0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000],hint 5 0xccf32ca71bc370cc1ac2af6a9a929da668ea124a77dc16a994525302a49b1ec52 0x1066a1c1bb86345186c308c5ad8a830a5326c8ca26ea398f63da669aa88a0ee9380063c42⟩,
  ⟨22,4,[0x507000005070, 0xaaaa0000aaaa, 0xcccc0000cccc, 0xff000000ff00, 0xffff00000000],hint 5 0x329c470cc26a4a769aa6684929c16cd945a8c12a4a526c7b1e05c14803 0x629ec08e61089c12a2a529a0500032892d139d946852189565⟩,
  ⟨22,5,[0x554400005544, 0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000],hint 5 0x329c6f0dc3309c1aafa929da11df705945a9492a49b1ec781705714803 0x16a82dc5b38e75cc24904236842248508532aba2e2e9b8000bd8a629745d1d374de1784c6⟩,
  ⟨22,6,[0xcc000000cc, 0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000],hint 6 0x396cdf32ca71bc5714c470dc32c2af6bcae6b7ac6afaa6a4a769ca668e92a4677dc16e1b36bdad650c12809b2007b17052 0x174437871de4566871d31d375109d1e34d14dd69d4de4d399375e7503509471e536440741a68141b41a79e41341474f5135507501071203468077c434411e1126d249e48468411d10b4c52dd2844c48903845041101225145cd3591c764d3571c769b31978c62185c4d37218584d369a01940024411b49220411b492⟩,
  ⟨22,5,[0xaaaa0000aaaa, 0xaaee0000aaee, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000],hint 5 0x329c470dc3309af6b9abea4a769ca11c16cdae6516a304a52809b2007b1e05c15c52 0xab9ae24d46f18dc03b000278001501745b31573af1bc412048c9c98c8c18c76980604a06⟩,
  ⟨22,4,[0xaaaa0000aaaa, 0xaaee00000000, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00],hint 5 0x311c3309abea4a769aa11c16cd945a8c12a4a52809b1ec781705714803 0x4a5d508de10896163a6e2c591206813220631da60003232ac6⟩,
  ⟨22,5,[0xaa220000aa22, 0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000],hint 5 0xccb29c7311c370cabea9a929da729aa3a4a77dc16cd94304a92809b1ec5c14803 0x1489aa03c40c6551a8cb4426ddac93487b108a71085490002450b42eaaaaa90a41b1085e4⟩
]

def nodeBlock32 : Array Node := #[
  ⟨22,6,[0xaaaa0000aaaa, 0xcccc00000000, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000],hint 6 0x31bc5714c370cc2f09b0abcae6b1abea4a769ca6a99a3a8477dc16e5b86ddb56d1b36c9b1669946156f5a953438a9294a026c7b1705714803 0x18718a4e3a972160e61f39fa1c12838e7dc7e86087e921f618a29a015c18ce3a38e605805ba436d8681a4105f04ca0231f2c1a018d766338e9229226188955246184ebae57df96bacf7df8e39e304114e16a8eaa8ea8534516915e6077a97456051681567c65a84857c5b0100580014106c82014a16a46aa90a85245⟩,
  ⟨22,5,[0xaaaa0000aaaa, 0xcccc0000cccc, 0xeeee0000aaaa, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000],hint 5 0xcb314c470dc3309abea4a768477dc16516a500a926c7b1e05c15c52 0x1497a9a44b4c65452b49e4a92a2d8b4038000260001401c0039349ce8aaaa8d8b4a50380e⟩,
  ⟨22,5,[0x22220000aaaa, 0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000],hint 5 0x32cca714c370cc26afa929da11df705945a8c12a49b1ec5c15c52 0x128725839b0a54c0087800258001380c692a49a264c8300d0350a42a298a60c8300d03484⟩,
  ⟨22,5,[0x30300000f0f0, 0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000],hint 5 0x315c470dc26afa929da6a99a11df705b86516f314c12949b1e05c14803 0x16992d274b9745d823984226842840486a90857908a510000c52e4b1745d2104050151144⟩,
  ⟨22,5,[0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xffcc0000ff00, 0xffff00000000],hint 6 0xdf734c6f14c4f12c370cc26afa92a0a769ca6a99a5e8ea11c16e1b66cd946196f5a8a9294a026c7b1705714803 0x41441d30c7546903105cc5dc50470c7d75177102177485d041c75c04e0623138a36c130105005274349044174105704a70229724170114c1608d880c7852c515d15640759d54540515c14f5c63dc3455c5841005640141061659⟩,
  ⟨22,4,[0x333300000000, 0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xffcc0000ff00],hint 5 0x30cc26afa929da6a84705b36516a524a9294a026c7b1705714803 0x1086d02370422504a7794a6614000c56d934905c26149565⟩,
  ⟨22,5,[0xaaaa0000aaaa, 0xcccc00000000, 0xcccc0000cccc, 0xf0f00000f0f0, 0xffcc0000ff00, 0xffff00000000],hint 5 0x3b7cd315c530cc26afa929da6a84705b66cd945a8a9294a026c7b1705714803 0xd549b022a084368154c23704224858ac36d0b42e12d6a529de529965000312d6a5⟩,
  ⟨22,5,[0x333300000000, 0xaaaa0000aaaa, 0xcccc00000000, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00],hint 5 0x329c470cc26b9abea4a769aa11df705b66cd945a949314c12a4a52809b1ec781705714803 0x1298e823984226865184575e54813228631de60003632b66746f12d5d5c870e619c6⟩,
  ⟨22,6,[0x333300000000, 0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000],hint 6 0x329c6f14c470dc330bb0abcae6b1a929da729aa3a8477dc1701bf6f1bb6e5b86cda6651925bd6a52141304a9294a026c781705714803 0x1881899966686661961e65e96196566a7977a56087a621e6189669618448596414c105805b9836d868198105e04d94235e30194114e168649a219c564516615d6077667056051651527864a5445785a410057c01410697df8533e164f8a69a06188269a26185a596379e8e595079e861921041569a4a145529a4b145⟩,
  ⟨22,5,[0xaaaa0000aaaa, 0xbbbb0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000],hint 5 0xccf29c6f0dc3309c1aafa929da11df705945a8a926c7b1e05c15c52 0x12872584a30c64c40380002580013810a42a499262c8b00d0351342a69aa5ec8b00d034a5⟩,
  ⟨22,5,[0x88880000aaaa, 0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000],hint 5 0xccf32ca71bc370cc1ac2af6bca929da11df705be6516a525102a49b1e05c15c52 0x16caadd4bb8a55d003c000268001400e7b32cbcae6ea380f03ccc4a60b8ad4e9380f03c84⟩,
  ⟨22,4,[0x707000005050, 0xaaaa0000aaaa, 0xcccc0000cccc, 0xff000000ff00, 0xffff00000000],hint 5 0xca711c3309a929da6a99a124a77dc16ccc12a4a526c7b1e05c14803 0x52dca08e41089a12a285299e500031812b039d536060181525⟩
]

def nodeBlock33 : Array Node := #[
  ⟨22,5,[0xaaaa0000aaaa, 0xc0c00000f0f0, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000],hint 5 0xc470dc3309a929da6a99a11df705b86516f304a526c7b1e05c14803 0x16c72c849b9745cc2390422684284058e4a5745d2104050129ea5299e52a945000312a945⟩,
  ⟨22,5,[0x333300000000, 0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f000000000, 0xf0f00000f0f0, 0xff000000ff00],hint 5 0x31bc370cc26c2ac2a4a769aa668477dc2705b36516a52ca9294a026c801705714803 0x421b97b5cdc4c238042250429784a7914a6614bad14000d08d8b633acd6bb3ee1d1745⟩,
  ⟨22,4,[0x333300000000, 0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xfff00000ff00],hint 5 0x30dc26afa9aa4a769aa6284705b36516a2a4a52809b1705714803 0xe75d023604224048671085510000c12b92daf93e6189244⟩,
  ⟨22,6,[0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f000000000, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000],hint 6 0xd9329c731bc5311c370cc2f09b0abcae6b1a929da729aa668ea11cb725c8719c5711c1701b86cda66799a651875bd6e5a969580c12a4a52809b200781705714803 0x18858b6716d861633624a649e18679f2cd8264b49918633b6d9e9467851a26a2661899e7686189e7b2792405706b844ae7a81841058060b438187c1b4106404fa423e43414c1054071731c5bc414811a11af9cabe1b864061ad1a36088ed88660618e1969075a954690618c1b06b0c19c062c6c01006940181070965⟩,
  ⟨22,5,[0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xfafa0000aaaa, 0xff000000ff00, 0xffff00000000],hint 5 0x333ca71bc370cc26c2abea4a768477dc1651885a8a926c7b1e05c15c52 0x1497a92b4c26a9a9a4ab4c6549b29340388002601c003801381344a28ab28a59364d0380e⟩,
  ⟨22,5,[0xa0a0000aaaa, 0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000],hint 5 0x333ca71bc570dc3309c1ab9a929da668477dc16516a524c52a49b1e05c15c52 0x14b6a9c6bb8a5554039000260001400e7b2ecac2a2eb380f03dab4a68aa2a0e9b80f03c84⟩,
  ⟨22,5,[0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xfcfc0000cccc, 0xff000000ff00, 0xffff00000000],hint 5 0x332ca725c731bc5711c370cae69da6a9977dc16cd9f650c5304a9294a026c52 0x14b628e75b151545c6bb88454e0e73d75c615155400755c80964108da1b043608921a0434⟩,
  ⟨22,5,[0xc0c0000cccc, 0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000],hint 5 0xca71cc6f11c370cb0aafa769a77dc16cd9452cc12a4a52809b1ec52 0x148729a1ab4a5540e8a2151551b06c046908446084348a6214de85a151545b06c00014c53⟩,
  ⟨22,5,[0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xfff00000ff00, 0xffff00000000],hint 6 0xe1382d932dca71bc5311c370bc26afa929da729aa6698a3a84709c16e1b368194625705bd6a304a9294a026c781705714803 0x49c49f98e7dc7129d269c6a45d691c8da5da95221a7c86924a67df05305e7047a67417010520557c35525017c105a04b9c22da2813c115c16198985c80534515f15948765f60548514c1516864674056858810056c01410626db⟩,
  ⟨22,5,[0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f000000000, 0xf0f00000f0f0, 0xfff00000ff00, 0xffff00000000],hint 5 0xee72dca71cc6f11c3709abea4a769aa6684705b35a8c12a4a52809b200781705714803 0xd2bdb17e5296d673db7510928108dc1089610e30132ac63220631d8635ee600032⟩,
  ⟨23,6,[0xaaaa0000aaaa0000, 0xcccc0000cccc0000, 0xf0f00000f0f00000, 0xff000000ff000000, 0xffff000000000000],hint 6 0xd2347d0f42d0740cf33bceb03c06ffbf2fbbdaf2bc6efb9ee2b86dfb6edab66d8b5ebeaeab8acdd5751d17381f06817 0x20d20d2225d722225f20d5cd20c5cc22124f2215de20c20c28c58c28a34d28a59528c34c20b5cb22024e2205dd20b20b28b44b29934d29945128b34b1cb94b1dc30c1dc95b1cb30b2102102245d22242632105d029035029844229835a2904501d03101d39411d33141d09501932c01506401102cb0d3653⟩,
  ⟨23,5,[0x8888000088880000, 0xaaaa0000aaaa0000, 0xcccc0000cccc0000, 0xf0f00000f0f00000, 0xff000000ff000000, 0xffff000000000000],hint 5 0x350d2b3ccef01bfefcbeef6bc6f0baae9b9ee1b7edbb66d8b5ebeaeab8acdd073c2107c1a 0x2e9a5a9995297355a3cb096e5d95853e1b7bc377800aabed2350f442c8b2a86a4a5ad⟩
]

def nodeBlock34 : Array Node := #[
  ⟨23,4,[0xaaaa0000aaaa0000, 0xcccc0000cccc0000, 0xf8f80000f8f80000, 0xff000000ff000000, 0xffff000000000000],hint 5 0x350d2b3ccef01bfefcbeef6bd6f1bbeeab9ee6b86dfb6ed9b62d70841f 0x23a84196631918382ad0090e410a435b6ab5822b3196f42169⟩,
  ⟨23,4,[0xaaaa0000aaaa0000, 0xcccc0000cccc0000, 0xf0f00000f0f00000, 0xff880000ff880000, 0xffff000000000000],hint 5 0xd434acf33bc06ffbf2fbbe6f6bc6f0baae9b9ee1b7edbb66d8b5c1a 0x1b2631124210d627a6af084c378a223a287296070004e6b547⟩,
  ⟨23,5,[0xaaaa0000aaaa0000, 0xcccc0000cccc0000, 0xeeee0000eeee0000, 0xf0f00000f0f00000, 0xff000000ff000000, 0xffff000000000000],hint 5 0xd2343cf33bceafcbdaf1bc2efb9ee2b86e0b7edbb6ad9b62d7afabaae2b374dd2 0x227741d5639d123cc931a02829c07119353190d318f9350cb7616b6a16b6416f59971⟩,
  ⟨23,4,[0xe0e00000e0e0000, 0xaaaa0000aaaa0000, 0xcccc0000cccc0000, 0xff000000ff000000, 0xffff000000000000],hint 5 0xd0f3ccef3abf2fabdaf1bbee2b86dfb6edab66d8b5c1a 0x1ae03091c108ce13222631d860982013ca2128620b422324c0⟩,
  ⟨23,4,[0xee000000ee0000, 0xaaaa0000aaaa0000, 0xcccc0000cccc0000, 0xf0f00000f0f00000, 0xffff000000000000],hint 5 0xd0f3ccef3abdaf1bc2efba2e7b8ae0b7edbb6ad9b62d70841f 0x19a231160210d623a6673a18711c4d249e41b864104443a8e0⟩,
  ⟨23,5,[0x2222000022220000, 0xaaaa0000aaaa0000, 0xcccc0000cccc0000, 0xf0f00000f0f00000, 0xff000000ff000000, 0xffff000000000000],hint 5 0xd4348d0f3ccef01bf2f6bc6efbaae7b8ae1b82dfb6ed9b62d7aeab808417 0x1a14314f3294cf2c5b7884ca344b22a175421464212e4011114070328ca2d8b621188⟩,
  ⟨23,5,[0x4444000044440000, 0xaaaa0000aaaa0000, 0xcccc0000cccc0000, 0xf0f00000f0f00000, 0xff000000ff000000, 0xffff000000000000],hint 5 0xd2b48cf33bceaffbf2fbbdaf1ba6e7b86dfb6edab66d8b5ebaae01f06817 0x1df539934318ee31513294eb294d62b1b76305260426800ac791e359d67b1ac68954a⟩,
  ⟨24,6,[0xaa00aa00aa00aa, 0xcc00cc00cc00cc, 0xf000f000f000f0, 0xff000000ff0000, 0xff00ff00000000],hint 6 0xcef1cc5714c470cc2f09bdaf4b9edfb72d8b5ed5b0ebeaf2b1785e077ddb75db86cd946096f5a8c12bca026c7b1e0681945714803 0x5cd84d5d738e5d88605cd38d65c39c6646466643a965c65c5e43445dc6045dc34d5e45e45814c15a33855a34e25813815c15c15db3435db61a5c13416419c164c70264c9cb6417015873875a64ca5a63a55874c75c73475de6095de35d5c75c76477076509c865070f6479c755f040507a0048704145fa1f⟩,
  ⟨24,5,[0x88008800880088, 0xaa00aa00aa00aa, 0xcc00cc00cc00cc, 0xf000f000f000f0, 0xff000000ff0000, 0xff00ff00000000],hint 5 0x34cd2b3bc731bc570cc1ef4bc2e7b62c8b0ebeaf2b177dd9761946094b5253826c7b1a052 0x1d143c45a88427b190b464fc3d6378c8bb91087c4211bcb335218869dc74c5f100063⟩,
  ⟨24,4,[0x70007000700070, 0xaa00aa00aa00aa, 0xcc00cc00cc00cc, 0xff000000ff0000, 0xff00ff00000000],hint 5 0x33bc470cc26f4b9edcb62d5b21b3651825a8c12bc9b1ec781a06514803 0x52e4a09261089c1322a631e0600031796cf18d547852169986⟩,
  ⟨24,4,[0x77007700000000, 0xaa00aa00aa00aa, 0xcc00cc00cc00cc, 0xf000f000f000f0, 0xff000000ff0000],hint 5 0x33bc470cc26f4b9edcb62d56cd946096a524af2809b1ec681945714803 0x2117408dc1089413220631da60003162e4b2becf6066149aa6⟩,
  ⟨24,5,[0xaa00aa00aa00aa, 0xcc00cc00cc00cc, 0xee00ee00ee00ee, 0xf000f000f000f0, 0xff000000ff0000, 0xff00ff00000000],hint 5 0x33bc7311c3309bd2f0b9edcb62d5b0ebeaf2b1779dc6cd946096a304af2809b1ec781a06515c52 0x2d995d4bea8c6bdb20c7ae4b8d6757009a000540002a074064f0c6458c63b4d7300d8⟩
]

def nodeBlock35 : Array Node := #[
  ⟨24,4,[0xaa00aa00aa00aa, 0xcc00cc00cc00cc, 0xe000e000e000e0, 0xff000000ff0000, 0xff00ff00000000],hint 5 0xcef11c3309bd2f0b72d8b55b3651825a8c12bca026c7b1e0681945714803 0x6366c81af0211950968108de1089613aac73a6273a1c700032⟩,
  ⟨24,4,[0xaa00aa00aa00aa, 0xcc00cc00cc00cc, 0xee00ee00000000, 0xf000f000f000f0, 0xff000000ff0000],hint 5 0xcef11c3309bd2e7b72d8b55b3651825a8c12bca026c7b1e0681945714803 0x211956b26c342f008de108961096813a6273a1c73aac700032⟩,
  ⟨24,5,[0x22002200220022, 0xaa00aa00aa00aa, 0xcc00cc00cc00cc, 0xf000f000f000f0, 0xff000000ff0000, 0xff00ff00000000],hint 5 0xd333bc7315c470cc1ef4b9edcb62beaf1df6cd946094b304af2809b1ec6814803 0x25524bc7878849a214c55d394cdf6790f5210d0210ab200975314c4b92d7d9f608624⟩,
  ⟨24,5,[0x44004400440044, 0xaa00aa00aa00aa, 0xcc00cc00cc00cc, 0xf000f000f000f0, 0xff000000ff0000, 0xff00ff00000000],hint 5 0xd2b3bc731bc570cc26f4b9ed8b56c8afabc77d946096a5253826c7b1e0681945714803 0x2d945c8da9108bb04b5084710844a0cd3b9a10bc4212b80336b1ac72debbcaf2c84e7⟩,
  ⟨26,6,[0xa0a0a0a0a0a0a0a, 0xc0c0c0c0c0c0c0c, 0xf000f000f000f00, 0xf0f00000f0f0000, 0xf0f0f0f00000000],hint 6 0xcf331caf14c470dc2f09bf2fbb86dfb72d9b5ed5b12c1afeb3a7e9ca6a99a5a8ea11ea7a5e678cc12bca526c801e06d1945c14803 0x5d15d15e84925e86275d14915dc49c5e46065e44a95dc5dc66444465c64465c4516646645c15c15e34855e36225c148158154159b44359b55a5814416417c16507026507cf6417015c74875e660a5e64a55c75c758744759e54959e45d5875476477076547c86547136477c73a00403478403070412e0860⟩,
  ⟨26,5,[0x808080808080808, 0xa0a0a0a0a0a0a0a, 0xc0c0c0c0c0c0c0c, 0xf000f000f000f00, 0xf0f00000f0f0000, 0xf0f0f0f00000000],hint 5 0xd434fcf32ecaf0dbf2fbb86d9b3ecdb12c1afeb3a7e99a5a6996256795e426c801b452 0x25574c85990429b555ba9d2b4c6539511aa18c95c2129d2b86a9ca2a589249f200063⟩,
  ⟨26,4,[0x700070007000700, 0xa0a0a0a0a0a0a0a, 0xc0c0c0c0c0c0c0c, 0xf0f00000f0f0000, 0xf0f0f0f00000000],hint 5 0x33ccaf11c3709beedcb66d5b369aa6696a10c12bc9b200781b46514803 0x52eaa09241089c13228631e0600031796cf18d537852169986⟩,
  ⟨26,4,[0x707000007070000, 0xa0a0a0a0a0a0a0a, 0xc0c0c0c0c0c0c0c, 0xf000f000f000f00, 0xf0f0f0f00000000],hint 5 0x33ccaf11c3709beedcb66d5a6a99a5a84958c12949b200781b45c14803 0x796cf09241089413228631da6000315b2ab18d73585c149a06⟩,
  ⟨26,5,[0xa0a0a0a0a0a0a0a, 0xc0c0c0c0c0c0c0c, 0xe0e0e0e0e0e0e0e, 0xf000f000f000f00, 0xf0f00000f0f0000, 0xf0f0f0f00000000],hint 5 0x33ccbb2bc470dc26fcbeedcb66d5b12c1afeb3a6a99a5a847a1e7304af2949b200781b46517052 0x35dc6d4bea8c6dd3a4e8b60d5d67550099000540002c060064ecc6458c63bcd7300dd⟩,
  ⟨26,4,[0xa0a0a0a0a0a0a0a, 0xc0c0c0c0c0c0c0c, 0xe000e000e000e00, 0xf0f00000f0f0000, 0xf0f0f0f00000000],hint 5 0xcf32ecaf11c3709b72d9b569aa6696a10c12bca526c801e06d1945c14803 0x636ac81af0211930964108de1089613aa873a6273a1c700036⟩,
  ⟨26,4,[0xa0a0a0a0a0a0a0a, 0xc0c0c0c0c0c0c0c, 0xe0e00000e0e0000, 0xf000f000f000f00, 0xf0f0f0f00000000],hint 5 0xcf32bc9711c3709b72d9b569aa6696a10c12bca526c801e06d1945c14803 0x81af0636cc21193096410896108de13aa873a1c73a62700035⟩,
  ⟨26,5,[0x202020202020202, 0xa0a0a0a0a0a0a0a, 0xc0c0c0c0c0c0c0c, 0xf000f000f000f00, 0xf0f00000f0f0000, 0xf0f0f0f00000000],hint 5 0xd433ccaf11c36fcbeee1b72d9b3ec1afe9fa6a99a5a58304af2949b2006d14803 0x25574c07880849ad159a212c4be12810f6210d1210ab200945394d4b12c84a1208664⟩
]

def nodeBlock36 : Array Node := #[
  ⟨26,5,[0x404040404040404, 0xa0a0a0a0a0a0a0a, 0xc0c0c0c0c0c0c0c, 0xf000f000f000f00, 0xf0f00000f0f0000, 0xf0f0f0f00000000],hint 5 0x34fcf32bc3709bf2fbb86d9b56cdb06bfa7e99a5a849a65626c801e06d1945c14803 0x2d985c8d99108bb84b6084710844a0d13aa210b6c21298034731ec6adab9ca72a84e7⟩,
  ⟨30,9,[0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000],hint 7 0x33ccc72bca714c470dc330bc26f6bbae7b7edcb66d8b5ed5b42ccb2ac7a929fa769ca6a99a5a8ea2e86a12829fa7b9e2749c66d97a4f87dec77dc16e1b3651825bd6a304af2a4a52809b1ec781a0651705714803 0x5841c1059048915905c405840890585131458f089158f134258508945a512945acc8105acd2b75a5081458a48a958ed30758ec8bf58a53295aa48295ac92855ac88105aa52a95cc8a0b5ea598b46a4a145cc99b25804a8158e888658e8ab958048815a055015ac48045ac55305a048015c04a0144919834090a215c059815e054813e3d9023c3d48e5e05901582088858f8a8d58f88bd5820a885a208085ad550c5ad48345a215085c219883aa0a0a38a19a75c20a085e21908364d489344d9125e2148832d808030215802e200812cd95ab⟩,
  ⟨30,8,[0x8888888888888888, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000],hint 7 0xea38ad6357d5753d2b3cccb31caf29c731bc370cbfefebf2fbbdaeeb9ed9b62d4b46d0b3accb2ecab26c8b1ec6aaaa4a7e9da669692a1b8661785a1584e118420f82e08812017f1f87c9ef7b9ed77dc165182525384c0a926c7b1a052 0x8821a8889004898901abf8820488882908a88ec48988ed0c2882848a8a2900a8ac84088ac90348a2840a88884a288e908288e84be88890a28a884228ac50018ac44088a890228cc45048e899043c8850a8cc593188905a488f448988f45c188904a48a911a48adc4088add1b88a904248cf45053a919054c9050a8cf59328edd11f389189f4c911228edd8b188cc4b388f058788f04c388cc5b38af04068acd1868acc4088af11a38ccd93360d850a36d99398ccc50a8ed98a860cd12234cd8b18ed91224ccc6b360312244c64c25889e22789104898910ba9889c4898aaa2aa8b144088b14b2b8aa84088cb0aac60b450a28b49928cb050a8eb88ae60bd12220bc78e8eb91224d24680889d2006120603889d983⟩,
  ⟨30,7,[0x2222222222222222, 0x8888888888888888, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000],hint 6 0xf57c4ef3bbe2b53d2b3cccb31caf29c731bc5311c370cbfefebf2fbbdaeeb9edfb72d9b62d4b4ac8b1eaaa929fa769ca6a99a5a4a77dc16e1b365182525384c0c12bca9294a026c7b1a003 0x32533234dca5c4c34c41442b34dad4d1035041342030c8139103105cd5ea502a8dc175175cc5df4c17cc3174d77d01978065d041f81f65166f34dbd1cd935965866730c9d8a19319bd025980965042f8209d74997d26575e77df0f80ed348b5eb033430f90e230789e8433030de0d640559e5434030de0cf5c43de3835c3ede0036408cd8ee44bb8dd63463b8c2a360a8cc32e6188e08e64109a0a6341099f7235d78df7e65d7e9d6a3659db76e30c3⟩,
  ⟨30,7,[0x4444444444444444, 0x8888888888888888, 0xaaaaaaaaaaaaaaaa, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000],hint 6 0xf57c4efbbdea353d2b3cccb31caf29c731bc370cc2f09bfefebf2fbbdaeeb9ed9b62d7b56d4b22c7b1aaaa929fa7699a5a8ea124a77dc1651825bd6a525384c0a91ec781a0651705714803 0x3a53b23cfca5c4e3ce41642d3cfb56d103d041542238e8959103905cf5ec587b0fc175975ce5e154584e3975578502178885d04218a18cf8ee44bb8fd63463b8e2a360a8ce3ae6188e28e64109a2a634109a17635d78e18665d707806b3c6adea813c107906038481e7c138105e05440351e4c140105e04d5c235e3015c1ede0018c065166f3cfbd1cd93d965866738e9d8a19399bd025988965042f8a29d74998526575e7861e9b6998d9db7719041⟩,
  ⟨30,7,[0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf8f8f8f8f8f8f8f8, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000],hint 6 0xf2b58d2b3cccb31caf29c731bc370cbfefebf2fbbdaefbbaebb9ed9b62d4b46c6b0ec2b02a9a9ea4a7e9da66967c5f077dda71dc16f5b3651916097f5d16a48ca926c7b1a052 0x7099c97322cb7329f17092c974e54e76d2cb76d57474e2ce70e50e72224972252570e24e7d62d67ec5427ec2f07d65567d62567e15017e12497d65167e13847d68847d638e7e18a16c64464ef2ca7af4736c62c67065c67292487295ea70624674638675a88775a399746886da95807c68407c65867e98616cc2cc82e4504ae2f580c44c70c24c7265cf72626470c5cc74c88c76838d7688ab74c38cda88437cc5837cc84c7e85967a318580c60578c186de3618⟩,
  ⟨30,6,[0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf8f8f8f8f8f8f8f8, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000, 0xffffffffaaaaaaaa],hint 5 0x34acf33bcc71cc6efebbad9b62a7a929fa75df705b3651916097f5d16a2a47b1a052 0x312e39dc74dceb9496b4e56b3cd6d8c5ad161ad09da31ae2f211e445884350842c0800122a526ba3b8ee92e4b8b62d23c8f⟩,
  ⟨30,6,[0xcccccccc, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf8f8f8f8f8f8f8f8, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000],hint 5 0x34acf33bcc71cbfeeebaee7b66d8a7e9d77dc7705bd6cd94645825a9492a49b1ec68 0x191732d195acd45b8387380670c6b81ec8799e65c571741d0493494b2694aaa91092e925326a1e6799715c5d0740a54c932⟩,
  ⟨30,7,[0x8888888888888888, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf8f8f8f8f8f8f8f8, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000],hint 6 0xf43cbf2b58d2b3cccb31caf29c731bc370cbfefebf2fbbdaeeb9ed9b62d4b42c8b1ac3b0ac0aaaa4a7e9da6696929f77d9f57d1f377dc16cd946096a525384c0a91ec68 0x78c7b8822e8ed1c81ca4caa482294f028828a48a8071e04a2287294214a1306822c5135141d47d201f1c751251f28252009428a7e07d62d6ac822b2ef5885965569471e55665875ab2835a00d628aae082551159f45651495f7e1221a8b16a23184b86a1c48551211c7a9556182190a2a482784a2a47dc8545217df9145217a179659b797633433208cde3de2086746741c7d1e3991c769e69e28a35e31a28acb57725146de1b258679e272849⟩,
  ⟨30,6,[0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf8f8f8f8f8f8f8f8, 0xff88ff88ff88ff88, 0xffff0000ffff0000, 0xffffffff00000000],hint 6 0x34acf332cc72bca71cc6f0dc32ffbfafcbeef6bbae7b66d8b52c6abaaba9ea4a869fa769aa6696a11df705b3651825a9494e0a91ec68 0x19c1a71c79dc9861c624d2621c788da491c924c25918664c6c91893c73e134184794f34f3c63d830060618f30f60908f6423c92586584ca4e41d590aa131d34d04de1947907d31939091536454c94e465978f2d360b4cf4de6186876a32848c7a9a29a8c60da4036861a341069921d24875981a24975839a3ce69861d3cf6934574915934da492⟩,
  ⟨30,6,[0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf8f8f8f8f8f8f8f8, 0xff00ff00ff00ff00, 0xff88ff88ff88ff88, 0xffff0000ffff0000, 0xffffffff00000000],hint 5 0xd2b32caf29c72febeee7b62a9a9ea4a8e9fa769ca6696a39c16cd946096a525381ec68 0xa6c9566599455156659945515086870d680ad9b5b39b5b391b52916d221257bca314a653a0f74108ae39eb4a56b46326d7be50⟩,
  ⟨30,6,[0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf8f8f8f8f8f8f8f8, 0xff00ff00ff00ff00, 0xffff8888ffff8888, 0xffffffff00000000],hint 6 0x34acf332cc72bca71cc6f0dc32ffbfafcbeef6bceeebb6ebb9ee3b72d9b62d5b52a4a7e9da669677dc16cd946096a4c0a91ec68 0x15a16518695a90518520b22018680b9c818820a21214548a60814830631f2c17c68cc2cc30531128044514c28c44808c4823082114913893a218688998e18e38d11c14470d74e14e8880ce48338822249270c40e45038c31c4515865a1259846a162568451d63475855a134d59259b2176d27962166d14d631359159b30c54f51639458f59538e⟩
]

def nodeBlock37 : Array Node := #[
  ⟨30,6,[0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf8f8f8f8f8f8f8f8, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff88888888],hint 6 0x34acf332cc72bca71cc6f18c470dc3309bfefebf2fbbdaeeb9ed9b62d4b1aaaa929fa7699a59df705b3651825a9384c0a91ec68 0x1971a51c79579061c624c25e1c778c9c91c924b25418650b58918934735d3017478cd30d3463532c04c618d2cd4c908d5023492535133ca1621c588a98f1cf3ce3d918664e68f18f8890cf5033c926251464d70f4dc3cd3594d3547221288847a152958461153845461a138e5545582496146d52496137d535f5534d834d5528123e04524153cf⟩,
  ⟨30,6,[0x7777777700000000, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf8f8f8f8f8f8f8f8, 0xff00ff00ff00ff00, 0xffff0000ffff0000],hint 6 0x34acf332cc72bca71cc6f0dc32ffbfafcbeef6bbeeebaee7b66d8aa6a7a929fa7699a59df71dc16f5b3651825fd745a94948ca926c7b1a052 0x39139928a65170e28e4ca4d844160a29345360e1136444ce3986581d41e02898148472871ce1d76485ce5876478130076001d31e061830a31d50f74a6cc50c31931f38d7d988c38c7d80cc4c331831f4d368714c5453071da5552e92de28a7a9a0b28a2e42d238e4a4acb38e4a308b4d32e39d24d32e62d01c7426a8b1c742518b30c2e5b1030c⟩,
  ⟨30,7,[0x8888888888888888, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xf8f8f8f8f8f8f8f8, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000],hint 6 0x358d2b3cccb2bbfefebf2fbbbae7b66d1b42c7b0ec2b02aaa929fa7699a59fb7e9f9705b8651825bd494e130 0x1057841c58071c464714c14c10b10b1d71d714c14c10b10b1d71d734d3c57cf3c470f0001d76cf3db6cf3db60285804110e60774769861a69861a60f41114a1521091131c81d55225a20c3186⟩,
  ⟨30,6,[0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xf8f8f8f8f8f8f8f8, 0xff88ff88ff88ff88, 0xffff0000ffff0000, 0xffffffff00000000],hint 5 0xd2b3cccb2bbfefebf2fbbbae7b66a8a9ea4a8a9fa769aa6696a11c16e1946096f52538 0x64c0cc4d18c399889224681a0d134489224681a0d13456b8133080ed010a1139e15ac1ef907720006c296e652a54a4a546b60e⟩,
  ⟨30,6,[0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xf8f8f8f8f8f8f8f8, 0xff00ff00ff00ff00, 0xffff8888ffff8888, 0xffffffff00000000],hint 5 0x34acf332caeffbfafcbeeeebb2ebb92dcb66d5a929fa7699a59c16e1946096f52530 0x64b8cc4c98c3918882206719ccd334882206719ccd335295930b10aab000cd63174a2d74887512962a89ad173a339c6107be2b⟩,
  ⟨30,6,[0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xf8f8f8f8f8f8f8f8, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff88888888],hint 5 0x34acf332caf19c4709bfefebf2fbbbae7b66aaa929fa7699a59c16e1946096f4e130 0x64b8cc4c98c3798882206719ccd334882206719ccd3352910b0b58e4b000cda51718ad712974e0846a71a66ad5d0839d0b598b⟩,
  ⟨30,7,[0x7070707070707070, 0x8888888888888888, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000],hint 6 0x3d1f43caeb78fd634acf332cc72bca71cc6f0dc32ffbfafcbeef6bbae7b66d8b52d1b42c8b1ac4b06bfaceaaa929fa7699a5a4a801ff7f9fd77dc165182525384c0a926c7b1a052 0x8908bc926f92e20920a48aa8926a4b128928a44a8482214632882952d5b0926c2f054955551598822652754856c28556115528ab21862262acb1eb27288b8ab2068941a2208ad452286294a2a586888a2a27e27d555b7d6637637249ddf6582493f83b8208e1f5df20835f31a28a69f69f28ad5f01d540d1f0dd8834c94e9482a49b534934c84e044180821345380a1138444ca2a08608154139904d54e09a04e24e095c822813953db3793753⟩,
  ⟨30,6,[0x7070707070707070, 0x7700770077007700, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xffff0000ffff0000, 0xffffffff00000000],hint 6 0x33ccc72bca714c470dc330bc26fbbdaeeb9edfb72d9b62d7b56a4a7e9da6a99a5a84929df705b3651825a930304af2a49b1ec781a06514803 0x32132b34dae1a8c34c0500643449108c134105705a30269764130118d1a8409a0d9c640618c19e5c878c7465c67c100660018105f6183d43e634d994b0f34f3d33dc30c71380f30f71828f0413d849c0413e23dc18672254f18658d5a550594da5651658c59b4c36cc3164d66d84560415982db04159f59b1866df3961866cf1d670758f3db71b⟩,
  ⟨30,6,[0x7070707070707070, 0x7700770077007700, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000],hint 5 0x32bca711c26fbb72d8b56a4a769ca6696a3a4a705b3651825a8c12bca526c7b1e0681945c14803 0x18df326d9b64c93025d8423b8422b04eae1ce9c9ce8d1c000da6d9b64c931efb0621d1e87a9bb5a9195c56b880561a9dc7c56b8⟩,
  ⟨30,6,[0x7070707070707070, 0x7777000077770000, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffffffff00000000],hint 6 0x33ccc72bca714c470dc330bc26fcbdaeeb9edcb66d8b56a4a7e9da729aa6696a3a84929df705b3651825a938304a92949b1ec781a05c14803 0x3d53e634d995b0f34f0500643449108c134104f0537424cf48174118d1a8409a0d9c640619d1973c75dd5863c67c100668018105f69a32132b34dae1a8c34c31d3143cf51d80c3cf3223190416626cc04165f28c18631f79918660d62554594da5855870f21874860f3dc75c71a45804161a2dc04161f61c18671f39818660c61c50370c318518⟩,
  ⟨30,6,[0x7070707070707070, 0x7777000077770000, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000],hint 5 0xcf329c4709bf2f6b9edfb66d8b5ea4a769aa124a705b3651825a8c12bca92949b1ec781945c14803 0x34dd35edfbdf7bbc24e0423d8422884cae98c9c98c7918000d34dd358cbbeefd86a1c9b06997d39dad3421f680561999c69dad3⟩,
  ⟨30,7,[0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff88ff88ff88ff88, 0xffff0000ffff0000, 0xffffffff00000000],hint 6 0xf3357cf332cc72ccaf29c9b1cc370cbfafcbdaeeb9ed9b62d4b3ac6b12bdaeea8a9ea4a829fa7a9da6e9aa6697a5a95a26848f603809df70594608a926c7b1a052 0x6c59456ef1866ef96d6c51857c74477e91867e94717c71877c73c77e21457e23e47c71476d41946e84426e81ac6d44547541547613c17611457543d47e11c47d48847d41c77e18a16cc20c6ea1906ea2306cc18c70c58c2a614e7a65a770c14ccaa1c07cc8807cc1cc7ea8a274c50c75a84d75a51974c84c6d21926ee2176ee1ab6d2212712152823595263145812592ca38837d21c37d28927e31c77528527635137638617525127a330b81260b79230cce3618⟩
]

def nodeBlock38 : Array Node := #[
  ⟨30,6,[0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff88ff88ff88ff88, 0xffff0000ffff0000, 0xffffaaaaffffaaaa, 0xffffffff00000000],hint 5 0x34bd2b3cccb29bfefcbdae7b7ed9b62c8ab2a7a929fa769aa5e95a268477dc1651822a47b1a052 0x14e5390b7238862f0c6a50c6244cd169ad9cdad091a319a685ed0f421e856100022884c1163f6cc612dea9b269366d43d0f⟩,
  ⟨30,6,[0xcccc0000cccc, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff88ff88ff88ff88, 0xffff0000ffff0000, 0xffffffff00000000],hint 5 0xd433cca726bf2f9bdae7b66d8b5eaca829fa769ba6a95a11df70594609382a49b1ec68 0x14d529cda39cb03b4396b40568c6795cdbbaae53c4f36c9b25bf0b590ab109675b24bb2d7441906714f33cdb26c9295d174⟩,
  ⟨30,7,[0x8888888888888888, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff88ff88ff88ff88, 0xffff0000ffff0000, 0xffffffff00000000],hint 6 0xf4bcdf3357d2b3cccb31caf29c731bc370cbfefebf2fbbdaeeb9ed9b62d4b32c8b1ac4af6bbaaaa4a7e9da6a99a5a8492a0781a057e5f377dc165182525384c0a91ec68 0x68c6b871ee8ed187188488a471e94b02072084488061a04622062141d4a120681ec5125141947d101f18651151f2025200942087e07d6256ac71eb26f5875965569461a55665865ab2035a00d6208ae082550f59f3d651495f7e11e1a8916a1f184986a184855121186a955618219082248278482247dc8545217df9145217a179659b7976336331c7cde3981c7674374186d1e31e186cb577220869e69e5142de29a5146de43259079e4f2853⟩,
  ⟨30,6,[0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff88ff88ff88ff88, 0xffff8888ffff8888, 0xffffffff00000000],hint 6 0xd2b3cccb31caf29c731bc370cbfefebf2fbbdef6bbae7b72d9b62d5b52c8b1aaaa929fa769aa6696a124a77dc165182524a91ec68 0x11a12614599a94414418b1a114584ba0614618a19610458a6461063453602c180590d2cd34435528054410d28d54608d5823461955953c73e31458c79cf14f3ce25d10974e78f10f8c650f5943c61a359674d20f5483cd35d5556056221c3885a581d888431838c60412238e6165dc1977167d818671549834d61555c34d6136d33db4534183cf⟩,
  ⟨30,6,[0x7777000077770000, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff88ff88ff88ff88, 0xffffffff00000000],hint 6 0x33cccb31cb32bca726c730dc32febf2f6bbae7b66d8aa2a7a92a0a7e9da6e9aa6697a5a89a123d77dc1651824e0a926c7b1a052 0x20f2201c780fa081c848749f3c27c78d23d26081126444882186582c92e11ce8499cb1cb84800b6402c82e16592d22d760c5d258b60b4074252549478902506990d020341941a20841841a49169861049068b29054a40b2da55519c1a61c799c9061c619918d2083596c620835804649219818d49219d1932cb4dd7862cb4da14641019a193410⟩,
  ⟨30,6,[0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff88ff88ff88ff88, 0xffff0000ffff0000, 0xffffffff88888888],hint 6 0x33cccb31caf2aca727c9b1fc7311c370cc26febf2f6bbae7b66d8b52a4a7e9da6a99a5a84929df70594608a91ec68 0xd40e210489484310314a15910464a9051051491510c34494c50c53043182816047cc28c3033102404030cc24c40508c44230515045038621b1086c68ce10e38d3950c354d58e0ce6c55ce45738515b45154c1ce40738c3154104842dd18b7447521927437523604830dd35d49169d15a75175214575075231e49041d31d48f71d39c74f75238e⟩,
  ⟨30,7,[0x8888888888888888, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xff88ff88ff88ff88, 0xffff0000ffff0000, 0xffffffff00000000],hint 6 0xd5f4accb2bca71cbfafbb9ed8b3accb22c7b12bdaeeaaa929fa769ca6696a3a4a82a097d1c165182525381ec68 0x1058043453453043043453453043041863c17cf3c010f68f3da68f3da44585144475179145e79145e28a3da6c389b0821106dc71b6dc71b5cf68f6d14931491541081185a366354f1cf2cb38e⟩,
  ⟨30,6,[0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xff88ff88ff88ff88, 0xffff8888ffff8888, 0xffffffff00000000],hint 5 0xd2b32caf29c72febeef8b9edcb62d5b22aaa929fa769ca6696a3a4a70594609491ec68 0x64c8d244910340d244910340ca55870b5806b8ad718ad716934d39ecd841b7bb5b73197198b735286c94ab39d6b37ae2ba51cd⟩,
  ⟨30,6,[0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xff88ff88ff88ff88, 0xffff0000ffff0000, 0xffffffff88888888],hint 5 0x332caf29ca326c831cc4709bfae7b62a4a769ca6696a3a4a70594609381ec68 0x64b8d244910340d244910340ca5586cb5806b6ad6d6ad6d39f0c60dec84192931923196d52aaea88758c6ae75694aadb59ceac⟩,
  ⟨30,7,[0x7700770077007700, 0x8888888888888888, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xffff0000ffff0000, 0xffffffff00000000],hint 6 0x3d3f4bcceb38ed5f4acf332cc72bca71cc6f0dc32ffbfafcbeef6bbae7b66d8b52ceb32c8b1ac3afabcac6aaa929fa7699a5a4a83a0d831fd77dc165182525384c0a926c7b1a052 0x8908bc926f92e209213253a520a926d4d24d32138110602084d14d52d5b0926c2f05495555159882265275485664d05604154d39a0822262acb1eb27288b8ab2068941a2208ad452581c8934e28209534e27e27d555b7d63f73b7249ddf5df249638638208e1f65820835f31a4d369f69f4d3d5f01d540d1f0dd8832922aa249a92c4a24a2912a12088518ca20a85310a8042932a182085514ab052952a1b212a52a18a2865a0a88adb378a74a⟩,
  ⟨30,6,[0x7070707070707070, 0x7700770077007700, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xffff0000ffff0000, 0xffffffff00000000],hint 5 0xcf32bc4709bbae7b72d9b56a4a769aa6696a11c16e1946096f4c0c12bca026c781945714803 0x16ce2d91645705c024d0423a8422a04a8d94a7b94a6c14000d1cceb9cbcbace75921785c591591645705c273a0541c15a5759d6⟩,
  ⟨30,6,[0x7700770077007700, 0x7777777700000000, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xffff0000ffff0000],hint 6 0x33ccc72bca71cc6f11c370cc26fbbdaeeb9edfb72d9b62d7b56a4a7e9da6a99a5a8477dc16e1b3651825bd6a525302bca92809b1ec681945714803 0x60e61d54474e39855805905c3837196c138105804d74235830174118e1a064980e7c664619d19160745d40660684100668018106169a3ed3e338e8edb0f38e5a614f6183e6ad66183ea3d30414ea94f0414e92cf1863e9a1318649549e38e79589239279821274849849e75d79a29204149a51e0414a449e1867a45d21864964a73cf9d6b923d2⟩
]

def nodeBlock39 : Array Node := #[
  ⟨30,6,[0x7700770077007700, 0x7777777700000000, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xffff0000ffff0000, 0xffffffff00000000],hint 5 0xcc71cc6f14c370cc2eeeb72d8b56a4a769aa11c16cd946096a4c0c12bca92809b1e0681945714803 0x1bffb67ad4e646cc25f0423a8422604cae98c9b98c7798000d1cefb7edd4f53f0721e9b8686f7083710422165862181a4686f70⟩,
  ⟨30,7,[0x8888888888888888, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff8888ffff8888, 0xffffffff00000000],hint 6 0x3d4f3babe3755d2b3cccb31caf29c731bc370cbfefebf2fbbdaeeb9edcb66d8b56d4b2ac8b1abeaeab8aceaaa929fa7699a5a4a826057e9f577dc165182525384c0a91ec68 0x68c6b871ee8ed187188408a471e94302072083c87c619f3e22062111d1a100681ec45045119178f01e18644f45e20245f09120879f793253ac71eb26f4c74d34939461a54a64c64eb2034df0d3208adf7e544e4de39345195e7a11e1a8916a1f184986a184852121186a924a17e19082247e784822479a85146179e9114617217134d97145b55b51c7d5c5d61c7cb66f218661c61c20835c31820855c55c4512dc29c451d1c7724ddcdc832860⟩,
  ⟨30,7,[0x8888888888888888, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff88888888],hint 6 0xf3fa9e2f53d2b3cccb31caf29c731bc470dc3309bfefebf2fbbdaeeb9ed9b62d4b22c7b1ac1aeab9ac6aaa929fa7699a5a4a82a077edf677dc165182525384c0a91ec68 0x6846b871ee86d187188408a071e84302072083c878619e3e02062111d19d00671ec45045119174f01d18644f45d20245e09120875e753253ac71eb26f4c74d34938c61a34a44c64eb2034de0d3208ade7a344e4dd3934518dd75f1dfa8916a1f17c97ea1847d211f186a9249f79f8882227a57c822275b7d145f75d89145f71f7134d9714cb26b21c75b55b5186d5c5d618655c55c20835c31c20861c61c4512dc298451d1c9b24e6cdca727e9⟩,
  ⟨30,7,[0x8888888888888888, 0xaaaaaaaaaaaaaaaa, 0xeeeeeeeeeeeeeeee, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000],hint 6 0xf1bc5f13bdcf332cc72ecaf29c730dc330bc26febf2f6bc2eeb9ed9b62d7b56d4b4ac6aaaa4a7e9da6696a4a8ea125892a1277ddd729c1651825e16f5a94b4c0a926c7b1e0681945c15c52 0x3aa3b53cfd6acce3ce41b4303cfc1bdd03d041a42638e99aa1039070f72f6c6bcfc9c6dc70e72568494e39c69c95021c9887104259a578f7b180ac4fd9ee5e78e7ab816aceb1ee9ec5025e809790431831adc55e81579c72b82b7cf7f44d2d0f3df4df7ce7e9751a4e39f75fa66a5f4107e636940dd2595f71c7e56747198389df79e03902e3c5ba2b403c003a0243839228c03800220184026225c040002200c7013222c0700822500780ee11c07c0⟩,
  ⟨30,6,[0x6666666666666666, 0xaaaaaaaaaaaaaaaa, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000],hint 6 0xcf332cc72bca70dc330bc2705c12febdaeeb66d8b5ed5b1ac5ad2aaa929fa7699a5a8ea12468f5df705946096f5a92848ca91ec68170571482b05c0d02003 0x3e53ef410be5b8f40f45846c410b18c514114574633cf8d79113d165066b609ad0b5961964f6625c888f3d95d98912998ca6514628e2010028484a109c048000f01e68378f7406800230144425234c044002200c6413222c064015016a7e9a90c057c514f1617e084f9857c51511567d55911c57c515914e7cd3991857c56dc6c500015c15b000⟩,
  ⟨30,7,[0x8888888888888888, 0xcccccccccccccccc, 0xeeeeeeeeeeeeeeee, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000],hint 6 0xf23c5f13bbd2b3ccc72ecaf29c6f14c470dc32fbbdaf0bbae7b7edcb66d8b4acdb22c6aaaa4a7e9da729aa6696a4a1477ddd729c16e1b3651825e1494e0c12bca9294a026c7b1a052 0x32933334dce9c4c34c41742c34db17d1035041642330c8d69d031068d6ab5c2acdc1a5da68c6a258188c31a59a89019a8c66904228e298d9af84abcdd66de6bcc26684998c32fe2f99042a860a90426866a9a6a685f99a6aa86a75377234dc9349d35d75b76830ca1b45d31da102dd8cb7504288e8c9a55d89575a6b28a287671d99c0f70ee348b9eb433430f80e530795e9033030de0d940565e6034030de0cf6843de38368385e503983e5e003740⟩,
  ⟨30,6,[0x6666666666666666, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000],hint 6 0xd2b3ccc72bca714c470dc3305c12f6bbae7b7edcb66d8b1ac5ad2aaa929fa769ca6a99a5a468f5df705b86cd946092848caf2a4a52809b1ec681482b05c0d02003 0x3e83f1410c68c0f40f4d84ec410b18c934134d74e33cf8d79d33d36d06eb607ad0bdb61b6cf6e25c688f3db5db8932db8cb6d34e28e201402a404a94a4040001c0203c381c7c03c00130168c25935408c001b00e88139b34088021022e86db90cc884820f22586494f30884821321a85969328884821b21285149b24884899e74800021e166000⟩,
  ⟨30,7,[0x8888888888888888, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xfafafafafafafafa, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000],hint 6 0xe3f72dc770dbf6ed5353d2b3ccef32caf00bfefebf2fbbbae7b86d9b62d1b42c7b12aaa929fa7696705b865182525384c07b1a052 0x1877462478092465c91e31e218c18c2552554c27d304118a2542532cb34778d34668d0c325464d35964d35358585610418c5896c96164d671634e9079479869c6a093c9a50453493000208⟩,
  ⟨30,7,[0x8888888888888888, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffaaffaaffaaffaa, 0xffff0000ffff0000, 0xffffffff00000000],hint 6 0x38edf37bdeb79dcf56d574fcf332caf29c7315bfefebeee7b66d8b3accb1ec3ab2aaa929fa769c95a4a77dc1651821ec6d1a052 0x1057441471471221215457d50843c41862c370b2c110b68b2da50b2d434578d34460d6cd35b6cd3552082d45c781710910c5965576542d42d734e9059459849c4a114954d58cb40b00028a⟩,
  ⟨30,7,[0xc0c0c0c0c0c0c0c, 0x8888888888888888, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000],hint 6 0x3ade6f9ae6798e5f58d5353d2b3ccef32caeffbfafcbeeeeb9ee1b66d8b52d1b42c8b12aaa929fa769692a18705946096f525384c09b1ec68 0x1c87c72488892476895818560001cc2572563c880f3c774f0c32572cf59916364410739925e2524966d93d09c8a08a47a87ac94494d651618608290894838738760960934d70f5592994ec4e6⟩,
  ⟨30,6,[0x8888888888888888, 0xaeaeaeaeaeaeaeae, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000],hint 6 0x34acf33bccb2bc6f11bfefebbae7b72d9b62d1b22aaa929da6a96929c16e194609494e130304af294a026c7b1a052 0x2cc80b38c8ce38b6ce5c28970412d03983974cc8534cb7132083983cf4d768a91a2492df68e74e5554926935130c77830c66430c54430c4583000343⟩,
  ⟨30,7,[0xcc00cc00cc00cc, 0x8888888888888888, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000],hint 6 0xeb3a4e8fa2e879cd5f56d574acf332caf29c7315bfefeb9ed9b62d4b3acdb32c8b0eacaaaa4a7e9da3a4a869df70594609494e13026c7b1b468 0x1c88476888da04748738280e3801ce64e39940889040771011068c30e65b1a46c51473db59d6d439939b411a48a88ac7b0755a5daa0e4ce34d0c328828894798724978e78e7d061b2db56d567⟩
]

def nodeBlock40 : Array Node := #[
  ⟨30,6,[0x8888888888888888, 0xaaeeaaeeaaeeaaee, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000],hint 6 0xd2b3cccb2bca711bfaf0b9edcb66d8b3acdb22acaaaa4a7e9da724a705b365182525384c0c12bca52809b1ec6d1a052 0x30d88c6cd91b08c58c48385248131269249a50d8d450c7d424951e41049a74b95d28a3137583cf5d2692754554108804107704106644105384000444⟩,
  ⟨30,7,[0x8888888888888888, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xfff0fff0fff0fff0, 0xffff0000ffff0000, 0xffffffff00000000],hint 6 0x388e1f86e1756d5754d4f4accb2bca71cbfefebf2fbbc6eeb9ed9b62d4b46d0b3accb1aafaaaa4a7e9da669692a1e8761c70594609494e13026c52 0x1469051a81a716a1691c64871c570768738d8ce38c14e64e1ce7501a541016041341028208788b2ce7db1266c30c53c96db61b1e11de39b39b411ac6b06b45b8521555850754758e5ce000041⟩,
  ⟨30,6,[0x7770777077707770, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000],hint 6 0x32bca711c26ffbc6eeb9edcb66d8b56d0b32cbb2ac9b1eafa929da6696705b8651825bcc12bca52809b1e0651705714803 0x30d98c3cd50f3cc80f4919524903123d23e10458c10446c10433c104248118a9061897861888861877c60000533563553183173dd3d949c49a4c12c17c6386⟩,
  ⟨30,6,[0x5550555055505550, 0x8888888888888888, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000],hint 6 0x34ace732caf29c46ffbfaeeb9edcb46ceb36c8aaaa4a7e9d929c16e194609494e130304af294a026c2e06803 0x2cc7cb38c84e38b68e4027904012d039039448c81248b6d22083953cf4140c77430c66030c55830c45c300066229944b24939c399414414493499343⟩,
  ⟨30,6,[0x8888888888888888, 0xaaaaaaaaaaaaaaaa, 0xccc0ccc0ccc0ccc0, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000],hint 6 0x34acf332caf29c26ffbfaeeb9ed9b62d5b3ac8aaaa4a7e9da124a705946096f5a9494e1301ec781a06514803 0x2cc7cb34c84d34b68d4057904032d035035748c81248b6d218635838e4176488991c72d164d70d5105d06524d204474104258104d3c105024104a541000⟩,
  ⟨30,8,[0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xeeeeeeeeeeeeeeee, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000],hint 7 0x3a8e2b6bdab68d9b3ccc72bca714c470dc330bc26f6bbae7b7edcb66d8b5ed5b4ad1b42ceb32cbb2ac9b1ec6aaaa4a7e9da729aa6696a3a849364c92e4790a3f8ea368c22d8a22789a2488a2188213845df705b86cd946096f5a8c12bca9294a026c7b1e0681945c15c52 0x9e3e20f9f348109f3624c9e3c80f9e4d5939f208109f215ce9e4c813a04d513a0fc78fa0fd543a04c7939eb882e9f1d5869f1c84b9eb95aea0b87aea0f9504a0f878fa0b952ea2f898aa4b9f8a4eb8993a2f9fbe9ecc8109f3d3349f3c8109ece7b3a0d478fa1412b6a14078fa0d6835a2dc99348e11a276e0993a2dd0b7a4e572e40e8f9e76e972ea4e4eb99e00a009f188059f18a459e00800a001780a0f4783a0f57bca000780a20098038a5f8276a49a8a201f80a4017003639f01763970da401f00765e9b09e019809e1c8079f28a0c9f288499e1ca07a01c787a10578ba1047c0a01d787a21df8764b498934b5faca21c987a41df0764497083249f11a41d7076462a429e1d9876460000761cb876458ab1⟩,
  ⟨30,7,[0x2222222222222222, 0xaaaaaaaaaaaaaaaa, 0xeeeeeeeeeeeeeeee, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000],hint 7 0xf57c7f1bc4e2b66cf332cc72bca71cc5311c370cc2f09bfafcbdaeeb7edcb66d8b5ed5b4ac7aaaa4a7e9da729aa6696a3a849624a77dc16e1b3651825bd6a52d30304af2a4a52809b1ec781a0651705714803 0x92d24e499372b5c122648b1d2ccc9936675d962658b1c2ca49125271616245901340c8e87644dba03a8101240a0e0550489203881416168148b4058b2852a111344d928f6c4dd227e8911244b92995c497a28089b161c8928e4458b364ad97203089298448102e4ab841310d4b8d6a4da082e2041210ad08c56495084220429107cb0a3ea4f082c2042810550092aa0a0840212c10021100024c0b12ec18930c04b8102480a74299392080508102a409b2c68da90604b0102a009140408a8040500178f52014405f254604401⟩,
  ⟨30,7,[0x4444444444444444, 0xcccccccccccccccc, 0xeeeeeeeeeeeeeeee, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000],hint 7 0xf57c9f23c4ea366d2b3ccc72bca71bc5311c370cc2f09beef6bbae7b7edcb66d8b5ed5b4acdb22c7b1aaaa7e9da729aa6696a3a8477dc16e1b3651825bd6a52538304af2a4a52809b1ec781a0651705714803 0x92e24e499372b9c122648b1b2ccc993666dd162658b1a2ca491252696962458f133cc8d87644db9e3678f123ca0d05504891e3479416167948b3c58b2852a161358d928f6c4ddac7eb1b121cb128e584893680d96162cbd2a45e58b2c4ab179e3cb12a35878f2f4abc09702c4986625d801260409f029c9044e7d301240409602654833258c01520409e0245402227880150052c10005600105c43526d1a971a20988107c42b24a959f1820908105841d5270e96142148810784155050a9e122140878f51085821f214020081⟩,
  ⟨30,7,[0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xeeeeeeeeeeeeeeee, 0xf0f0f0f0f0f0f0f0, 0xfafafafafafafafa, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000],hint 6 0x3addcb71dc36fdbb6bd9f66cf33bcaf09bbaecb9ee1b66d8b56d2b46d0b12aaa929fa7696a122377dcd705b86cd946096a26c7b1e0681945c15c52 0x24a8c934a94d34984d2a72a625425435e35e70691c10425235d35c4d32aa2a926c26b35736d62ea187197180058800036c000244068001000120054030f28c30e80c30d74c1c770c2df300316⟩,
  ⟨30,6,[0xaaaaaaaaaaaaaaaa, 0xc8c8c8c8c8c8c8c8, 0xeeeeeeeeeeeeeeee, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000],hint 6 0xd433ccef2bc26fdbf2eebb2e7b66d8b56d1b3ec3b0aaaa9296a125877dcd705b86cd946096a26c7b1e0681945c15c52 0x24a88934a90d34978d6868da10425235b35a7e095f25025535735669869f0058400036400024400012004c030f28c30e74c30d6cc68c2cb70c007014⟩,
  ⟨30,7,[0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xeeeeeeeeeeeeeeee, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffaaffaaffaaffaa, 0xffff0000ffff0000, 0xffffffff00000000],hint 6 0xeb37cdef7ade773dab69da33ccaf29ca315c26fbb66d8b56d2b3accb0eacaaaa4a7e9da729aa122577dc1651825a89b1ec781b4681945c15c52 0x28b8ca2cd2cd2a62a574b91d14a58a30c4878924842928124a071249c2ea2e92ac2ab62d9d87597584974a80067c00036c068000e0023c000124050044d85145329120875141149c45e440455⟩,
  ⟨30,6,[0xaaaaaaaaaaaaaaaa, 0xcc88cc88cc88cc88, 0xeeeeeeeeeeeeeeee, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000],hint 6 0xcf32bca728c7b1cc2707bc2e7b66d8b56ceb12bbab2aaa929da729aa11dd729946096a52c9b1ec781b4681945c15c52 0x2cc90b6cc95b14b54b4878d24842d269249a3093162e12e06d86e049e4970067c00036400023c00012804c044e89144d2d1751410452691711008014⟩
]

def nodeBlock41 : Array Node := #[
  ⟨30,7,[0xc0c0c0c0c0c0c0c, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xeeeeeeeeeeeeeeee, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000],hint 6 0xe6f9ae6798e5f8fd9f66cf33bcaf11bbae7b86dcb66d8b46d0b1ec4aaaa8a929fa769aa59df705b8651825e96f304af2949b1ec6815c52 0x28b84a34b8cd34a7cd68389a08228f35b35a2e82e72aa2a935636b69969820b38820a4882095080486932041e010419c10415010430c11e10811590b94b48a48a74d74d45199700010c10c⟩,
  ⟨30,7,[0xcc00cc00cc00cc, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xeeeeeeeeeeeeeeee, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000],hint 6 0xe93a3e8ba1e738eda768cf32bca715c46e7b72d9b62ceb32c7b0eacaaaa9a929fa769ca528e77dc16cd94608c12bca026c7b1b46817052 0x24a88970a8dc0c95894448514422516d145b2a92a826b26a71a71945746738a34e38948e04e70e3d439338521f1451dd14541014518b15e14e15534a34a90994930c811811998000150150⟩,
  ⟨30,7,[0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xe0e0e0e0e0e0e0e0, 0xeeeeeeeeeeeeeeee, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000],hint 7 0xf5bc0effade3f6bcf331caf29c5311c370cc2f09bf2fbbdaeeb7edcb66d8b5ed5b4ad1b42c6b12c1afeb3aaa9fa769ca6a99a5a8ea122c8ae2a8a5df705b86cd946096f5a8c12bca9294a026c7b1e0681945c15c52 0x3d88f784083c62ec7901e4ce136e4083738f4990264cd935a3c7ad36c098f268c81082a524120411c146a478f84a51421e3cc422ea49934aa52a5264cb292a7c81f6c7033620e8f9c3e7c79f586c22c1e3cf9b3eb098a3eb451f264d62d590df283e9cf802801a900ad4a340040000400158f06ad02a003c0002600d2d046899900b40297ecc0270000f801cb008e3e3402c001c807725063920e03940e1c7875e805af1eb83a00e1d6873c4c49e5a743930ea60320e9c387581c91f10496110e7c3a900003a90ea5321⟩,
  ⟨30,6,[0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xe0e0e0e0e0e0e0e0, 0xee00ee00ee00ee00, 0xffff0000ffff0000, 0xffffffff00000000],hint 6 0x33ccc72bca714c470dc330bc26f6bbadfb72d9b62d7b56d2b1aaaa7e9da729aa6696a3a8477dc16e1b3651825bd6a304af2a4a52809b1ec781a0651705714803 0x428431451c68c1045051952c451b19c944545185244109189d441471172b647ad1bdc65c7107236058d041c61c8d42dc90b71452392305506a446a95a4144105d06240489d8414010540579035d458190105c04f8c23dc3818c121122e54db91b4854821022674c99094874822421b50a6e46885082232137094e34887088010088002010607de⟩,
  ⟨30,6,[0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xe0e0e0e0e0e0e0e0, 0xee00ee00ee00ee00, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000],hint 5 0x32bca711c26dcb62d5aaa9da7299a5a8e705b3651825a8c12bca026c7b1e0681945714803 0x18de324d9362c8b24d9362c8b1efa1b74a1194bd297bd2970972108ec10c2010c201089613ab473a7073ce673ce673a1c700035⟩,
  ⟨30,6,[0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xe0e0e0e0e0e0e0e0, 0xeeee0000eeee0000, 0xff00ff00ff00ff00, 0xffffffff00000000],hint 6 0xcf331caf29c9714c470dc330bc26f6bbadfb72d9b62d7b56d2b1aaaa7e9da729aa6696a3a8477dc16e1b3651825bd6a304af2a4a52809b1ec781a0651705714803 0x51952c451b19cd4454428432451ca8c504504244185146249d051471172b647ad1c1c65c8d42dc90b7145239237107236058d041c61c05506a446a95a414410540579035d458190105d06240489d84140105c04f8c23dc3818c121122e54db91b4854822421b50a6e468850821022674c9909487482232137094e3488708bc100880020106f7de⟩,
  ⟨30,6,[0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xe0e0e0e0e0e0e0e0, 0xeeee0000eeee0000, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000],hint 5 0x33cca711c26f6b7ed9b62d7aaa9da6a84705b3651825a8c12a4a52809b1ec781705714803 0x30dc35ede3df6b3f0dc358cb3ecf91772956b24a5f5956b2093210d28108e010d2810896132b4635ee63222635ee631dc600033⟩,
  ⟨30,7,[0xe0e0e0e0e0e0e0e, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000],hint 6 0x3d6daf3ccc72bca714c470dc330bc26f6bbadfb72d9b62d7b56d2b46c8b1ac3b0ac0a7e9da729aa6696a3a8492a2f8b9df705b86cd946096f5a8c12bca9294a026c7b1e0681945c15c52 0x84fb8f877410877bb684f40f8936d38b24108b26f889341385369386a3cf86a6ad8533d39805005b04059b052f8004008407c08683c38687e78403c08804c0899a828994d8880a808074078f450c5744338075078473c786c7cb86c3eb8477c7887a8789d4c989da9c8874c78e40009875c7e870008e45d795e6de9714359716c695e41e95e69e9693cf96968495e3de969aa995e4d395ea8a9694cae6900095e38d95e000969381e5e1c79694919691c795e488⟩,
  ⟨30,6,[0xe0e0e0e0e0e0e0e, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000, 0xffffffffaaaaaaaa],hint 5 0xcf33bcc714c4709bbad9b62d5a7e9da124a77dc1651825a8a926c7b1e0681945c15c52 0x357152a2a5e54ca518c5ed8c5558e001c02d8001c80013c073af1754551a328c0380e84e70868d0828909b1080240184e70⟩,
  ⟨30,6,[0xcccccccc, 0xe0e0e0e0e0e0e0e, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000],hint 5 0xcf33bce331c530bbbadcb66d8b229fa769a77dc16cd94608af2a4a52809b1ec781a052 0x25584b15b6313560aca8260964d9325f2422284219c4890917e86f7a42f930e793df222c856aa098259364c00244917c9f2⟩,
  ⟨30,7,[0xe0e0e0e0e0e0e0e, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xeeeeeeeeeeeeeeee, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000],hint 7 0x3d7f5bbfdaf3ccc72bca714c470dc330bc26f6bbadfb72d9b62d7b56d2b42c8b1ac3b0ac0aaa9fa769ca6a99a5a8ea124a8d6348ce328c5df705b86cd946096f5a8c12bca9294a026c7b1e0681945c15c52 0x3d90f764083b64e87901e4cf136c408363cf0990264ce935c3c7ae3ac498f26a88107ea8cbf204123f309478f80a8bc01e3d2c04a989932ca8aaa264d32a4c00a0068402b428cc0100001100583c1ac44ac00f000098038b811c266c02e00a951a00f4007201dc1418e08370e503871e1d82216c07af0e883875c1d013128171f0e4c3aa4ea03bd0ea80000ea83aa4e8d09e42d48396a78321208509d42b478f5a742211e856ae5a8499342b852d2629f3d5285ea15a000211c3508000b4701421c3ad24456870e84908⟩,
  ⟨30,6,[0xee00ee00ee00ee, 0xe0e0e0e0e0e0e0e, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xffff0000ffff0000, 0xffffffff00000000],hint 6 0x33ccc72bca714c470dc330bc26f6bbadfb72d9b62d7b56d3a7e9da729aa6696a3a8477dc16e1b3651825bd6a304af2a4a52809b1ec781a0651705714811 0x42642f451be6b90450055068446a159c144105d06040481d7c140121122c54db11ac854821022474c9108c874878104800820105e00071972946da591dc45c71872141085815c41c84105c3ce7010613c27082214d284821c4c951152a670a914546545105226258904146148810545d65010625c35082226da8882146ca5212e270b8a1854714⟩
]

def nodeBlock42 : Array Node := #[
  ⟨30,6,[0xee00ee00ee00ee, 0xe0e0e0e0e0e0e0e, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000],hint 5 0xcaf29c4709b72d8b569da7299a5a8e929c16cd946096a304af2809b1ec781a06515c52 0x16cdae4c9322b8ac04c0002a8010800c9c98c8b98d39980603e9a2d28b1d2d4a580a004cd31d92649715c5ce0401034cd3b52d4⟩,
  ⟨30,6,[0xeeee0000eeee, 0xe0e0e0e0e0e0e0e, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffffffff00000000],hint 6 0xcf331caf29c5311c370cc2f09bdaeeb7edcb66d8b5ed5aaa9fa769ca6a99a5a8ea125d77dc16e1b3651825bd6a304af2a4a52809b1ec781a065170571481a 0x51a52b451adac54454055069446a55a014410540588c36145c18c121122d54db51b0854822321c50a7236c850800104858820104059f75a76a46ea9a1dd45d8a389d5147632e250b88105d3ce7410623c27482224d288821d4c94114309efc114509d04145198e66545108d040105e86078105084478821096440821e94c41d75988565d750890⟩,
  ⟨30,6,[0xe0e0e0e0e0e0e0e, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xeeeeeeee00000000, 0xff00ff00ff00ff00, 0xffff0000ffff0000],hint 6 0x33ccc72bca714c470dc330bc26f6bbadfb72d9b62d7b56c8a7e9da729aa6696a3a84929df705b86cd946096f5a8c12bca9294a026c7b1e0681945c15c52 0x4d84e23cf8989533d342f4263cf9afb903cf42a4194d366ac104d301d0203c381d7c03c00130178825d3580880014028405a149c04001cf1e474b90f8c77471e21db4c96e26874c71d01ec50cb10ac75077800075471c001e5557187213cf85811c3dc86285c4d37222a14ca71972942da5919c41c84001c38d7000213817071e14918471dc488⟩,
  ⟨30,6,[0xeeeeeeee, 0xe0e0e0e0e0e0e0e, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000],hint 6 0xcf331caf29c5311c370cc2f09bdaeeb7edcb66d8b5ed5aaa9fa769ca6a99a5a8ea11df705b86cd946096f5a8c12bca9294a026c7b1e0681945c15c520c02e 0x5595634518d999545509e0a144585e8024420950988c46155c28c225126578d95190978926325c54b7236c954900208904924208005f75976245189919d45d8a389d55576332254c88209d40f7420a240374926251388925d50a491467c2f9d1452c1249555aaf1695552ad2482096a68582092a47589252b6c489256b4e49d75aa8869d752aae⟩,
  ⟨30,7,[0xe0e0e0e0e0e0e0e, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xeeeeeeeeeeeeeeee, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000],hint 6 0x36bcf32bc4709bbae7b72d9b56d1b42c7b0ec2b02aaa929da6a99a5a848e6388ddc16e1946096f304af2949b1e06517052 0x24a90930a94c30984c29229225125131e31e28f29724e25830d31999c9800e200009d0000500002080150041e310419f1041531042cb12010011648a48a44944978c78c5146da00800810b10b⟩,
  ⟨30,6,[0xee00ee00ee00ee, 0xe0e0e0e0e0e0e0e, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xffff0000ffff0000, 0xffffffff00000000],hint 5 0x33ccaf11c26eeb72d9b569da6a99a5a84705b8651825bd30304af2949b1e06517052 0x14bca9705c14f53c03b80029800948087c1086a908c610040220b82dea7aa52024092308c6e96d6d94da35b403801244856d28d⟩,
  ⟨30,6,[0xeeee0000eeee, 0xe0e0e0e0e0e0e0e, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffffffff00000000],hint 5 0x33ccaf11c26eeb72d9b56aaa769aa6696a11c16e1946096f304af2949b1e06517052 0x18ad314f53d9465003b80016800840087c10858108b59004049ea7aa8ca32310200822c8b4e549659897252e04c02254864b9c9⟩,
  ⟨30,6,[0xeeeeeeee, 0xe0e0e0e0e0e0e0e, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000],hint 5 0x33ccaf11c26eeb72d9b56aaa769aa6696a11c16e1946096f304af2949b1e06517052 0x189b312e4b99465002980016800840086a90858108b59004049c97268ca32310200822c8b4e52a6698a7a94f05c032608753dea⟩,
  ⟨30,7,[0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xee00ee00ee00ee00, 0xeeeeeeeeeeeeeeee, 0xf0f0f0f0f0f0f0f0, 0xffff0000ffff0000, 0xffffffff00000000],hint 7 0xf63c2f07ace3b6acf331caf29c7314c470dc330bc26f6bbae7b7edcb66d8b5ed5b4aceb32c6b0ebeaf2b1aaa9fa769ca6a99a5a8ea123e8f23b8a5df705b86cd946096f5a8c12bca9294a026c7b1e0681945c15c52 0x3d90f784083c64ec7901e7c81f6a7033520e8f9c3e7c79f586c22c1e3cf9b3ea481082a51412040c412e8c78f84a52421e3d1c246a4f9f4aa52a53e7cb292a4ce136c4083638f4990264cd935a3c7ad36c498f26b4f8a26b05133e4d6ac590df28269c9802801a100ad0a330040000400158f06ad02a003c0003e0072c0238f8d00b00297ee4027000098034b411a266402d001c807705063820dc3940e1c7875e805af1eb83a00e1d607247c412584439f0ea60300e9c3875a1cf13127969d0e4c3a900003a90ea5321⟩,
  ⟨30,6,[0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xe0e0e0e0e0e0e0e0, 0xee00ee00ee00ee00, 0xf0f0f0f0f0f0f0f0, 0xffff0000ffff0000, 0xffffffff00000000],hint 5 0xcf32bc4709bbadcb66d5aaa9da6a99a5a84705b8651825bcc12bca526c781945c14803 0x14bd29705c14f53dabdb5aabb6ad6d5705c14f53e526d5b50930108e810a521089c10a5212a32529ec52b18529a252b18500033⟩,
  ⟨30,6,[0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xee00ee00ee00ee00, 0xeeeeeeee00000000, 0xf0f0f0f0f0f0f0f0, 0xffff0000ffff0000],hint 6 0xcf331caf29c5311c370cc2f09bdaeeb9edfb72d9b62d7b56d2b1aaaa7e9da729aa6696a3a8477dc16e1b3651825bd6a304af2a4a52809b1ec781a0651705714803 0x7107236058d041c61c472469410a72c5141066c1d171c46cc1971c518524410918a1441491c2d48cb51c5248e351952d451b59cd445405d06240489d84140105c04f8c23dc3818c105506b446ad5a814410540579035d458190121022674c9909487482232137094e348870821122f54dbd1b8854822421b50a6e46885089c10088002010677de⟩,
  ⟨30,6,[0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xee00ee00ee00ee00, 0xeeeeeeee00000000, 0xf0f0f0f0f0f0f0f0, 0xffff0000ffff0000, 0xffffffff00000000],hint 5 0xd2b31c530dc330bbbadcb62d5aaa9da6a84705b3651825a8af2a4a52809b1a0651705714803 0x19ce3259cca45649ade338cccb327eb4f7b2ef4a5f57eb4f0e30109281089610e30108e0136fa632ac631dc636f663222600033⟩
]

def nodeBlock43 : Array Node := #[
  ⟨30,7,[0xee00ee00ee00ee, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xffff0000ffff0000, 0xffffffff00000000],hint 6 0x3d8dab3ccc72bca714c470dc330bc26f6bbadfb72d9b62d7b56d2b3acdb1ac4af6bba7e9da729aa6696a3a849064077dc16e1b3651825bd6a4c0c12bca9294a026c7b1e0681945c15c52 0x810b90837451837bb681045081e45e8316c683147581e6de89e41e8a96848a941089e69e80054083044583056f8004409807c05e84039a87e784040088078088fa4188f78e880a4080744783454c8344738075478474078ec7cb5ac42b8477c7887a47893788893a528877878e4000987347e870008e434d9544549726f89724519546d495441496a6ad96a41095469496aa69954794954a4a96a78ae6a00095465895400096a642e541c796a75c96a1c7954749⟩,
  ⟨30,6,[0xee00ee00ee00ee, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xffff0000ffff0000, 0xffffaaaaffffaaaa, 0xffffffff00000000],hint 5 0x343cf329c26f6bbee7b7edcb66d8b56aca7e9da11df705946096a4c0a926c7b1e0681945c15c52 0x31cc72d9a5c57037210a521022e002ec09001201cc000a81777ae73aef6bc330024096f58d6d6ad6c96da350803c026e2ed⟩,
  ⟨30,6,[0xcccc0000cccc, 0xee00ee00ee00ee, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xffff0000ffff0000, 0xffffffff00000000],hint 5 0xcf33aca711bdaf0b7ed9b62d7ab29fa769a77dc16cd94608c12a4a52809b1ec6819452 0x25574bc797bc497c95a906497cdf222304256a4215649109666d4c6452c9b0e793194238866a9aa825f37cc002549565194⟩,
  ⟨30,7,[0xee00ee00ee00ee, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xeeeeeeeeeeeeeeee, 0xf0f0f0f0f0f0f0f0, 0xffff0000ffff0000, 0xffffffff00000000],hint 7 0x3d9f63c1dab3ccc72bca714c470dc330bc26f6bbadfb72d9b62d7b56d2b36ccb1ac4af6bbaaa9fa769ca6a99a5a8ea1245912438de3177dc16e1b3651825bd6a4c0c12bca9294a026c7b1e0681945c15c52 0x4191076448bb64e881120848a16a7833522e509e42848215a7422d204109d42908917ea8d3f224523f48a881080a8cc020412c030990a12ea8b2a428532a4c00a8068442b42acc011000110058401ac44ac01000010801eb408f423802d00a950d00f4007221dc1518e08b70e54387201d82216c082f0e883875a1c9a1104d6920e843aa4ea43bd0ea80000ea83aa4e8ca1128d8f3c6c448943c50a1028b8eb15c408143a5172d5a5109428b452e4229f3d5051e945c00014386ca0000b8e02281c3ae407d7070e51009⟩,
  ⟨30,6,[0xee00ee00ee00ee, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xeeee0000eeee0000, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000],hint 6 0x33ccc72bca714c470dc330bc2708bdaeeb7edcb66d8b5ed5a7e9da729aa6696a3a8477dc16e1b3651825bd6a4c0c12bca9294a026c7b1e0681945c15c52 0x711729646a51b5c65c42542f451be5b9045062011071c42041871c015028445a159c044001c00f8013dc38080001d01f4037dd7804001d11ec54cb11ac75471e01d37084e04877071d01e374b8d08877479800073471c002634d51152a670a914546548608147145202a170a5105216248504146148400145d65000215c25071e16da8471d46c9⟩,
  ⟨30,6,[0xeeee0000eeee, 0xee00ee00ee00ee, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000],hint 6 0xcf331caf29c5311c370cc2f09bdaeeb7edcb66d8b5ed5aaa9fa769ca6a99a5a8ea11df705b86cd946096f5a8c12bca9294a026c7b1e0681945c15c520841f 0x75276a688a92b9d69d0960a9487a56a0248209d09088341d3c288225226d58eb52b0958926225474a5224c974900208904924208005f55256b6b1ad24956958e289575556232374c8c20956175420a360454926371b8c925570b4524709efc124919d165d75189145d75988644209e86078209184578925196444925e94d6555518d14555598e6⟩,
  ⟨30,6,[0xeeeeeeee, 0xee00ee00ee00ee, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xffff0000ffff0000],hint 6 0xcf331caf29c5311c370cc2f09bdaeeb7edcb66d8b5ed5aaa9fa769ca6a99a5a8ea11df705b86cd946096f5a954304af2a4a52809b1ec781a0651705714834 0x75176264589145d65d05e06144485e80144105d05088241d3c188121122578c9519087882222147495224c874800104838820104039f5515636668d14556558e28957555622e374b8c105561754106360354822371b8c821570a491467c2f9d1452c1269d752aae49d75aa87481056a68581052a46588212b6c488216b4d695552ad249555aaf1⟩,
  ⟨30,7,[0xee00ee00ee00ee, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xeeeeeeeeeeeeeeee, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000],hint 6 0xdab2bca711c26fbb72d8b56ceb32c7b12bdaeeaaa929da7299a5a8e926488c9c16cd946096a304af2809b1ec781a06515c52 0x2cc98b50c50c4cb4cb5859565832d68165a03113192d02da9de9d63d66c012300009f00049200004a0170062641862211865551861cd1a21801983143142d32d338e81681675c012012195195⟩,
  ⟨30,6,[0xeeee0000eeee, 0xee00ee00ee00ee, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffffffff00000000],hint 5 0xcaf29c4709b72d8b56aaa769ca6696a39c16cd946096a304af2809b1ec781a06515c52 0x22c8b265d4ed39d804c000f78001500c9c98d2918c76980605191645ceb4ed303c0f348d25ed8b5c20b9ae630540235cc882d70⟩,
  ⟨30,6,[0xeeeeeeee, 0xee00ee00ee00ee, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000],hint 5 0xcaf29c4709b72d8b56aaa769ca6696a39c16cd946096a304af2809b1ec781a06515c52 0x20b82e635ced39d802a800f78001500c8b98d2918c769806051705c1ceb4ed303c0f348d25ed6c6462c9ea6506004364c98b191⟩,
  ⟨30,7,[0xeeee0000eeee, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xeeeeeeeeeeeeeeee, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffffffff00000000],hint 7 0xf6bc3eaf8dda33ccc72bca714c470dc330bc26f6bbadfb72d9b62d7b56d2b2ac6afabaae2b3aaa9fa769ca6a99a5a8ea1258922448e23377dc16e1b3651825bd6a4e0c12bca9294a026c7b1e0681945c15c52 0x50f146c448b63cf0a1128848a16a7833522e509e42b4a0a42b852128516ae5a9489182a934122452c14a9ca1432a8c2a28513aa4ea90a12ea8b2a428522a4800a8068442b42acc0110000a0038b811c286c02e00010801eb408f423802d00a9f1a00f4007221dc1518e08b70e543875c1d014128171f0e503875a1c9a1104d6920e843aa7e343bd0ea80000ea83aa508c81120ed93a7644890644081428757313a50a105c40ea14241690208509d5a1203d5241e90200002258ad1000041603441c39060bc8070e8980b⟩,
  ⟨30,7,[0xeeeeeeee, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xeeeeeeeeeeeeeeee, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000],hint 7 0x3dbea78bd9b3ccc72bca714c470dc330bc26f6bbadfb72d9b62d7b56d2b1ec6b06baae6b1aaa9fa769ca6a99a5a8ea1249916398d5df705b86cd946096f5a94b524c12bca9294a026c7b1e0681945c15c52 0x54e955c448ae3ac4a912a848a15a7422d224509d42b4a8a42b85212a556ae5a9489180a934022452c04aa8a9534a8caa2a5522a489d0a130a8baa42853aa4e0110058441ac44ac0110000a8038b811c2a6c02e000108020b4090423c02d00a9f0e00f4007221d82216c08af0e883875c1d015128171f0e543875a1ca2110516930e843aa7e343bd0ea80000ea83aa508c91122c9dba644489276489152a79b3c3c54a926c48f214249ab9248509e6a19ebd5249e92240001668ccb000049a052c1c39270dc9070e59c0c⟩
]

def nodeBlock44 : Array Node := #[
  ⟨30,7,[0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xeeeeeeeeeeeeeeee, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xfff0fff0fff0fff0, 0xffff0000ffff0000, 0xffffffff00000000],hint 6 0x388e1f86e1769da367d9b2bca711c26f1bbae7b72d9b62d5b4ad1b42ceb32afaaaa8a929da7299a5a8e939c16e1946096f304af26c7819452 0x1c89072262251e81e728850a2877ca70a40e8d040d1d06d0290808a88a47b07ad95962ca58a5506105c00a100005a0001860003120001860110031620c311d0c32490c33cf0c32490de0c00d3⟩,
  ⟨30,6,[0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xeee0eee0eee0eee0, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000],hint 6 0xcaf29c4709bc6eeb72d9b62d5b42ccb2ecab26c7abeaaaa29da7299a5a8e705b8651825bcc12bc9b1e06514803 0x2098c82c94cb2c878b40e89040d2102d02df2552542172162dc2d841b41904380104268104c4410471c10471c110684410574410f3c410a28410a284000052⟩,
  ⟨30,8,[0x2222222222222222, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000],hint 7 0xe3f8ee338ad9b53cf332cc72bca71cc5311c370cbfafcbdaeeb9edfb72d9b62d4b4ad1b42ceb32cab1ec6a929fa769ca6a99a5a5a966579565494e529465092a207b5df705b86cd9460930304af2a4a52809b1ec6814803 0x842d98b84f460c84f59bc842c60b843cf0f84dc60c84dcf3f843c60f863ce8f86b858b86b8eb2863c58f848462184d8f0384d863b8484f2186845a186b4e8286b458b8684ea188b47878a85707388478f88b572d848c82384e860c84e883e848c623868d12386d058b86d1135868c5a388e878a368d70a568c78f88e972e8ad1093348d693568d0a18ad16ad841060484e480984e46388410804861058486c110886c05af861110488117045880786328171f88107848a116845839085303968d8a11084485cb00561090458451a3849460c8508810850860c8494810869858b870d122870c58b8699122889d72e56a078f2aa172e889c78f8aa56ad56a90a128a96ad8aa50a15704901849518159008b18494204⟩,
  ⟨30,7,[0x2222222222222222, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xf2f2f2f2f2f2f2f2, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000],hint 6 0xe3f8be2b3ccef32caf11bfafcbbae7b86dcb66d8b46d0b1ea4a7e9da6a9677dc16e1946096f4c0c12bca526c7b1a003 0x24a7c930a88c3096cc2a42a325125131931958285604124e31731641048a8124897521c731771249c7124960c67830c56030c43c30cb2c30cb2c300348a34a3494494573173144d6565208683⟩,
  ⟨30,7,[0x2222222222222222, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xff22ff22ff22ff22, 0xffff0000ffff0000, 0xffffffff00000000],hint 6 0xe3b8de333cccb2bca71cc5711bfafbb72d9b62ceb32c7ab2a4a7e9da728e929df705b365182304af2809b1ec6d1a003 0x20980824c24c2242236098980884c82cb4037d040121075041d5d04174898524886d279249e79249834d41710770410664410f3c410f3c41052840044893093084484555185a55d05d038e684⟩,
  ⟨30,7,[0x2222222222222222, 0x4444444444444444, 0xaaaaaaaaaaaaaaaa, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000],hint 6 0xf1bbdcf332cc72bca71cc370cc2f09c1704bfafcbdaeeb9ed9b62d7b56d4b4ac6b16b4a929fa7699a5a8ea124a91a3d849df705946096f5a9304a1232a49b1ec781a065170571482b05c0d02003 0x4ed4f9514e6de1351355e575514d5eed551555d56a4d3a9db154d57d47f478bd14ddf79f7d37e9749a534df75fa5535fa8d7d5569aa9014031584c54c005800130238038d388080002a01954266a60054002900f7c13e93807c0856876514d96ea152186086e4d3ba0be14e1d95421a90855576aaab9f6a1a5a85f7eea69f653210001541735b2cd4285585153168827a1320580516a15c55b72a1c55451691527d14a91857c5f26ac50009265c5845⟩,
  ⟨30,7,[0x2222222222222222, 0x4444444444444444, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000],hint 6 0x3c8eef4acf331caf29c6f14c470dc3305c12ffbeef6bbae7b7edcb66d8b52d2b22c6b16b4a929fa769ca6a99a5a468f61477dc16e1b365182525384a123304af2a4a52809b1ec681482b05c0d02003 0x4ae4ba4d3eaee524d259c5b44d3d1ced64d659b5a9492a5bb564967d37f3707cd3e1f71f7d27e86c6a1249f6dfa162dfa4b7d65a8a680170324c4c97c404c00200234838e088048001601aa42696640a4001f00fa013df380a002172364f5d973484c822022b4aaae030848821621ea5d796288a4821f215a1455f248a08f67848000b13b375d1dd3f2c5ecdd242c810b124b7820b29b2f596be9c2c596be896c7dfb28a2f7dffa616c00092662c208⟩,
  ⟨30,7,[0x2222222222222222, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xfafafafafafafafa, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000],hint 6 0x38be2b58cf33bccb2bbfafcbbaecb9ee1b66d8b46d0b1ea4a7e9da59df735c16e1b3651824c12826c7b1a052 0x1877062877ca28664a1e21e118f18f29629650279404118d29529438e4077504066d014529569041a69041424c1c924b60924a5490c35092042501cc1cc18f18f54a54a8115135120005c9⟩,
  ⟨30,7,[0x2222222222222222, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffaaffaaffaaffaa, 0xffff0000ffff0000, 0xffffffff00000000],hint 6 0xe378cd5f3cccb2bca728c7315bfafbb66d8b3accb1eaca929fa769ca6a4a919df705946089b1ec6d1a052 0x1467051881881611605467950854051c73436cd34114d60d35850d3543c674f3c55cf64f3d964f3d528a35430868c30e14c10454c2cc35430930f18818814e14e7d155355250d50d00058c⟩,
  ⟨30,7,[0xc0c0c0c0c0c0c0c, 0x2222222222222222, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000],hint 6 0x38be2b6bcf33bccb2bc46febf2eeb9ee1b72d9b62d1b42c7a929fa769aa5a4a77dc16e1946096f4c128304af2949b1ec68 0x24a80930a8cc30970c5c189700024f3183174ca8534c97931c73183935c215f0821190820d00822cb08609328d28d25225260c60c5d65d52086c294a98a48948968c68c45175308b08b914⟩,
  ⟨30,7,[0xcc00cc00cc00cc, 0x2222222222222222, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000],hint 6 0x38de336acf332caf29c7315c46feb9edcb66d8b3accb1eaca929fa769ca3a4a919df705b3651824c0c12bca026c7b1b468 0x2098486498d90485084428114402116114584c98934c87131d364e39160319d0c315a0c34100c310a0cd0d324c24c2122126576566116113cf6c33093099489882cb7917917d30d00d0915⟩,
  ⟨30,7,[0x2222222222222222, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xfff0fff0fff0fff0, 0xffff0000ffff0000, 0xffffffff00000000],hint 6 0x38de338be2b32caf29c7311bfafcbc6eeb9edcb66d8b4ad1b42ceb32afa929fa769ca66969725b929df705b8651824c0c12bc9b14803 0x1879461e81e71aa1a92475092467896c944f91144e1916912517d31e64d31a14d94d33451498cb2d18021220820dc0822080824100822080800931ca1ca1921923165995495895d1611041742⟩
]

def nodeBlock45 : Array Node := #[
  ⟨30,6,[0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xddd0ddd0ddd0ddd0, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000],hint 6 0x33ccaf29c4709bbadcb66d8b56a4a7e9da7284929df705b8651825bd6a4c0c12bc9b1ec781a06514803 0x30d7cc3cd80f3cc6cf5057945033143d43d840d40d54c54c3d93d95185180447010425c104948105128104b5811887461876861934c618e38618e386000056⟩,
  ⟨30,6,[0x2222222222222222, 0xaaaaaaaaaaaaaaaa, 0xccc0ccc0ccc0ccc0, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000],hint 6 0xcf332caf29c2704bfaeeb9ed9b62d5ad2a4a769ca124a8f5c16e1946096f5a9304a1231ec781a0651482b05c03 0x34e84d40e8d040d71054781554535541541958e89658d75628a41a4925590027800015c001444000f2000093c00df1830d81030d36830cb6433036c0⟩,
  ⟨30,8,[0x4444444444444444, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000],hint 7 0x3adeb3aaea366d4f4acf331caf29c6f0dc330bc26ffbeef6bbae7b66d8b5ed5b46d0b3accb2ac8b1ec6a929fa7699a5a8ea126a9a26799a6598a5f94e52885ee77dc1651825bd6a525382a49b1ec781a0651705714803 0x823990e82f078f82f193b823878e824101082e078f82e103d82407908440f9084bc70e84bcfb1844071082847a182dd00782dc7ba8285021848472184b8f8584b870e8484fa186b88098885789388481086b97ae820488182d878682d88b58204781840510184b470484b512c840470186048013679783487881d860578188050813435702483508c880570182c07b082e488b82e47be82c08b084e470a84c110a84c070e84e512286c17b048cc81032cd7b486c081088cd72648c10a130c172e88cd0a14854a00484c08148c09308294891830478f8304891829478f849d122850870e8509122849c70e86a08102ea57af48a481086a17af88a90a12cad72e48ad0a188a972e48fc923829408149009888295808⟩,
  ⟨30,7,[0x404040404040404, 0x4444444444444444, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000],hint 6 0x3adea7a8d2b3ccef2bc26ffbeeeeb9ee1b66d8b56d1b42c8b1ea4a7e9da5a849866077dc16e1946096a525381ec781a0651705714803 0x2cc90b38c98e38b80e70795c1452d339d39c0468c10446c10434810422817c99df2082d57ce88e6187210017cf30f3152d52ce74e76a69c58134da0ca4c54b54b78e78e51444141f657⟩,
  ⟨30,6,[0x4444444444444444, 0xaeaeaeaeaeaeaeae, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000],hint 6 0x34acf33bcaf1bc4709bfeeeb9edcb66d8b56c8b1ea4a769aa5a84705b8651825a9494e0c12bca52809b1ec781a0651705714803 0x4119504d19d34d081370799c1454154dd4dc0468810446c10435010423c17cea1f34d4247d385369a5d700005f22330821e2c821628821c248601648212⟩,
  ⟨30,6,[0x4444444444444444, 0xaaaaaaaaaaaaaaaa, 0xc8c8c8c8c8c8c8c8, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000],hint 6 0x350d2b3ccef2bc2701bfefcbeeeeb9ed9b62d5b22c7a929fa5a84961c16e1946096a525381ec781a0651705714803 0x2cc80b38c88e38b68e5c78571452d13983970467c10445810434010422816498d92082d264e74e5555db00005970c91c3cb48b3983987177974c150134d⟩,
  ⟨30,7,[0x44004400440044, 0x4444444444444444, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000],hint 6 0x3aceafaad2b3ccaf29c5709bfee7b66d8b56ceb36ccb22c7ab2a4a7e9da72849926377dc1651825a9494e07b1e06d1a0651705714803 0x30d94c7cd99f18c5cc50891450531479451e0478810447410434810422c180a9e024931581b86065479400180f34f35531532a71f51e51e5814d33cd3cda0ca4c38e8d48d4441420698⟩,
  ⟨30,6,[0x4444444444444444, 0xaaeeaaeeaaeeaaee, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000],hint 6 0x34acf32bca711c26e7b72d9b62d5b36c8b1eaca929fa769ca11c16cd946096a52538304af294a026c7b1e06d1a0651705714803 0x4529918129e01916915c89575c54577d75df0478c104478104354104240188fa2238e45889d5147177d70000622643492613092602c92532896416c9256⟩,
  ⟨30,6,[0x4444444444444444, 0xaaaaaaaaaaaaaaaa, 0xcc88cc88cc88cc88, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000],hint 6 0x34acf334caf29c7309bfee7b66d8b56cdb22c7ab2a4a7e9da728477d946096a52d494e07b1e06d1a0651705714803 0x34e84d6ce8db18d54d48881248535269249a04778104464104340104230170a91c24935371875c5d269200005c2ce3ce4cd4cd7db89b49a49a501581451⟩,
  ⟨30,7,[0x4444444444444444, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xfafafafafafafafa, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000],hint 6 0x3adea7a8daf4acf33bcaf09c02ffbeeeeb9ee1b66d8b56d1b42c6a929fa7696a126177dc16e1946096a525384a07b1e0681945c15c52 0x2cc8cb38c94e38b78e3293282d42d439c39c68691a1042d239b39a4d300588000364000244058001000128074999d2082d474e80e7dd69d84701d3cc3cc50b50b39b39b5ea9d75da61a54034d⟩,
  ⟨30,7,[0x4444444444444444, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffaaffaaffaaffaa, 0xffff0000ffff0000, 0xffffffff00000000],hint 6 0x3aceafaadab4fcf32bca715c26ffbeee7b66d8b56ceb32c6ab2a4a7e9da728499256919df705946096a1ec781b4681945c15c52 0x24a88928c28c2672666ca8db1495492cb4878524842528124a069249a0067c000364058000f00240000120074c91d24e25371c6dd79a49a48d01d30a30a4c94c95e89575db61b49a49a500451⟩,
  ⟨30,7,[0xc0c0c0c0c0c0c0c, 0x4444444444444444, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000],hint 6 0x3adea7a8d634acf33bcaeffbeeeeb9ee1b66d8b46d0b22c6aa2a4a7e9da5a6077dc1651825e96f525384a09b1ec6815c52 0x28b7ca30b84c30a70c60381808228f31931820b34820a4482094c804861b1e26c618a45b31e31555874521b34b34b44a44a3193195985d848810490b94b44a44a68c68c41000051b39b5a35a6⟩
]

def nodeBlock46 : Array Node := #[
  ⟨30,7,[0xcc00cc00cc00cc, 0x4444444444444444, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000],hint 6 0x3aceafaad5f4acf32bca715bfee7b66d8b3acdb32c8b1aacaa6a4a7e9da528e98e4677dc1651825253826c7b1b46817052 0x2098086c985b0c85084047d040221069041a3892ce38844e04e6ce3d339c1e270618845c61d71641a40c39c2c92c94484485db65b41a41a48e1452c92c990894828a79079000055c35c5e35e6⟩,
  ⟨30,7,[0x4444444444444444, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xfff0fff0fff0fff0, 0xffff0000ffff0000, 0xffffffff00000000],hint 6 0x3abeaba9ea34acaf29c26ffbeef1bbae7b66d8b56d1b42ceb32c6abea8a929fa7699a5a8e9b26b77dc1651825bd494e09b1e06514803 0x20994826826722a22928954a2887ca74a45091144f2117112918010e304109b0411c70413940411c705e1a678514848d79e59e2a22a145e44005e2c92c948848859860c29829745a4594c1104⟩,
  ⟨30,6,[0x4440444044404440, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000],hint 6 0x33ccaf29c4709bfeeeb9edcb66d8b56a4a7e9da11df705b8651825a8c12bca52809b1ec781a0651705714803 0x38f84e44f89144e7115078145053944544580467810445c10434c104234120c7c820b68820a74820960800005b48f48f54e54e459459518518581408⟩,
  ⟨30,6,[0x4444444444444444, 0x5550555055505550, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000],hint 6 0xd2b39caf29c4704bfeeeb9edcb3acdb22b4a929fa7684705b8651825a9494e128304af294a026c2e0ac1a05c0d02003 0x4118d04d19134d07935468955444154d54d90058000036000025000013c076539d59034d4df4dd5595597403001e12c71dc2871da2471d92075c01d26c7⟩,
  ⟨30,8,[0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xfafafafafafafafa, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000],hint 7 0x3afe4772dc36ed2b3ccef31caf1bc370cc2f09c0affbf2f6bbaecb9ee1b66d8b5ed5b46d0b3accb2ac9b1ec3a929fa7699a5a8ea12709ba6595222855df705b86cd946096f5a9494e12826c7b1e0681945c15c52 0x7c3580d7ce870e7ce98397c3470d7c44e117cdc70e7cdce3c7c447117e44d917eac68d7eacdaf7e446917c8470e7cf93a27cf870e7c85f217e8c68d7efcf1e7efc68d7e8cf1e80908914e9562c4e94891809162c7ca872a7cd8e067cd873b7ca8e2a7ed86847ea8d847ea868d7ed8d9b80a88914c995ab4c9c89180a95aa4c9e09d7ca909d7c009007cd47057cd49347c007007e00f007ea46837ea4f287e0068080008804069582406889980015804ec4c314e013804e013804ec4bb14c013004c315014c3138b4c015007c407107ce090a7ce073d7c409107e406907eb4f097eb46ae7e40f10804159040cc89140cd5b280408904c9a1077c410874c9952a4c413904c9930f2cb40002a40f88284000026b4f9f⟩,
  ⟨30,7,[0xaaaaaaaaaaaaaaaa, 0xc8c8c8c8c8c8c8c8, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000],hint 6 0x3b3eb78ad7b58d4f52d434acf33bcc72bc6f0dc3301bfefcbeef6bbaecb9ed9b62d1b42ceb32cbb2ac9b22c7b0ec2a7e9da66969be619622377dc16e1b3651825253826c7b1a052 0x1a41ad1c7b64b061c62912aa1c7a91bca1ca2902a01868108ca18a7c77e9442a47b9f45fa4605f4017c61a94107ca2b482078a29f81f98b9b21c7c8bc661e65133661869934d418654a2a682098a2958209b49b47dfd1ea267df58b2d81c760b2d61c765465a18668f6991866ca29c82070a29b820e344b47d2d1e7b57dfdde01698024726b2c5ac7c092c92462614c48468894c926026528a9609c928995f5c978925f225d0884e84998924c2619a185d0c9d8325d261ce1⟩,
  ⟨30,6,[0xaaaaaaaaaaaaaaaa, 0xc8c8c8c8c8c8c8c8, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffffc8c8ffffc8c8, 0xffffffff00000000],hint 5 0x380d434ad1b3ccef2bc06ffbf2e7b72d9b62d5b2ac8a7e96961df705b86cd94609494e07b1b468 0x29b0549b490a52588b31000ac4c931a9bb5595a54c932ac6f151946795324cb71f4610413881a10d426c8720e7a21149cd14⟩,
  ⟨30,7,[0x3232323232323232, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000],hint 6 0xecf8fe2b6bd7b53d4b50cf331caf29c5311c370cbf2f6bbae7b7edcb66d8b4ad1b42ceb32cbb2ac9b1ec6b0ec2a7e9da729aa66969624a77dc16e1b365182304af2a4a52809b1ec6814803 0x2aa2b22cbcaac4a2ca3933ad2cbb53cce2ce3923a528a952a4e28e58b5ac4c3b0bc164d658a5a448290a29649690e1d694758e3a4964acfaf52cbd4fd2b2eb61746b28aad75d828a64e3ab965ace399965ad643a910e965ab92410b12f3c9bcbb843c410a1275c89ca9845c412511538656550438412410d585364304584a1a004ac0123128ae86cb2dc3cf70b2db3cf74a29e5d778a29d5d77e596038e82595f38ede493a596ea493b596e2205bac1da8a21104868a39104⟩,
  ⟨30,8,[0xa0a0a0a0a0a0a0a, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000],hint 6 0x393e4b91dbb5ad2b48cf331caf29c6f15c370bc2702bfef6bbaecb9ed9b62d7b56d4b46d0b3accb2ac7b1ac3a929fa7699a5a8ea12739c9df705b8651825bd494e128314a92809b1e06517052 0xe8ca8ceb434deb4ab3e8c34ce8f58feaf34deaf5b5e8f34fecf54fee630cee6569ecf30fe97357eb0587eb0372e97597ed7317ef6555ef630ced7557f303c68179868173cff309a6e80400eae343eae42de80340ec0600ee4302ee4623ec0300f003c06949816943d3f009808005c080b84b80b5cb800800e8e34eeb140aeb1377e8e40eece30eee7609ee7328ece60ef0e98e6ac3cf6ac9abf0e3ce82080580e84e8205d76e700088e6486ce0008a7659e9c596eba34deba596e9c34dedd555efb30cefb555edd30cf1e9a685f3cf85f9a6f1e3cf839865e9c5d78520008612cb8510008612cb838804e9c384⟩,
  ⟨30,7,[0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xcececececececece, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000],hint 6 0xecfa8e3f6bd9b5ed233ccc72bca715c5311c370bc26f6bbae7b7edcb66d8b5ed5b52d2b46d0b3accb2ecab26c7b0e9fa769ca6a99a5a8ea11df705b86cd946096f314c12bca9294a026c781945c15c52 0x36e37738edeed8d38d45647138ec56e1139145546934da55b5135164e67458bd0ed5959964d679555e4d359559d11219a48651474a6971249d38e75249c38e79555f34d7d555e34d8114619218514606e0fd967c8e3f1967af28012030384c12bc038001a0273439da980340011014a425114c0a4001903c8c1f19640f008fd30070014e17348accec8548514d16b689acda856851691584476295c544517c1506464233c5645b3eb0588517b16c8acb0000590514002c96c⟩,
  ⟨30,7,[0xaaaaaaaaaaaaaaaa, 0xc4c4c4c4c4c4c4c4, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000],hint 6 0xecfadea366d7b58d2b3ccc72bca71bc370cc2f09bfefbbdaeebb2e7b66d8b5ed5b52d1b42ceb32cbb2ac9b1e9fa7699a5a8ea11df705b8651825bd6a525382a4a026c7b1e0681945c14803 0x3a93b33cfce9c8e3ce45646f3cfbd6d113d145546538e955a113915cf5ee586b8fc575975ce5e454490e3975579112579495d146496405206d3c5b52b013c10580633838d88813810510549425114c194105707a924e9730190165249a3cf6924993cf6d861c38e71861b38e75145e96579145d965ed75fa924e975f7924da035904140f43048bc0fd5049040e42660a98e9d061042542a451aa5ad0450aa42105c842442a5d79810108404010668669b99907d04381e67c7⟩,
  ⟨30,8,[0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffaaffaaffaaffaa, 0xffff0000ffff0000, 0xffffffff00000000],hint 7 0x3b6e7b7bde773cf331caf29ca325c7315c370cc2f09c0afbbdad9b62d7b56d1b42ceb32cbb2ac7b0eaca929fa769ca6a99a5a8ea12779d66695a5591a24859df705946096f5a89b1ec781b4681945c15c52 0x7a2d68b7ae860c7ae96b97a2c60b7a8860c7af470e7af460c7a8870e7c8c58b7cf93247cf858b7c8df237ab0d2c7acc60c7accd3b7ab062c7cccc857cb058b7cb0ca07ccc58b4a99f8d7ab110d7a7461d7ac8d077ac86387a74d1d7c7459d7cacc847cac58b7c74c9d4cd1434787539d4c7531d78d13b44aad2ab4a7561d4a7531d4aad62b7a007007ac46067ac47307a006007c00f007ca85837ca8f297c005804cd4b354c013004c013004cd4ab54a012804a616024a613174a016007800e8042295814228e8978015807a7061c7ad870e7ad86377a7071c7c7059c7cb8f137cb858b7c70f1c4a960087a711084a9562c4a7131c4a9529b787159c42bce9d42bd5ab7870e9c28b80002470f9120700001eb8f9f⟩
]

def nodeBlock47 : Array Node := #[
  ⟨30,7,[0xaaaaaaaaaaaaaaaa, 0xcc88cc88cc88cc88, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000],hint 6 0x3b8eb38ad8f57d4f4ecf334cc72bca728c731bc370cbdae7b66d8b46d0b3accb2ecab26c7b12bbab29fa769ca6a99a5a769922577dc16518252d494e09b1ec6d1a052 0x22322b249ae3a88248850865249950b6126194f0a120884f5652084c94e4403909a534134c84e03c18082133d38308138534dd4e086058b1e72499cb2d62499d452e208b945272089f09f0861c1db278615d34e78209d34d782061661924964e65824969451b2086d451a208d302b084ac1d7718617934df8207d34de820cdd0189c04894a62c6989a122d24884a25058882125128a18927524a1462c114a04a24d38a08124d288d8929d248c4a29e289c112c8449c4a2be2⟩,
  ⟨30,6,[0xaaaaaaaaaaaaaaaa, 0xcc88cc88cc88cc88, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffffcc88cc88],hint 5 0x389d133ccd31cc4709b9ed9b62c7ab29fa769ca69df6518252d381b468 0x229447168e091646a52d480896a52d194c55114493a6e4b52d61544512aeb392d4b6107a10f408887a0e7425a87a10f8c50f⟩,
  ⟨30,7,[0x3322332233223322, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000],hint 6 0xee38ee2b6ad8f53d3b3ccc72bca71cc5311c370cbeef6bbae7b7edcb66d8b4ad1b42ceb32cbb2ac9b1ec6b12bba7e9da729aa669677dc16e1b36518252d30304af2a4a52809b1ec6814803 0x32a33334dceac8c34c41342d34db53d1035041242530c952a5031058d5ac4c3b0dc564d658c5a448290c3164969101d69475904249646112f034dc1145834dc175f530cd575f030cc102ba94ae904309656565b0924c1659992410d12f449bcdb8444410c1275c89cc9845c412511540656550440412410f5853e4384584ada004c0012312bc2b6cd35c45170d35b45174c31e5d778c31d5d7de597a410ea597b4108649225968a4921596e2005bc01daba1f1047ebaf9104⟩,
  ⟨30,8,[0xaa00aa00aa00aa, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000],hint 6 0x39fe7b94de762d2744cc72bca728c970cc2f09c0afbbdaeeb86d9b62d7b56d4b46d0b3accb2ac7b1ac3a929fa769ca6696a3a7a9e656919df705946096f5a8a92949b1ec781a06515c52 0xe4ba4be7330ce73a72e4b30be4d54de7530ce75574e4d30de8d50dea72cbea7528e8d2cde57317e6e545e6e331e57557e972d7ea5503ea52cbe975177a53487979c879734d7a59e5e40380e6d304e6d3ace40300e80600ea42c2ea4623e802c07803407937d3793353780780e005c068a94168a5c9e00940e56316e6f38ee6f330e56396e962d6eaa610eaa2cbe9661679e7877967d679e34de169566ab5d76ab965e165d66ea00089664f6d60008aa659e5c30ce7938ee7930ce5c38ee9d2cbeba514eba2cbe9d5147b77e6e5c34de209657df5d77e1965e205d77d20007df4d37d10007df4d37b6786e5c586⟩,
  ⟨30,7,[0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xcceecceecceeccee, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000],hint 7 0x3b8ea38edab66d8f49d1331caf29c5311c330bc26fbbdaf0bbae7b86dfb72d9b62d7b56d4b4ad1b42ceb32cbb2ac9b1ec4a7e9da729aa6696a39df705b86cd946096f5a8c12bca9294a026c7b1e0681945c15c52 0x7b11ee881074c5c8f203c99726f0810785dd93204c99626b478f5a597931e4cd1034d4b866a41c1a2e68d0f34a4b04523c79a2c69493146968a344c9a95aa4e902078b973c4081d2e5cf8f1e80b16403c79f2c5a11326fd1227e4c9bd7ea919a34912a44868d23388c01400d08056851980200001b00a0783506d3801e0001300fd1027e4c9807e0001a00394811c6868052011402a00e800e403b72831b906c1ca070e3c3ac362d60f561cd870efc3992624ca2301c9870ea43923420929221cd076505707421c3be0ec90b264000074a1c38000c9330⟩,
  ⟨30,7,[0xaaaaaaaaaaaaaaaa, 0xcc44cc44cc44cc44, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000],hint 6 0x3b8eb3a8d9b63d5f3ccc72bca728c6f0dc330bc26f6bbae7b66d8b5ed5b52d1b42ceb32cbb2ac9b1e9fa769ca6696a3a8477dc1651825bd6a525382a4a526c7b1e0681945714803 0x3a83b13cfc68c0e3ce41542c3cfb15c903d041442538e9549d03905cf5eb546acfbd75575ce5e450490e3975179102579495d042496405106a3c5a91a413c10580633838d8881381050077965dd048194105704d90235730190165145a3cf6914593cf6d861c38e71861b38ee10437965dd04349657d75e09248175df924cde4d904158f5ad44bb4fb9645658e5a660a98e3966169a52164085a55a64105a45a65d79a49165d69810168405810668669b69967565b51e6747⟩,
  ⟨30,8,[0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xfcfcfcfcfcfcfcfc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000],hint 6 0x3b3e5f77ddb75d233cccb31caf29c7315c5311c3703bfafbbdaeeb9edfb72d9b62d2b46d0b3accb2ac7b1ac3aa2a4a7e9da729aa66969f67c77dc16e1b3651825bd6a4c128314c12bca9294a026c52 0xe8cacceb634deb6af5e8c34ce90550eaf34deaf578e90350ed0510ee630cee652aed0310e9e34deba555eba34de9e555edf30cefb514efb30cedf514f204108e19a68e1410f209a6e98358eb2547eb2374e98558ed8318ef9514ef930ced8518f32404898984898410f329a68a3f65e98798e8b44beb334deb3477e8b34becb64beee30ceee66decb30bf0b40b71a98971a41bf0b98b8a2f80e8b7808a261888b8cb8a288ae81341eb1446eb1370e81441ec1301ee8645ee8327ec1641f01981717403717996f014018ec4ec8c18c18c18c18ec4ac88188188f60288f8ce8816017692c89016819012c176969a⟩,
  ⟨30,7,[0xa8a8a8a8a8a8a8a8, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000],hint 6 0xebfa8e3f5ad6353d3f48cf332cc72bca725c7315c3700bfafcbeef6bbad9b62d4b4ad1b42ceb36ccb2ecab26c7b0ea8a929fa7699a5a56929df705946096f5a930314a926c52 0x1e21ed208b62b0720724e2672089cebc920924d2601c780d8491c93c83e8383a08acf38f3c73f034dc071cf34fa0908f8023c926882018a1a9208a4ab862061901a41c79109461c618919180444948680690f2c670618f164cc58c88ea28aa88c632a3a871e340c8c71ea4104e06632498e08132498f38f33cfcdc9a33cf8c619d4517461a345150821528a54821428a5871d734d5c71d634d61361a24969e698249df37f33cfcdc7343cfd8601b4406c61b2451d5c0548c1⟩,
  ⟨30,7,[0x5454545454545454, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000],hint 6 0x3afeb7a8daf5ad4f4fcf331caf29c970dc330bc26fbbdaeeb66d8b5ed5b4ad1b42ceb36ccb2ecab26c8b1ec3a929fa7699a5a8ea125677dc1651825bd6a2a49b1ec781a0651705714803 0x32933234dca9c4c34c3943ae34db94cce34e3933a730c9d3a0e30e54d56d507b4dc1551554c5664c598c3154d598e2559c954e3a69e604f06c346b0fac134105606530495690130104e0529c348e4419c105504b9822d5281981a8daaf3cfbcdd2a3eabcc32a590a8c32f5966277ea38eaa79d838eaa66b9555e669aa555a810235c08c106a5d764f3db34d6cf3d934d71659d30c75659c30c78e3a09e780e39e9e7d955799a6e5557a9a6d575e10418575f8041de2219a88⟩,
  ⟨30,8,[0xc0c0c0c0c0c0c0c, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000],hint 6 0x39be6797dd75ecf33bccb31caf1cc5311c370cc0efebdaeeb9ee1b7edcb66d8b46d0b3accb2ac9b1ec3aa2a4a7e9da729aa6696a067f99e5789a1777dc16e1946096f4c128304af2949b1ec6815c52 0xf0bb4bf3630cf36b75f0b30bf0e5cef3130cf315f9f0e30ef4e58ef672cbf675acf4e2cef26326f305c3f30338f265e6f702c2f66582f662cbf70596fa638e9249e792538efa69e6f0a3caf3430cf343f7f0a30af4a6caf6f2cbf6f6eef4a2caf8a38a79c9c979c39df8a9ca92490190a94a9249a6f04304f333c7f33332f043c4f442c4f696c6f692e8f446c4f849c47993857999d8f8438490498490d94d90d98d9049044eb28848470444428442b71cf1ff1ff3c30cf3c960f1f30cf616dbf7d2cbf7d6dbf612cbfa2aaa96338e963aaafa238e93b95af1f99a93a900f1f28095510496534d95410496534d⟩,
  ⟨30,7,[0xaaaaaaaaaaaaaaaa, 0xaeaeaeaeaeaeaeae, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000],hint 6 0xebfade2b6bd9b5acf33bcc72bc5311c370cc2f09bdaeeb7edcb66d8b5ed5b46d0b3accb2ecab26c7b0aa4a7e9da729aa6696a3a84a0260861df705b8651825bd6a304af294a026c7b1e0681945c15c52 0x3af3b73cfdefd8e3ce4594733cfcd9e513d145846b38ead8b91391a8fab2646c8fe2a66ac8e12a604a8e3b2618a9147caeb9d146aaea0120313c5c52c003c001d029383a5da00380011017ac25d1580ac003c00da81367300a8080f3e149284f3e049288e3a35638ce3a27e292bae545196bae4451feaabc9e7f2a73af1c98003d79eec002679e1cf1f548bd4fd074871ce1ed74ab4eb077471eb1db4496eb6874471ea1fc9c8f2aa87f075000077871c001379e9fe407807⟩,
  ⟨30,6,[0xaeae0000aeae, 0xaaaaaaaaaaaaaaaa, 0xaeaeaeaeaeaeaeae, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffffffff00000000],hint 6 0xe8346cf33bcaf11c26dcb66d8b56caa929aa5a8477dc1651825a938304af294a026c7b1e06d1a05c15c52 0x40f7d06067984194180056c00024800013403d13d16506506216200150151cb7071c95071c860700701530739d3ce3901104ce0c301701558e1da1ca⟩
]

def nodeBlock48 : Array Node := #[
  ⟨30,7,[0xa2a2a2a2a2a2a2a2, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000],hint 6 0xebf8fe2b66d6b58cf332cc72bca71cc5311c370cbfafcbdaeeb7edcb66d8b52d1b42ceb32cbb2ac9b1ec6aa2a4a7e9da729aa669677dc16e1b3651825bd30304af2a4a526c7b1a05714803 0x32933334dce9c8c34c41342d34db53d5035041242530c952a1031058d5ac4c4b0dc564d658c5a448390c3164969101d69475904249642d12f034dc11d0b34b2d72ea30ca97acb30b2d02d894a61064b94ba9608b9022d62ea92414d16f449bcdb8544514c1675c89cc9855c516515540656550540516417a596ea438558568b00560014b1636186cd35c45170d35b45174c31e5d778c31d5d77e596041082595f410ee493a596ea493759684b2f9618e0b061601da23db145⟩,
  ⟨30,8,[0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffccffccffccffcc, 0xffff0000ffff0000, 0xffffffff00000000],hint 6 0x3b8e877fdfb78d2744cdf32cc72bca714c470cbfafcbdaeeb9ee1b7edcb66d8b4ad1b42ceb32cab1ec6b0ea9a929fa769ca6a99a5a8ea1684a0e4a919df705b86cd94608c12bca9294a026c7b1a052 0xec9b49ef528aef5b74ec9289edf38eefb28aefb38eedf28af20555f3c249f3c555f20249ecd58def928aef95b8ecd28df0d54df2a249f2a56cf0d24d862f67ecd7cded9299ef0582ef02b3ed9599f19259f26541f26249f195598a6926e998d9899899ea68e6866346859a8685934d866aa6ed4394ef728aef73b6ed4294f14694f2e249f2e6aff14254861f80ed47c086134d854894861852e9465475b99075b65ce94994ec3283ef2388ef22b1ec3383f03243f29687f29268f036838ab4eb8838838838838ab46b843843858345858897843343e8398374c64474c98be836437ab50f9436c39435037ab6db⟩,
  ⟨30,7,[0xaa88aa88aa88aa88, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000],hint 6 0xedba8e3b62d5f53d2b49d1332cc72bca71cc6f0cbfefebf2f6bbae7b86d9b62d4b4ad1b42ceb32cbb2ac9b22c7b12a9a929fa7699a5a8ea124a77dc165182525384c0a926c7b1a052 0x22622f249be6b882482902b2249c90c4a24a28f2a32088cf94a20a44946a402a89b514114484613c18482113d184a1118c444a2a18e138b3ac249b0bc0e24e3923a72089d2a0e20eb0a14e70e38a36cd4d39139384c4d150e84e90992b2c7ac9ce42e4ac81a448690822b49293593528ad5ca6428a5615e445192185545190e39f4d37ce3a44d359041824961041624964f3da20868f3d9208e758b528ad5c73628a75575e4517a079d451e0e01b4c06ce3b44d3ddc0d6903⟩,
  ⟨30,7,[0x5544554455445544, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000],hint 6 0x3b6eb3a8dab62d4f4acf331caf29c6f0dc330bc26f6bbae7b66d8b5ed5b4ad1b42ceb32cbb2ac9b22c7b12a4a7e9da6696a3a8477dc1651825bd6a525382a49b1ec781a0651705714803 0x3aa3b23cfcaac4e3ce41542e3cfb95cd03d041442738e9d4a5039058f5ad547b4fc1655658e5a650598e3965169902569c95904269e605106c3c6b11ac13c10570653849579013810500539c34d04819c105604d982356301981a0fa2f44bbcfd28468bce2a85caa0e3af5d7a27a39410e679e84106666e8596a26999596a010236008c106861869145c3cf71145a3cf7575de38e7975dd38ed904399e7e5043a9e78565a29a68965a19a6d5861f0417d8638041de021aa08⟩,
  ⟨30,8,[0xcc00cc00cc00cc, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000],hint 6 0xe8fa1e737ed8f3ccdf32cc72bca715c5311c370cbfafcbdae7b7edcb66d8b46d0b3accb2ecab1ec3ab2a9a929fa769ca6696a3a8aa1e689664a91a27865df705b86cd94608c12bca026c7b1b46817052 0xf89b49fb728afb7b76f89289fa9669fb128afb167afa92a9ff1603fe9249fe961fff1249f9b29bfb0644fb02b5f9b65bfdb25bfe8602fe8249fdb61b92892891ba5b91b95b928a68f97397fb928afb93b8f97297fd7717fee249fee72ffd7257924901917957924a69f576d781da1281d6def57a17f85285fb3388fb32b2f85385fc5245feb707feb26afc5705905a4591a95a91aa5a905905f45a0580c6c680ca0bf456c552c5d14c57454055c53ec75dfa138efbe28afbe38efa128afe2fe2fff249fff963fe224993c94dfa1a4df66d349656db967d34f666db93b900fa15c095614596569a95514596569a⟩,
  ⟨30,7,[0xaaaaaaaaaaaaaaaa, 0xaaeeaaeeaaeeaaee, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000],hint 7 0x3b6eb38adab66d8b3ccc72bca714c470dc330bc26f6b7edcb66d8b5ed5b46d0b3accb2ecab26c7aeeaca929fa769ca6696a3a88a1263869df705b86cd946096f5a8c12bca52809b1ec781b4681945c15c52 0x7b01ee481072c1c0f203d69b5ad0810686dd2d20b5a1a0ab478f5a690341e3ce903accd876641b9d3674e8f3ab0d04583c79d347563d587569d3a9ceac5ab001400c88066451880200001e00ac78356795001e0003d0065682329cb805a0001d00396011c746805801110208cc234640822428920f1e94f1e4a3c7a43c7a02d5af53a77ab49bb7a4d42c58a4e9d52b16283a7530000f8f9f78000263e7c41010d8a0c6c41a88282040f10bcf0b5e3d7083c2042d10f538a7ab56887a2042c1048e8924b08883a20b000020f8810000153e7d3bf3821108⟩,
  ⟨30,6,[0xaaeeaaee, 0xaaaaaaaaaaaaaaaa, 0xaaeeaaeeaaeeaaee, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000],hint 5 0x3a7d133cc4709b72d9b62d5b1eaca929fa76846cd946096a524c12bca52809b1b4681945c15c52 0x2b68d891b1bc63700ec000a00005806c9b2c7b1dbc6f104c13327263230631de601813599b26cb1cc3af1bc41a04eae36cca⟩,
  ⟨30,7,[0xaa22aa22aa22aa22, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000],hint 6 0xedb8ee2b66d8b57cf332cc72bca71cc5311c370cbfafcbdaeeb7edcb66d8b52d1b42ceb32cbb2ac9b1ec6aa6a4a7e9da729aa6696a3a4a77dc16e1b365182304af2a4a026c7b1a05c14803 0x2a92b32cbce9c8a2ca3933ad2cbb53d4e2ce3923a528a952a0e28e58b5ac4c4b0bc564d658a5a448390a29649690e1d694758e3a496444f4702cbc0fd112d145746a28aa97ad1291c0e09194244e47096545645891061665191114b16f3c9bcbb853c514a1675c89ca9855c516517a38eea550538516414d5863643055856910056001511636186cb2dc3cf70b2db3cf74a29e5d778a29d5d7ee597a38eea597738e8649225968a49215967d1479618e1105f601da055b145⟩,
  ⟨30,8,[0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xfff0fff0fff0fff0, 0xffff0000ffff0000, 0xffffffff00000000],hint 6 0x3bae9b87e1731cbf2bca714c470bc26f6bcaf1bbae7b7edcb66d8b5ed5b46d0b3accb2ecab26c7abea8a929fa769ca6696a4e90a3a8da326a96a4d86ddf705b8651825bcc12bc9b1e06514803 0xe48c08e78249e78c36e48248e5e249e798dfe79249e5ee5eea0208eba8e1eba208ea0ea0e4b5cbe79249e795dde4b24be8b58beaf208eaf5ade8b20b8a4ee9e4b78be59259e775d7e77275e595d9e99219eba596eba208e995998a2f28e597998a22cb8999198a28aee41301e72243e72331e41241e81681ea7202ea76a6e812018c15418c78c78c78c78c15018812c18938d38932dc881881901641907947907647901901e44244e74306e74273e44304e84204eab685eab22ae846848c44848ca8ca8ca8ca8c44448848848982d88988d88842c490490490a64a90a94a90464442c0403c46c038404136c6db⟩,
  ⟨30,7,[0xaaa0aaa0aaa0aaa0, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000],hint 6 0xedbafe4f62d735bd6b49d2344cc72bca715c5311c2f09bdaeeb86dfb72d9b62d7b56d4b4ad1b42ceb32cbb2ac9b1ec6aa2a4a7e9da6a99a5a8e77dc16e1b3651825bcc5304af2a49b1e06514803 0x2ab2b32cbcebc8a2ca3923b62cbd92d0e2ce3913a928aa51a8e28e50b530488c0bc5449450a535451d4a294454c0e154a4550e3b0a6904f06d2c3b4fb012c10550642829158c128104e05079040e5c1e01054049809254241e4110b12f3c7bcbb843c410a128546a0a9c454413813838ee1e4c4384139139514e6030450460100458010106259664b2da3cf68b2d93cf6ca29c55570a29b555f789b838ee397fa38ef3995d514778777514609261041849262041ede359104⟩,
  ⟨30,7,[0x5550555055505550, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000],hint 6 0x3b6ec7b0ebf72d8b5acf331caf29c5311c370cc2f09bdaeeb7edcb66d8b5ed5b4aceb32cbb2ac9b1ea4a7e9da6696a3e8ea126c9ae1d77dc16e1946096f5a8c12bca52809b1ec781a0651705714803 0x3ed3f6410dadd4f40f49b4b1410c5bdd241249a4a93cfa5ab123d27107306c7c10d1c6dc70f728685a0f3dc69ca1249ca5c7124a8a6805306f406bd3b8140105d0673c49dd9813c1052058a436125c1a4105c04ea0239c341a012102334cccd0c884c820f22b74bacfa8874822923c48af29a4848822823d709f68a0870858100878020105479e7d34e04108134df41085d7623cf89d7613cfe524bca69f124bea69e1c723a288dc73ba2865e7a504195e795041ea445f208⟩,
  ⟨30,6,[0x888c888c888c888c, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000],hint 6 0xcf332caf29c5711bfefebbae7b86dcb66d8b42ccb2ecab26c7a929d929c16e19460930304af294a026c7b1a052 0x24a84930a8cc3096cc38280e38124e30e3163ca88f3c970f20831734d3960c77830c66030c57430c45836830cf40a44a4894c950c64c54e7ce0000cb0da⟩
]

def nodeBlock49 : Array Node := #[
  ⟨30,7,[0xaaaaaaaaaaaaaaaa, 0xccc0ccc0ccc0ccc0, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000],hint 6 0x3b8ecf9bd8f60d7f5ecf331caf29c5311c370cc2f09bdaeeb9edfb72d9b62d7b56d4b3accb2ecab26c7a7e9da7299a5a91a126b9721e77dc16e1946096f5a8c12bc9b1ec781a06514803 0x2e92f230cca9c4b30b3963ad30cb56cce30e3953a42cb915a0e2ce60c62c585b0cc1859860b6235438cb2d85588ce39891860e3a392304f06b304acfa813010590622c28998412c104e075924d4e4c19010580768e3d982418c168f3db30c6cf3da30c71965d2cb75965c2cbe8e3b5924d4e3b7924e5861e8e37986348e3e1f29a04118c1af3c8bccb863c618b1a664798b9466461a41973975e45c63861a318d60d3633466069c100644018106742719218d80d354346806⟩,
  ⟨30,6,[0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xeeeaeeeaeeeaeeea, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000],hint 6 0xcf32bca728c5709bbaecb86d8b56d0b3accb2ecab26c7aaaa4a769ca6a8477dcd705b86cd946096a26c7b1e0681945c15c52 0x24a98934a9cd34984d4c69534c425335335e29729625925835f35a4e34dc00588000374000240000120050001b30f90c30e80c31245148c2cb1c700c015⟩,
  ⟨30,7,[0x3330333033303330, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000],hint 7 0x3b8ed7b4ecf77d8f5ed2748d1331caf29c5714c470bc26f6bbae7b86dfb72d9b62d7b56d4b4ad1b42ceb32cbb2ac9b1ec6a7e9da729aa669677dc16e1b3651825bcc5304af2a4a52809b1e0651705714803 0x72e1cd878f6cb9a8e1e3891524e478f7255b921e4891424ac70e56516921c48c0f30cca8c663da182a60c0e30e0a14703871828619921261589304893356ac09302c0785604d7811e0409902987044c652811c0409202f90037c489017c0409802fd1027e60c017e0430f0cc898b643d886261830e0ca8c8a5439486321833e0c5c9082e80b06241833f0c44c072288806301960100191800c040ac34b0d8f1e70993383c79b264ce8e1c78c993c3871d3265dbe50f89127cfd0c02449d3f4e7cc183ef8fbd3061e201a6c08148b16230c18d2c588c306⟩
]

def nodeGet (i : Nat) : Option Node :=
  if i < 300 then
    if i < 144 then
      if i < 72 then
        if i < 36 then
          if i < 12 then
            nodeBlock0[(i-0)]?
          else
            if i < 24 then
              nodeBlock1[(i-12)]?
            else
              nodeBlock2[(i-24)]?
        else
          if i < 48 then
            nodeBlock3[(i-36)]?
          else
            if i < 60 then
              nodeBlock4[(i-48)]?
            else
              nodeBlock5[(i-60)]?
      else
        if i < 108 then
          if i < 84 then
            nodeBlock6[(i-72)]?
          else
            if i < 96 then
              nodeBlock7[(i-84)]?
            else
              nodeBlock8[(i-96)]?
        else
          if i < 120 then
            nodeBlock9[(i-108)]?
          else
            if i < 132 then
              nodeBlock10[(i-120)]?
            else
              nodeBlock11[(i-132)]?
    else
      if i < 216 then
        if i < 180 then
          if i < 156 then
            nodeBlock12[(i-144)]?
          else
            if i < 168 then
              nodeBlock13[(i-156)]?
            else
              nodeBlock14[(i-168)]?
        else
          if i < 192 then
            nodeBlock15[(i-180)]?
          else
            if i < 204 then
              nodeBlock16[(i-192)]?
            else
              nodeBlock17[(i-204)]?
      else
        if i < 252 then
          if i < 228 then
            nodeBlock18[(i-216)]?
          else
            if i < 240 then
              nodeBlock19[(i-228)]?
            else
              nodeBlock20[(i-240)]?
        else
          if i < 276 then
            if i < 264 then
              nodeBlock21[(i-252)]?
            else
              nodeBlock22[(i-264)]?
          else
            if i < 288 then
              nodeBlock23[(i-276)]?
            else
              nodeBlock24[(i-288)]?
  else
    if i < 444 then
      if i < 372 then
        if i < 336 then
          if i < 312 then
            nodeBlock25[(i-300)]?
          else
            if i < 324 then
              nodeBlock26[(i-312)]?
            else
              nodeBlock27[(i-324)]?
        else
          if i < 348 then
            nodeBlock28[(i-336)]?
          else
            if i < 360 then
              nodeBlock29[(i-348)]?
            else
              nodeBlock30[(i-360)]?
      else
        if i < 408 then
          if i < 384 then
            nodeBlock31[(i-372)]?
          else
            if i < 396 then
              nodeBlock32[(i-384)]?
            else
              nodeBlock33[(i-396)]?
        else
          if i < 420 then
            nodeBlock34[(i-408)]?
          else
            if i < 432 then
              nodeBlock35[(i-420)]?
            else
              nodeBlock36[(i-432)]?
    else
      if i < 516 then
        if i < 480 then
          if i < 456 then
            nodeBlock37[(i-444)]?
          else
            if i < 468 then
              nodeBlock38[(i-456)]?
            else
              nodeBlock39[(i-468)]?
        else
          if i < 492 then
            nodeBlock40[(i-480)]?
          else
            if i < 504 then
              nodeBlock41[(i-492)]?
            else
              nodeBlock42[(i-504)]?
      else
        if i < 552 then
          if i < 528 then
            nodeBlock43[(i-516)]?
          else
            if i < 540 then
              nodeBlock44[(i-528)]?
            else
              nodeBlock45[(i-540)]?
        else
          if i < 576 then
            if i < 564 then
              nodeBlock46[(i-552)]?
            else
              nodeBlock47[(i-564)]?
          else
            if i < 588 then
              nodeBlock48[(i-576)]?
            else
              nodeBlock49[(i-588)]?

def fastViews : QFast.Table View := ⟨31,viewGet⟩
def fastNodes : QFast.Table Node := ⟨591,nodeGet⟩

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem chkRoot_0 : QFast.passBlock (QFast.checkRootAt fastViews fastNodes) 0 8 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem chkRoot_8 : QFast.passBlock (QFast.checkRootAt fastViews fastNodes) 8 8 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem chkRoot_16 : QFast.passBlock (QFast.checkRootAt fastViews fastNodes) 16 8 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem chkRoot_24 : QFast.passBlock (QFast.checkRootAt fastViews fastNodes) 24 7 = true := by decide +kernel

theorem combineRoot_0_16 : QFast.passBlock (QFast.checkRootAt fastViews fastNodes) 0 16 = true :=
  @QFast.merge_blocks (QFast.checkRootAt fastViews fastNodes) 0 8 8 chkRoot_0 chkRoot_8

theorem combineRoot_16_15 : QFast.passBlock (QFast.checkRootAt fastViews fastNodes) 16 15 = true :=
  @QFast.merge_blocks (QFast.checkRootAt fastViews fastNodes) 16 8 7 chkRoot_16 chkRoot_24

theorem combineRoot_0_31 : QFast.passBlock (QFast.checkRootAt fastViews fastNodes) 0 31 = true :=
  @QFast.merge_blocks (QFast.checkRootAt fastViews fastNodes) 0 16 15 combineRoot_0_16 combineRoot_16_15

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem chkNode_0 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem chkNode_6 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 6 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem chkNode_12 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 12 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem chkNode_18 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 18 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem chkNode_24 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 24 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem chkNode_30 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 30 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem chkNode_36 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 36 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem chkNode_42 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 42 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem chkNode_48 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 48 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem chkNode_54 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 54 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem chkNode_60 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 60 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem chkNode_66 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 66 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem chkNode_72 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 72 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem chkNode_78 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 78 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem chkNode_84 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 84 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem chkNode_90 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 90 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem chkNode_96 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 96 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem chkNode_102 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 102 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem chkNode_108 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 108 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem chkNode_114 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 114 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem chkNode_120 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 120 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem chkNode_126 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 126 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem chkNode_132 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 132 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem chkNode_138 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 138 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem chkNode_144 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 144 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem chkNode_150 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 150 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem chkNode_156 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 156 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem chkNode_162 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 162 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem chkNode_168 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 168 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem chkNode_174 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 174 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem chkNode_180 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 180 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem chkNode_186 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 186 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem chkNode_192 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 192 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem chkNode_198 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 198 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem chkNode_204 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 204 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem chkNode_210 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 210 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem chkNode_216 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 216 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem chkNode_222 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 222 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem chkNode_228 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 228 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem chkNode_234 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 234 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem chkNode_240 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 240 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem chkNode_246 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 246 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem chkNode_252 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 252 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem chkNode_258 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 258 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem chkNode_264 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 264 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem chkNode_270 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 270 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem chkNode_276 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 276 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem chkNode_282 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 282 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem chkNode_288 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 288 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem chkNode_294 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 294 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem chkNode_300 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 300 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem chkNode_306 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 306 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem chkNode_312 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 312 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem chkNode_318 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 318 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem chkNode_324 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 324 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem chkNode_330 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 330 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem chkNode_336 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 336 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem chkNode_342 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 342 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem chkNode_348 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 348 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem chkNode_354 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 354 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem chkNode_360 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 360 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem chkNode_366 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 366 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem chkNode_372 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 372 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem chkNode_378 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 378 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem chkNode_384 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 384 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem chkNode_390 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 390 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem chkNode_396 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 396 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem chkNode_402 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 402 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem chkNode_408 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 408 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem chkNode_414 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 414 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem chkNode_420 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 420 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem chkNode_426 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 426 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem chkNode_432 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 432 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem chkNode_438 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 438 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem chkNode_444 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 444 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem chkNode_450 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 450 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem chkNode_456 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 456 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem chkNode_462 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 462 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem chkNode_468 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 468 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem chkNode_474 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 474 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem chkNode_480 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 480 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem chkNode_486 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 486 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem chkNode_492 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 492 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem chkNode_498 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 498 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem chkNode_504 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 504 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem chkNode_510 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 510 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem chkNode_516 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 516 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem chkNode_522 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 522 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem chkNode_528 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 528 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem chkNode_534 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 534 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem chkNode_540 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 540 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem chkNode_546 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 546 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem chkNode_552 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 552 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem chkNode_558 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 558 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem chkNode_564 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 564 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem chkNode_570 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 570 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem chkNode_576 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 576 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem chkNode_582 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 582 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem chkNode_588 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 588 3 = true := by decide +kernel

theorem combineNode_0_12 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 12 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 0 6 6 chkNode_0 chkNode_6

theorem combineNode_12_12 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 12 12 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 12 6 6 chkNode_12 chkNode_18

theorem combineNode_24_12 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 24 12 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 24 6 6 chkNode_24 chkNode_30

theorem combineNode_36_12 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 36 12 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 36 6 6 chkNode_36 chkNode_42

theorem combineNode_48_12 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 48 12 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 48 6 6 chkNode_48 chkNode_54

theorem combineNode_60_12 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 60 12 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 60 6 6 chkNode_60 chkNode_66

theorem combineNode_72_12 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 72 12 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 72 6 6 chkNode_72 chkNode_78

theorem combineNode_84_12 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 84 12 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 84 6 6 chkNode_84 chkNode_90

theorem combineNode_96_12 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 96 12 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 96 6 6 chkNode_96 chkNode_102

theorem combineNode_108_12 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 108 12 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 108 6 6 chkNode_108 chkNode_114

theorem combineNode_120_12 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 120 12 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 120 6 6 chkNode_120 chkNode_126

theorem combineNode_132_12 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 132 12 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 132 6 6 chkNode_132 chkNode_138

theorem combineNode_144_12 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 144 12 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 144 6 6 chkNode_144 chkNode_150

theorem combineNode_156_12 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 156 12 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 156 6 6 chkNode_156 chkNode_162

theorem combineNode_168_12 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 168 12 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 168 6 6 chkNode_168 chkNode_174

theorem combineNode_180_12 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 180 12 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 180 6 6 chkNode_180 chkNode_186

theorem combineNode_192_12 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 192 12 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 192 6 6 chkNode_192 chkNode_198

theorem combineNode_204_12 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 204 12 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 204 6 6 chkNode_204 chkNode_210

theorem combineNode_216_12 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 216 12 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 216 6 6 chkNode_216 chkNode_222

theorem combineNode_228_12 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 228 12 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 228 6 6 chkNode_228 chkNode_234

theorem combineNode_240_12 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 240 12 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 240 6 6 chkNode_240 chkNode_246

theorem combineNode_252_12 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 252 12 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 252 6 6 chkNode_252 chkNode_258

theorem combineNode_264_12 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 264 12 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 264 6 6 chkNode_264 chkNode_270

theorem combineNode_276_12 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 276 12 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 276 6 6 chkNode_276 chkNode_282

theorem combineNode_288_12 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 288 12 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 288 6 6 chkNode_288 chkNode_294

theorem combineNode_300_12 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 300 12 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 300 6 6 chkNode_300 chkNode_306

theorem combineNode_312_12 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 312 12 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 312 6 6 chkNode_312 chkNode_318

theorem combineNode_324_12 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 324 12 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 324 6 6 chkNode_324 chkNode_330

theorem combineNode_336_12 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 336 12 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 336 6 6 chkNode_336 chkNode_342

theorem combineNode_348_12 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 348 12 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 348 6 6 chkNode_348 chkNode_354

theorem combineNode_360_12 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 360 12 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 360 6 6 chkNode_360 chkNode_366

theorem combineNode_372_12 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 372 12 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 372 6 6 chkNode_372 chkNode_378

theorem combineNode_384_12 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 384 12 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 384 6 6 chkNode_384 chkNode_390

theorem combineNode_396_12 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 396 12 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 396 6 6 chkNode_396 chkNode_402

theorem combineNode_408_12 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 408 12 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 408 6 6 chkNode_408 chkNode_414

theorem combineNode_420_12 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 420 12 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 420 6 6 chkNode_420 chkNode_426

theorem combineNode_432_12 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 432 12 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 432 6 6 chkNode_432 chkNode_438

theorem combineNode_444_12 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 444 12 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 444 6 6 chkNode_444 chkNode_450

theorem combineNode_456_12 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 456 12 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 456 6 6 chkNode_456 chkNode_462

theorem combineNode_468_12 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 468 12 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 468 6 6 chkNode_468 chkNode_474

theorem combineNode_480_12 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 480 12 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 480 6 6 chkNode_480 chkNode_486

theorem combineNode_492_12 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 492 12 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 492 6 6 chkNode_492 chkNode_498

theorem combineNode_504_12 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 504 12 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 504 6 6 chkNode_504 chkNode_510

theorem combineNode_516_12 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 516 12 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 516 6 6 chkNode_516 chkNode_522

theorem combineNode_528_12 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 528 12 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 528 6 6 chkNode_528 chkNode_534

theorem combineNode_540_12 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 540 12 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 540 6 6 chkNode_540 chkNode_546

theorem combineNode_552_12 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 552 12 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 552 6 6 chkNode_552 chkNode_558

theorem combineNode_564_12 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 564 12 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 564 6 6 chkNode_564 chkNode_570

theorem combineNode_576_12 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 576 12 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 576 6 6 chkNode_576 chkNode_582

theorem combineNode_0_24 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 24 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 0 12 12 combineNode_0_12 combineNode_12_12

theorem combineNode_24_24 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 24 24 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 24 12 12 combineNode_24_12 combineNode_36_12

theorem combineNode_48_24 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 48 24 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 48 12 12 combineNode_48_12 combineNode_60_12

theorem combineNode_72_24 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 72 24 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 72 12 12 combineNode_72_12 combineNode_84_12

theorem combineNode_96_24 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 96 24 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 96 12 12 combineNode_96_12 combineNode_108_12

theorem combineNode_120_24 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 120 24 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 120 12 12 combineNode_120_12 combineNode_132_12

theorem combineNode_144_24 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 144 24 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 144 12 12 combineNode_144_12 combineNode_156_12

theorem combineNode_168_24 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 168 24 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 168 12 12 combineNode_168_12 combineNode_180_12

theorem combineNode_192_24 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 192 24 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 192 12 12 combineNode_192_12 combineNode_204_12

theorem combineNode_216_24 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 216 24 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 216 12 12 combineNode_216_12 combineNode_228_12

theorem combineNode_240_24 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 240 24 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 240 12 12 combineNode_240_12 combineNode_252_12

theorem combineNode_264_24 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 264 24 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 264 12 12 combineNode_264_12 combineNode_276_12

theorem combineNode_288_24 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 288 24 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 288 12 12 combineNode_288_12 combineNode_300_12

theorem combineNode_312_24 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 312 24 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 312 12 12 combineNode_312_12 combineNode_324_12

theorem combineNode_336_24 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 336 24 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 336 12 12 combineNode_336_12 combineNode_348_12

theorem combineNode_360_24 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 360 24 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 360 12 12 combineNode_360_12 combineNode_372_12

theorem combineNode_384_24 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 384 24 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 384 12 12 combineNode_384_12 combineNode_396_12

theorem combineNode_408_24 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 408 24 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 408 12 12 combineNode_408_12 combineNode_420_12

theorem combineNode_432_24 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 432 24 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 432 12 12 combineNode_432_12 combineNode_444_12

theorem combineNode_456_24 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 456 24 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 456 12 12 combineNode_456_12 combineNode_468_12

theorem combineNode_480_24 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 480 24 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 480 12 12 combineNode_480_12 combineNode_492_12

theorem combineNode_504_24 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 504 24 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 504 12 12 combineNode_504_12 combineNode_516_12

theorem combineNode_528_24 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 528 24 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 528 12 12 combineNode_528_12 combineNode_540_12

theorem combineNode_552_24 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 552 24 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 552 12 12 combineNode_552_12 combineNode_564_12

theorem combineNode_576_15 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 576 15 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 576 12 3 combineNode_576_12 chkNode_588

theorem combineNode_0_48 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 48 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 0 24 24 combineNode_0_24 combineNode_24_24

theorem combineNode_48_48 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 48 48 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 48 24 24 combineNode_48_24 combineNode_72_24

theorem combineNode_96_48 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 96 48 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 96 24 24 combineNode_96_24 combineNode_120_24

theorem combineNode_144_48 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 144 48 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 144 24 24 combineNode_144_24 combineNode_168_24

theorem combineNode_192_48 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 192 48 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 192 24 24 combineNode_192_24 combineNode_216_24

theorem combineNode_240_48 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 240 48 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 240 24 24 combineNode_240_24 combineNode_264_24

theorem combineNode_288_48 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 288 48 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 288 24 24 combineNode_288_24 combineNode_312_24

theorem combineNode_336_48 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 336 48 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 336 24 24 combineNode_336_24 combineNode_360_24

theorem combineNode_384_48 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 384 48 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 384 24 24 combineNode_384_24 combineNode_408_24

theorem combineNode_432_48 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 432 48 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 432 24 24 combineNode_432_24 combineNode_456_24

theorem combineNode_480_48 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 480 48 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 480 24 24 combineNode_480_24 combineNode_504_24

theorem combineNode_528_48 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 528 48 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 528 24 24 combineNode_528_24 combineNode_552_24

theorem combineNode_0_96 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 96 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 0 48 48 combineNode_0_48 combineNode_48_48

theorem combineNode_96_96 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 96 96 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 96 48 48 combineNode_96_48 combineNode_144_48

theorem combineNode_192_96 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 192 96 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 192 48 48 combineNode_192_48 combineNode_240_48

theorem combineNode_288_96 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 288 96 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 288 48 48 combineNode_288_48 combineNode_336_48

theorem combineNode_384_96 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 384 96 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 384 48 48 combineNode_384_48 combineNode_432_48

theorem combineNode_480_96 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 480 96 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 480 48 48 combineNode_480_48 combineNode_528_48

theorem combineNode_0_192 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 192 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 0 96 96 combineNode_0_96 combineNode_96_96

theorem combineNode_192_192 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 192 192 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 192 96 96 combineNode_192_96 combineNode_288_96

theorem combineNode_384_192 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 384 192 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 384 96 96 combineNode_384_96 combineNode_480_96

theorem combineNode_0_384 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 384 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 0 192 192 combineNode_0_192 combineNode_192_192

theorem combineNode_384_207 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 384 207 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 384 192 15 combineNode_384_192 combineNode_576_15

theorem combineNode_0_591 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 591 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 0 384 207 combineNode_0_384 combineNode_384_207

def bMatches (z : Option View) : Bool :=
  match z with
  | none => false
  | some v => vg v == (0xeee8eae8eea8c888 : Word) && vk v == 9 && (vs v).toFinset == Direct64.cols.toFinset

theorem rootNegative : ¬ CoreSigned.build signedOps (0xeee8eae8eea8c888 : BitVec 64) 9 Direct64.cols.toFinset := by
  have shape : bMatches (QFast.get fastViews 30) = true := by decide +kernel
  cases ev : QFast.get fastViews 30 with
  | none => simp [ev, bMatches] at shape
  | some v =>
    have valid := QFast.certified_view fastViews fastNodes combineRoot_0_31 combineNode_0_591 ev
    simp only [ev,bMatches,Bool.and_eq_true,beq_iff_eq] at shape
    change ¬ CoreSigned.build signedOps (vg v) (vk v) (vs v).toFinset at valid
    rwa [shape.1.1,shape.1.2,shape.2] at valid
end SignedProjection
end PEqualNP.Outside.L_meta_36483_aux

open PEqualNP.Outside.L_meta_36483_aux in
theorem PEqualNP.Outside.L_meta_36483 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008241896 * 2 ^ 32 + 4004038792) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008241896 * 2 ^ 32 + 4004038792) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  LowerSymSix.finish SignedProjection.rootNegative

import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3939

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def copies : List Gate :=
  (List.range 20).map fun i => ⟨.not, [i]⟩

def shift (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (20 + ·)⟩

def transform (c : Circuit) : Circuit :=
  ⟨copies ++ c.gates.map shift, 20 + c.output⟩

def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun v g => v ++ [g.op.eval (g.inputs.map fun i => v.getD i false)]) w

lemma read_shift (p w : List Bool) (hp : p.length = 20) (i : ℕ) :
    (p ++ w).getD (20 + i) false = w.getD i false := by
  rw [List.getD_append_right _ _ _ _ (by omega), hp, Nat.add_sub_cancel_left]

lemma run_shift (gs : List Gate) (p w : List Bool) (hp : p.length = 20) :
    run (gs.map shift) (p ++ w) = p ++ run gs w := by
  induction gs generalizing w with
  | nil => simp [run]
  | cons g gs ih =>
    let b := g.op.eval (g.inputs.map fun i => w.getD i false)
    have h : (shift g).op.eval ((shift g).inputs.map fun i => (p ++ w).getD i false) = b := by
      simp only [shift, List.map_map, Function.comp_def, read_shift p w hp, b]
    change run (gs.map shift) ((p ++ w) ++ [_]) = p ++ run gs (w ++ [b])
    rw [h, List.append_assoc, ih]

def inverter (i : ℕ) : Gate := ⟨.not, [i]⟩

lemma read_bank (indices : List ℕ) (w : List Bool)
    (ok : ∀ i ∈ indices, i < w.length) :
    run (indices.map inverter) w = w ++ indices.map (fun i => !(w.getD i false)) := by
  induction indices generalizing w with
  | nil => simp [run]
  | cons i indices ih =>
    let b := !(w.getD i false)
    change run (indices.map inverter) (w ++ [b]) = w ++ b :: _
    have bound (j) (hj : j ∈ indices) : j < w.length := ok j (by simp [hj])
    rw [ih _ (by intro j hj; simpa using Nat.lt_succ_of_lt (bound j hj))]
    rw [List.append_assoc]
    congr 2
    apply congrArg (List.cons b)
    apply List.map_congr_left
    intro j hj
    rw [List.getD_append _ _ _ _ (bound j hj)]

def pad (x : Fin 10 → Bool) := List.ofFn x ++ List.ofFn fun i => !(x i)

lemma copy_values (x : Fin 10 → Bool) : run copies (List.ofFn x) = pad x ++ List.ofFn x := by
  let a := List.ofFn x
  let b := List.ofFn fun i => !(x i)
  have la : a.length = 10 := List.length_ofFn
  have lb : b.length = 10 := List.length_ofFn
  let second := (List.range 10).map (10 + ·)
  have part : copies = (List.range 10).map inverter ++ second.map inverter := by
    change (List.map inverter (List.range (10 + 10))) = _
    rw [List.range_add, List.map_append]
  have ha : (List.range 10).map (fun i => !(a.getD i false)) = b := by
    apply List.ext_getElem
    · simp [lb]
    · intro i hi hj
      have h : i < 10 := by simpa using hi
      simp only [List.getElem_map, List.getElem_range]
      rw [List.getD_eq_getElem _ _ (by omega)]
      simp only [a, b, List.getElem_ofFn]
  have hb : second.map (fun i => !((a ++ b).getD i false)) = a := by
    apply List.ext_getElem
    · simp [second, la]
    · intro i hi hj
      have h : i < 10 := by simpa [second] using hi
      simp only [second, List.getElem_map, List.getElem_range]
      rw [List.getD_append_right _ _ _ _ (by omega), la, Nat.add_sub_cancel_left,
        List.getD_eq_getElem _ _ (by omega)]
      simp only [a, b, List.getElem_ofFn, Bool.not_not]
  rw [part]
  have split : run ((List.range 10).map inverter ++ second.map inverter) a =
      run (second.map inverter) (run ((List.range 10).map inverter) a) := List.foldl_append
  change run ((List.range 10).map inverter ++ second.map inverter) a = _
  rw [split, read_bank _ a (by simp [la]), ha]
  rw [read_bank _ (a ++ b) (by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
    have := List.mem_range.mp hj
    simp [la, lb]
    omega), hb]
  rfl

lemma same (c : Circuit) (x : Fin 10 → Bool) :
    (transform c).eval (List.ofFn x) = c.eval (List.ofFn x) := by
  have hp : (pad x).length = 20 := by simp [pad]
  change (run (copies ++ c.gates.map shift) (List.ofFn x)).getD (20 + c.output) false = _
  have h : run (copies ++ c.gates.map shift) (List.ofFn x) =
      run (c.gates.map shift) (run copies (List.ofFn x)) := List.foldl_append
  rw [h, copy_values, run_shift _ _ _ hp, read_shift _ _ hp]
  rfl

lemma fan (c : Circuit) (hf : FanInTwo c) : FanInTwo (transform c) := by
  intro g hg
  rcases List.mem_append.mp hg with h | h
  · obtain ⟨i, _, rfl⟩ := List.mem_map.mp h
    simp
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp h
    simpa [shift] using hf a ha

noncomputable def counted (g : Gate) : Bool :=
  GateOp.rec true true false (fun _ => true) true g.op

lemma count_eq (c : Circuit) : (transform c).gates.countP counted = c.gates.countP counted := by
  change (copies ++ c.gates.map shift).countP counted = _
  rw [List.countP_append, show copies.countP counted = 0 by decide, Nat.zero_add, List.countP_map]
  rfl

lemma location (c : Circuit) (k : ℕ) (hk : k < 10) (i : Fin (transform c).gates.length)
    (hi : k ∈ ((transform c).gates.get i).inputs) : i.val = k := by
  change k ∈ ((copies ++ c.gates.map shift)[i.val]).inputs at hi
  by_cases h : i.val < copies.length
  · rw [List.getElem_append_left h] at hi
    symm
    simpa [copies] using hi
  · rw [List.getElem_append_right (by omega : copies.length ≤ i.val)] at hi
    simp only [List.getElem_map, shift, List.mem_map] at hi
    obtain ⟨a, _, ha⟩ := hi
    omega

end PEqualNP.Outside.L_meta_3939

open PEqualNP.Outside.L_meta_3939

theorem PEqualNP.Outside.L_meta_3939 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → List.countP (fun (x3 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.rec Bool.true Bool.true Bool.false (fun (x4 : ℕ) => Bool.true) Bool.true x3.op) x1.gates ≤ (12 : ℕ) → (∀ (x4 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x4 ++ [x4 (0 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ))]) = (x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)))) → ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x5 ∧ List.countP (fun (x6 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.rec Bool.true Bool.true Bool.false (fun (x7 : ℕ) => Bool.true) Bool.true x6.op) x5.gates ≤ (12 : ℕ) ∧ (∀ x6 ∈ [(0 : ℕ), (1 : ℕ), (2 : ℕ), (4 : ℕ), (7 : ℕ), (8 : ℕ)], ∀ (x8 x9 : Fin x5.gates.length), x6 ∈ (x5.gates.get x8).inputs → x6 ∈ (x5.gates.get x9).inputs → x8 = x9) ∧ ∀ (x6 : Fin (10 : ℕ) → Bool), x5.eval (List.ofFn x6) = x1.eval (List.ofFn x6) := by
  intro c hf hc _
  refine ⟨transform c, fan c hf, ?_, ?_, same c⟩
  · change (transform c).gates.countP counted ≤ 12
    rw [count_eq]
    exact hc
  · intro k hk i j hi hj
    have h : k < 10 := by simp at hk; omega
    exact Fin.ext ((location c k h i hi).trans (location c k h j hj).symm)

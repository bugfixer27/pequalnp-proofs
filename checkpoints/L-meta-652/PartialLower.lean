import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_652

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]

private def evalWires {n : ℕ} (gs : List Gate) (x : Fin n → Bool) : List Bool :=
  gs.foldl step (List.ofFn x)

private def value {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (j : ℕ) : Bool :=
  (evalWires gs x).getD j false

private theorem fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [step]
    omega

private theorem wires_length {n : ℕ} (gs : List Gate) (x : Fin n → Bool) :
    (evalWires gs x).length = n + gs.length := by
  simp [evalWires, fold_length]

private theorem value_snoc_old {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool)
    {j : ℕ} (hj : j < n + gs.length) : value (gs ++ [g]) x j = value gs x j := by
  simp only [value, evalWires, List.foldl_append, List.foldl_cons, List.foldl_nil, step]
  exact List.getD_append _ _ _ _ (by simpa [fold_length] using hj)

private theorem value_snoc_new {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) :
    value (gs ++ [g]) x (n + gs.length) = g.op.eval (g.inputs.map (value gs x)) := by
  rw [value, evalWires, List.foldl_append, List.foldl_cons, List.foldl_nil, step,
    List.getD_append_right _ _ _ _ (by simp [fold_length])]
  simp [fold_length]
  rfl

private theorem value_outside {n : ℕ} (gs : List Gate) (x : Fin n → Bool)
    {j : ℕ} (hj : n + gs.length ≤ j) : value gs x j = false :=
  List.getD_eq_default _ _ (by rwa [wires_length])

private theorem value_input {n : ℕ} (gs : List Gate) (x : Fin n → Bool) {j : ℕ} (hj : j < n) :
    value gs x j = x ⟨j, hj⟩ := by
  induction gs using List.reverseRecOn with
  | nil =>
    simp [value, evalWires, hj]
  | append_singleton gs g ih =>
    rw [value_snoc_old _ _ _ (by omega), ih]

private def delta {n m : ℕ} (gs : List Gate) (z : Fin n → Bool)
    (rows : Fin m → Fin n → Bool) (j : ℕ) : Finset (Fin m) :=
  Finset.univ.filter (fun r => value gs (rows r) j ≠ value gs z j)

private def affected {n m : ℕ} (gs : List Gate) (z : Fin n → Bool)
    (rows : Fin m → Fin n → Bool) (T : Finset ℕ) : Finset (Fin m) :=
  T.biUnion (delta gs z rows)

private theorem affected_mem {n m : ℕ} (gs : List Gate) (z : Fin n → Bool)
    (rows : Fin m → Fin n → Bool) (T : Finset ℕ) (r : Fin m) :
    r ∈ affected gs z rows T ↔ ∃ j ∈ T, value gs (rows r) j ≠ value gs z j := by
  simp [affected, delta]

-- A source gate distinguishes at most one test input from the baseline.
-- The other gates can reuse source wires arbitrarily and have fan-in at most two.
private theorem cut_count {n m : ℕ} (gs : List Gate) (src : Gate → Bool)
    (z : Fin n → Bool) (rows : Fin m → Fin n → Bool)
    (hsrc : ∀ pre g tail, gs = pre ++ g :: tail → src g = true →
      (delta (pre ++ [g]) z rows (n + pre.length)).card ≤ 1)
    (hrest : ∀ g ∈ gs, src g = false → g.inputs.length ≤ 2 ∧ ∀ j ∈ g.inputs, n ≤ j)
    (T : Finset ℕ) (hT : ∀ j ∈ T, n ≤ j ∧ j < n + gs.length) :
    (affected gs z rows T).card ≤ (gs.filter src).length ∧
    (affected gs z rows T).card ≤ T.card + (gs.filter (fun g => !(src g))).length := by
  classical
  induction gs using List.reverseRecOn generalizing T with
  | nil =>
    have he : T = ∅ := by apply Finset.eq_empty_iff_forall_notMem.mpr; intro j hj; have h := hT j hj; simp at h; omega
    simp [he, affected]
  | append_singleton gs g ih =>
    let b := n + gs.length
    have hpre : ∀ pre a tail, gs = pre ++ a :: tail → src a = true →
        (delta (pre ++ [a]) z rows (n + pre.length)).card ≤ 1 := by
      intro pre a tail e ha
      exact hsrc pre a (tail ++ [g]) (by simp [e]) ha
    have hgs : ∀ a ∈ gs, src a = false → a.inputs.length ≤ 2 ∧ ∀ j ∈ a.inputs, n ≤ j :=
      fun a ha => hrest a (List.mem_append_left _ ha)
    have hl (j : ℕ) (hj : j ∈ T) (hne : j ≠ b) : j < b := by
      have hh := (hT j hj).2
      simp only [List.length_append, List.length_singleton] at hh
      dsimp [b] at *; omega
    have ht : ∀ j ∈ T.erase b, n ≤ j ∧ j < b :=
      fun j hj => ⟨(hT j (Finset.mem_of_mem_erase hj)).1,
        hl j (Finset.mem_of_mem_erase hj) (Finset.ne_of_mem_erase hj)⟩
    by_cases hb : b ∈ T
    · have hc := Finset.card_erase_add_one hb
      by_cases hs : src g = true
      · have hi := ih hpre hgs (T.erase b) ht
        have hd := hsrc gs g [] rfl hs
        have hsub : affected (gs ++ [g]) z rows T ⊆ affected gs z rows (T.erase b) ∪
            delta (gs ++ [g]) z rows b := by
          intro r hr
          obtain ⟨j,hj,hne⟩ := (affected_mem _ _ _ _ _).mp hr
          by_cases he : j = b
          · subst j; apply Finset.mem_union_right
            simpa [delta] using hne
          · apply Finset.mem_union_left
            apply (affected_mem _ _ _ _ _).mpr
            exact ⟨j, Finset.mem_erase.mpr ⟨he,hj⟩, by
              simpa only [value_snoc_old _ _ _ (hl j hj he)] using hne⟩
        have h := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
        change (delta (gs ++ [g]) z rows b).card ≤ 1 at hd
        simp [hs]; omega
      · have hs' : src g = false := Bool.eq_false_iff.mpr hs
        obtain ⟨hg, hraw⟩ := hrest g (by simp) hs'
        let U := g.inputs.toFinset.filter (fun j => j < b)
        let T' := T.erase b ∪ U
        have ht' : ∀ j ∈ T', n ≤ j ∧ j < b := by
          intro j hj
          rcases Finset.mem_union.mp hj with h | h
          · exact ht j h
          · exact ⟨hraw j (List.mem_toFinset.mp (Finset.mem_filter.mp h).1), (Finset.mem_filter.mp h).2⟩
        have hi := ih hpre hgs T' ht'
        have hu : U.card ≤ 2 := (Finset.card_filter_le _ _).trans (List.toFinset_card_le _ |>.trans hg)
        have htcard : T'.card ≤ T.card + 1 := by
          have e := Finset.card_union_le (T.erase b) U; change T'.card ≤ _ at e; omega
        have hsub : affected (gs ++ [g]) z rows T ⊆ affected gs z rows T' := by
          intro r hr
          obtain ⟨j,hj,hne⟩ := (affected_mem _ _ _ _ _).mp hr
          by_cases he : j = b
          · subst j
            change value (gs ++ [g]) (rows r) (n + gs.length) ≠ value (gs ++ [g]) z (n + gs.length) at hne
            rw [value_snoc_new, value_snoc_new] at hne
            by_contra hmiss
            apply hne
            congr 1
            apply List.map_congr_left
            intro j hj
            by_cases hjb : j < b
            · by_contra hdiff
              exact hmiss ((affected_mem _ _ _ _ _).mpr ⟨j, Finset.mem_union_right _
                (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hj, hjb⟩), hdiff⟩)
            · rw [value_outside _ _ (Nat.le_of_not_gt hjb), value_outside _ _ (Nat.le_of_not_gt hjb)]
          · apply (affected_mem _ _ _ _ _).mpr
            exact ⟨j, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨he,hj⟩), by
              simpa only [value_snoc_old _ _ _ (hl j hj he)] using hne⟩
        have h := Finset.card_le_card hsub
        simp [hs']; omega
    · have ht' : ∀ j ∈ T, n ≤ j ∧ j < b := fun j hj =>
        ⟨(hT j hj).1,hl j hj (fun e => hb (e ▸ hj))⟩
      have hi := ih hpre hgs T ht'
      have hsub : affected (gs ++ [g]) z rows T ⊆ affected gs z rows T := by
        intro r hr
        obtain ⟨j,hj,hne⟩ := (affected_mem _ _ _ _ _).mp hr
        exact (affected_mem _ _ _ _ _).mpr ⟨j,hj,by simpa only [value_snoc_old _ _ _ (ht' j hj).2] using hne⟩
      have h := Finset.card_le_card hsub
      cases hs : src g <;> simp [hs] <;> omega

private theorem partition_length (gs : List Gate) (src : Gate → Bool) :
    (gs.filter src).length + (gs.filter (fun g => !(src g))).length = gs.length := by
  induction gs with
  | nil => rfl
  | cons g gs ih => cases h : src g <;> simp [h] <;> omega

theorem separating_rows_bound {n m : ℕ} (C : Circuit) (src : Gate → Bool)
    (z : Fin n → Bool) (rows : Fin m → Fin n → Bool)
    (hsrc : ∀ pre g tail, C.gates = pre ++ g :: tail → src g = true →
      (Finset.univ.filter (fun r : Fin m =>
        value (pre ++ [g]) (rows r) (n + pre.length) ≠
        value (pre ++ [g]) z (n + pre.length))).card ≤ 1)
    (hrest : ∀ g ∈ C.gates, src g = false → g.inputs.length ≤ 2 ∧ ∀ j ∈ g.inputs, n ≤ j)
    (T : Finset ℕ) (hT : ∀ j ∈ T, n ≤ j ∧ j < n + C.gates.length)
    (hd : ∀ r : Fin m, ∃ j ∈ T,
      (C.wires (List.ofFn (rows r))).getD j false ≠ (C.wires (List.ofFn z)).getD j false) :
    2 * m ≤ C.size + T.card := by
  have h := cut_count C.gates src z rows hsrc hrest T hT
  have hall : affected C.gates z rows T = Finset.univ := Finset.eq_univ_of_forall
    (fun r => (affected_mem _ _ _ _ _).mpr (hd r))
  rw [hall, Finset.card_univ, Fintype.card_fin] at h
  have hc := partition_length C.gates src
  unfold Circuit.size; omega

private def pairRow (e : Fin 9) (a : Fin 6) : Bool :=
  decide (a.val = e.val / 3 ∨ a.val = 3 + e.val % 3)

private def target (x : Fin 6 → Bool) (i : Fin 3) : Bool :=
  ![((x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5)),
    ((x 0 && x 4) || (x 1 && x 5) || (x 2 && x 3)),
    ((x 0 && x 5) || (x 1 && x 3) || (x 2 && x 4))] i

private def readsRaw (n : ℕ) (g : Gate) : Bool := g.inputs.any (fun i => decide (i < n))

def rawPairLayer (n : ℕ) (C : Circuit) : Prop :=
  ∀ g ∈ C.gates, readsRaw n g = true → ∃ a b : Fin n, a ≠ b ∧ g.op = .and ∧ g.inputs = [a.val,b.val]

private theorem pairUnique : ∀ a b : Fin 6, a ≠ b →
    (Finset.univ.filter (fun e : Fin 9 => (pairRow e a && pairRow e b) = true)).card ≤ 1 := by
  decide

theorem lower_with_raw_pair_layer (C : Circuit) (fan : PEqualNP.MetaComplexity.FanInTwo C)
    (hp : rawPairLayer 6 C) (out : Fin 3 → ℕ)
    (hC : ∀ x : Fin 6 → Bool, ∀ i, (C.wires (List.ofFn x)).getD (out i) false = target x i) :
    15 ≤ C.size := by
  classical
  let z : Fin 6 → Bool := fun _ => false
  let T := Finset.univ.image out
  have hc (x : Fin 6 → Bool) (i : Fin 3) : value C.gates x (out i) = target x i := hC x i
  have hsrc : ∀ pre g tail, C.gates = pre ++ g :: tail → readsRaw 6 g = true →
      (delta (pre ++ [g]) z pairRow (6 + pre.length)).card ≤ 1 := by
    intro pre g tail he hr
    obtain ⟨a,b,hab,hop,hin⟩ := hp g (by rw [he]; simp) hr
    have hval (x : Fin 6 → Bool) : value (pre ++ [g]) x (6 + pre.length) = (x a && x b) := by
      rw [value_snoc_new, hop, hin]
      simp only [List.map_cons, List.map_nil, value_input _ _ a.isLt, value_input _ _ b.isLt]
      simp [GateOp.eval]
    have hd : delta (pre ++ [g]) z pairRow (6 + pre.length) =
        Finset.univ.filter (fun e : Fin 9 => (pairRow e a && pairRow e b) = true) := by
      ext e; simp only [delta,Finset.mem_filter,Finset.mem_univ,true_and,hval]; simp [z]
    rw [hd]; exact pairUnique a b hab
  have hrest : ∀ g ∈ C.gates, readsRaw 6 g = false → g.inputs.length ≤ 2 ∧ ∀ j ∈ g.inputs, 6 ≤ j := by
    intro g hg hr
    refine ⟨(fan g hg).2, ?_⟩
    simpa [readsRaw, List.any_eq_false] using hr
  have ht : ∀ j ∈ T, 6 ≤ j ∧ j < 6 + C.gates.length := by
    intro j hj
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hj
    constructor
    · by_contra! h
      let a : Fin 6 := ⟨out i,h⟩
      let x : Fin 6 → Bool := fun b => decide (b = a)
      have hzero : ∀ a : Fin 6, ∀ i : Fin 3, target (fun b => decide (b = a)) i = false := by decide
      have hh := hc x i
      rw [value_input _ _ h, hzero a i] at hh
      simp [x,a] at hh
    · by_contra! h
      have hh := hc (fun _ => true) i
      have hone : ∀ i : Fin 3, target (fun _ => true) i = true := by decide
      rw [value_outside _ _ h, hone] at hh
      contradiction
  have heach : ∀ e : Fin 9, ∃ i : Fin 3, target (pairRow e) i ≠ target z i := by decide
  have hd (r : Fin 9) : ∃ j ∈ T, value C.gates (pairRow r) j ≠ value C.gates z j := by
    obtain ⟨i,hi⟩ := heach r
    exact ⟨out i,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩, by simpa only [hc] using hi⟩
  have bound := separating_rows_bound C (readsRaw 6) z pairRow hsrc hrest T ht hd
  have hcard : T.card ≤ 3 := (Finset.card_image_le).trans_eq (by simp)
  omega



def matchValue (x : Fin 6 → Bool) : Fin 3 → Bool :=
  ![((x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5)),
    ((x 0 && x 4) || (x 1 && x 5) || (x 2 && x 3)),
    ((x 0 && x 5) || (x 1 && x 3) || (x 2 && x 4))]

private def row (r : Fin 64) (i : Fin 6) : Bool := r.val.testBit i.val

private def separates (v : Fin 6) (i : Fin 3) (r : Fin 64) : Bool :=
  matchValue (Function.update (row r) v false) i !=
    matchValue (Function.update (row r) v true) i

-- Even after fixing two other inputs arbitrarily, some output still depends on v.
set_option maxRecDepth 32000 in
set_option maxHeartbeats 6000000 in
private theorem probeTable :
    ∀ v a b : Fin 6, v ≠ a → v ≠ b → ∀ p q : Bool, (a = b → p = q) →
      ∃ r : Fin 64, row r a = p ∧ row r b = q ∧ ∃ i, separates v i r = true := by
  decide +kernel

theorem sensitive_after_two_pins (v a b : Fin 6) (hva : v ≠ a) (hvb : v ≠ b)
    (p q : Bool) (hcompat : a = b → p = q) :
    ∃ x : Fin 6 → Bool, x a = p ∧ x b = q ∧
      ∃ i, matchValue (Function.update x v false) i ≠ matchValue (Function.update x v true) i := by
  obtain ⟨r, ha, hb, i, hi⟩ := probeTable v a b hva hvb p q hcompat
  exact ⟨row r, ha, hb, i, by simpa [separates] using hi⟩

private def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun l g => l ++ [g.op.eval (g.inputs.map fun i => l.getD i false)]) w

private theorem run_length (gs : List Gate) (w : List Bool) :
    (run gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [run]
  | cons g gs ih => unfold run; rw [List.foldl_cons]; change (run gs _).length = _
                    rw [ih]; simp; omega

private def agreeOff (x y : List Bool) (v : ℕ) : Prop :=
  ∀ j, j ≠ v → x.getD j false = y.getD j false

private theorem agreeOff_snoc {x y : List Bool} {v : ℕ} {c : Bool}
    (hl : x.length = y.length) (h : agreeOff x y v) :
    agreeOff (x ++ [c]) (y ++ [c]) v := by
  intro j hj
  by_cases hlt : j < x.length
  · rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ (by omega)]
    exact h j hj
  · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega), hl]

private theorem run_agreeOff (gs : List Gate) (x y : List Bool) (v : ℕ)
    (hl : x.length = y.length) (h : agreeOff x y v)
    (hread : ∀ pre g tail, gs = pre ++ g :: tail → v ∈ g.inputs →
      g.op.eval (g.inputs.map fun j => (run pre x).getD j false) =
      g.op.eval (g.inputs.map fun j => (run pre y).getD j false)) :
    agreeOff (run gs x) (run gs y) v := by
  induction gs generalizing x y with
  | nil => exact h
  | cons g gs ih =>
    let eval := fun (l : List Bool) => g.op.eval (g.inputs.map fun j => l.getD j false)
    have hg : eval x = eval y := by
      by_cases hr : v ∈ g.inputs
      · exact hread [] g gs rfl hr
      · dsimp [eval]
        congr 1
        apply List.map_congr_left
        intro j hj
        exact h j (by rintro rfl; exact hr hj)
    change agreeOff (run gs (x ++ [eval x])) (run gs (y ++ [eval y])) v
    apply ih _ _ (by simp [hl])
    · rw [hg]; exact agreeOff_snoc hl h
    · intro pre g' tail he hr
      exact hread (g :: pre) g' tail (by simp [he]) hr

private theorem run_input (gs : List Gate) (x : List Bool) {j : ℕ} (hj : j < x.length) :
    (run gs x).getD j false = x.getD j false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (x ++ [_])).getD j false = _
    rw [ih _ (by simp; omega), List.getD_append _ _ _ _ hj]

private def pin (x : Fin 6 → Bool) (v : Fin 6) (c : Bool) :=
  List.ofFn (Function.update x v c)

private theorem raw_get (x : Fin 6 → Bool) (a : Fin 6) :
    (List.ofFn x).getD a.val false = x a := by
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]

private theorem pin_agree (x : Fin 6 → Bool) (v : Fin 6) :
    agreeOff (pin x v false) (pin x v true) v.val := by
  intro j hj
  by_cases hj' : j < 6
  · have hn : (⟨j,hj'⟩ : Fin 6) ≠ v := by intro e; exact hj (congrArg Fin.val e)
    change (List.ofFn _).getD (⟨j,hj'⟩ : Fin 6).val false = (List.ofFn _).getD (⟨j,hj'⟩ : Fin 6).val false
    rw [raw_get, raw_get, Function.update_of_ne hn, Function.update_of_ne hn]
  · rw [List.getD_eq_default _ _ (by simp [pin]; omega),
        List.getD_eq_default _ _ (by simp [pin]; omega)]

private theorem pin_get (x : Fin 6 → Bool) (v a : Fin 6) (c : Bool) (pre : List Gate) :
    (run pre (pin x v c)).getD a.val false = Function.update x v c a := by
  rw [run_input _ _ (by simp [pin])]
  exact raw_get _ _

-- A controlling raw input fixes the output of this AND or OR gate.
def blockedBy (v a : Fin 6) (p : Bool) (g : Gate) : Prop :=
  (g.inputs = [v.val,a.val] ∨ g.inputs = [a.val,v.val]) ∧
    ((g.op = .and ∧ p = false) ∨ (g.op = .or ∧ p = true))

private theorem blocked_eval {v a : Fin 6} (ha : v ≠ a) {p : Bool}
    {g : Gate} (hb : blockedBy v a p g) {x : Fin 6 → Bool} (hx : x a = p) (pre : List Gate) :
    g.op.eval (g.inputs.map fun j => (run pre (pin x v false)).getD j false) =
    g.op.eval (g.inputs.map fun j => (run pre (pin x v true)).getD j false) := by
  rcases hb with ⟨hin, hop⟩
  rcases hin with hin | hin <;> rcases hop with ⟨hop,rfl⟩ | ⟨hop,rfl⟩ <;>
    simp only [hin, hop, List.map_cons, List.map_nil, pin_get, Function.update_of_ne ha.symm, hx] <;>
    simp [GateOp.eval]

private theorem outputs_not_input (out : Fin 3 → ℕ) (C : Circuit)
    (h : ∀ x : Fin 6 → Bool, ∀ i, (C.wires (List.ofFn x)).getD (out i) false = matchValue x i) :
    ∀ i (v : Fin 6), out i ≠ v.val := by
  intro i v heq
  let x : Fin 6 → Bool := fun w => decide (w = v)
  have hx := h x i
  rw [heq] at hx
  change (run C.gates (List.ofFn x)).getD v.val false = _ at hx
  rw [run_input _ _ (by simp), raw_get] at hx
  have lone : ∀ a : Fin 6, ∀ k : Fin 3, matchValue (fun w => decide (w = a)) k = false := by decide
  simp [x,lone] at hx

theorem no_two_blocked_readers (C : Circuit) (out : Fin 3 → ℕ)
    (hC : ∀ x : Fin 6 → Bool, ∀ i, (C.wires (List.ofFn x)).getD (out i) false = matchValue x i)
    (v a b : Fin 6) (hva : v ≠ a) (hvb : v ≠ b) (p q : Bool) (hc : a = b → p = q) :
    ∃ g ∈ C.gates, v.val ∈ g.inputs ∧ ¬ blockedBy v a p g ∧ ¬ blockedBy v b q g := by
  obtain ⟨x, ha, hb, i, hi⟩ := sensitive_after_two_pins v a b hva hvb p q hc
  by_contra! h
  have same := run_agreeOff C.gates (pin x v false) (pin x v true) v.val
    (by simp [pin]) (pin_agree x v) (by
      intro pre g tail he hr
      have hm : g ∈ C.gates := by rw [he]; simp
      by_cases hga : blockedBy v a p g
      · exact blocked_eval hva hga ha pre
      · exact blocked_eval hvb (h g hm hr hga) hb pre)
  apply hi
  rw [← hC _ i, ← hC _ i]
  exact same (out i) (outputs_not_input out C hC i v)

end PEqualNP.Outside.L_meta_652

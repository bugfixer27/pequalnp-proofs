import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_519

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

private def readsRaw (n : ℕ) (g : Gate) : Bool := g.inputs.any (fun i => decide (i < n))

def rawPairLayer (n : ℕ) (C : Circuit) : Prop :=
  ∀ g ∈ C.gates, readsRaw n g = true → ∃ a b : Fin n, a ≠ b ∧ g.op = .and ∧ g.inputs = [a.val,b.val]

private noncomputable def edgeFun {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → Bool) : Bool :=
  @decide (∃ i j, G.Adj i j ∧ x i = true ∧ x j = true) (Classical.propDecidable _)

theorem edges_lower_with_raw_pair_layer {n : ℕ} (G : SimpleGraph (Fin n))
    (hne : ∃ a b, G.Adj a b) (C : Circuit)
    (fan : PEqualNP.MetaComplexity.FanInTwo C) (hp : rawPairLayer n C)
    (heval : ∀ x, C.eval (List.ofFn x) = edgeFun G x) :
    2 * G.edgeSet.ncard ≤ C.size + 1 := by
  classical
  let es := G.edgeSet
  let m := Fintype.card es
  let enum : Fin m ≃ es := (Fintype.equivFin es).symm
  let rows (r : Fin m) (a : Fin n) : Bool := decide (a ∈ (enum r).val)
  let z : Fin n → Bool := fun _ => false
  have hm : m = G.edgeSet.ncard := by rw [Set.ncard_eq_toFinset_card', Set.toFinset_card]
  have hzero : edgeFun G z = false := by simp [edgeFun,z]
  have hrow (r : Fin m) : edgeFun G (rows r) = true := by
    let e := (enum r).val
    have he : G.Adj e.out.1 e.out.2 := by
      change s(e.out.1,e.out.2) ∈ G.edgeSet
      rw [Sym2.mk_fst_out_snd_out]; exact (enum r).property
    simp only [edgeFun, decide_eq_true_eq]
    exact ⟨e.out.1,e.out.2,he,decide_eq_true (Sym2.out_fst_mem e),decide_eq_true (Sym2.out_snd_mem e)⟩
  have hsrc : ∀ pre g tail, C.gates = pre ++ g :: tail → readsRaw n g = true →
      (delta (pre ++ [g]) z rows (n + pre.length)).card ≤ 1 := by
    intro pre g tail he hr
    obtain ⟨a,b,hab,hop,hin⟩ := hp g (by rw [he]; simp) hr
    have hval (x : Fin n → Bool) : value (pre ++ [g]) x (n + pre.length) = (x a && x b) := by
      rw [value_snoc_new,hop,hin]
      simp only [List.map_cons,List.map_nil,value_input _ _ a.isLt,value_input _ _ b.isLt]
      simp [GateOp.eval]
    apply Finset.card_le_one.mpr
    intro r hr t ht
    have both (u : Fin m) (hu : u ∈ delta (pre ++ [g]) z rows (n + pre.length)) :
        a ∈ (enum u).val ∧ b ∈ (enum u).val := by
      have hh := (Finset.mem_filter.mp hu).2
      rw [hval,hval] at hh
      change (decide (a ∈ (enum u).val) && decide (b ∈ (enum u).val)) ≠ false at hh
      simpa only [Bool.not_eq_false, Bool.and_eq_true, decide_eq_true_eq] using hh
    exact enum.injective (Subtype.ext (((Sym2.mem_and_mem_iff hab).mp (both r hr)).trans
      ((Sym2.mem_and_mem_iff hab).mp (both t ht)).symm))
  have hrest : ∀ g ∈ C.gates, readsRaw n g = false → g.inputs.length ≤ 2 ∧ ∀ j ∈ g.inputs, n ≤ j := by
    intro g hg hr; exact ⟨(fan g hg).2, by simpa [readsRaw,List.any_eq_false] using hr⟩
  have hv (x : Fin n → Bool) : value C.gates x C.output = edgeFun G x := heval x
  have ht : n ≤ C.output ∧ C.output < n + C.gates.length := by
    constructor
    · by_contra! h
      let a : Fin n := ⟨C.output,h⟩
      let x : Fin n → Bool := fun b => decide (b = a)
      have hh := hv x
      rw [value_input _ _ h] at hh
      have hx : edgeFun G x = false := by simp [edgeFun,x]
      rw [hx] at hh; simp [x,a] at hh
    · by_contra! h
      obtain ⟨a,b,hab⟩ := hne
      have hh := hv (fun _ => true)
      rw [value_outside _ _ h] at hh
      have he : edgeFun G (fun _ => true) = true := by
        simp only [edgeFun,decide_eq_true_eq]; exact ⟨a,b,hab,trivial,trivial⟩
      rw [he] at hh; contradiction
  have hd (r : Fin m) : ∃ j ∈ ({C.output} : Finset ℕ), value C.gates (rows r) j ≠ value C.gates z j := by
    exact ⟨C.output,by simp,by rw [hv,hv,hrow,hzero]; decide⟩
  have bound := separating_rows_bound C (readsRaw n) z rows hsrc hrest {C.output} (by simpa using ht) hd
  simpa [hm] using bound

theorem lower_with_raw_pair_layer {n k : ℕ} (G : SimpleGraph (Fin n)) (hne : ∃ a b, G.Adj a b)
    (hk : ∀ T : Finset (Fin n), (∀ i j, G.Adj i j → i ∈ T ∨ j ∈ T) → k ≤ T.card)
    (C : Circuit) (fan : PEqualNP.MetaComplexity.FanInTwo C) (hp : rawPairLayer n C)
    (heval : ∀ x, C.eval (List.ofFn x) = edgeFun G x) :
    G.edgeSet.ncard + k ≤ C.size + 1 := by
  classical
  let T := G.edgeFinset.image (fun e => e.out.1)
  have ht : ∀ i j, G.Adj i j → i ∈ T ∨ j ∈ T := by
    intro i j hij
    have hm : s(i,j).out.1 ∈ T := Finset.mem_image.mpr ⟨s(i,j),by simpa using hij,rfl⟩
    have ho := Sym2.mem_iff.mp (Sym2.out_fst_mem s(i,j))
    rcases ho with h | h
    · exact Or.inl (h ▸ hm)
    · exact Or.inr (h ▸ hm)
  have hcard : T.card ≤ G.edgeSet.ncard := by
    rw [Set.ncard_eq_toFinset_card']; exact (Finset.card_image_le : T.card ≤ G.edgeFinset.card)
  have hcover := hk T ht
  have hbound := edges_lower_with_raw_pair_layer G hne C fan hp heval
  omega

end PEqualNP.Outside.L_meta_519

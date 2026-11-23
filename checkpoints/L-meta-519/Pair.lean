import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_519

open PEqualNP.MetaComplexity.NestedCover

def deletePair {n : ℕ} (G : SimpleGraph (Fin n)) (u v : Fin n) : SimpleGraph (Fin n) :=
  G.deleteEdges (G.incidenceSet u ∪ G.incidenceSet v)

theorem deletePair_adj {n : ℕ} (G : SimpleGraph (Fin n)) (u v a b : Fin n) :
    (deletePair G u v).Adj a b ↔ G.Adj a b ∧ a ≠ u ∧ b ≠ u ∧ a ≠ v ∧ b ≠ v := by
  simp only [deletePair, SimpleGraph.deleteEdges_adj, Set.mem_union,
    SimpleGraph.mk'_mem_incidenceSet_iff]
  grind

private theorem deletePair_comm {n : ℕ} (G : SimpleGraph (Fin n)) (u v : Fin n) :
    deletePair G u v = deletePair G v u := by
  simp [deletePair, Set.union_comm]

theorem deletePair_edge_count {n : ℕ} (G : SimpleGraph (Fin n)) (u v : Fin n)
    (huv : G.Adj u v) (hu : (G.neighborSet u).ncard = 3)
    (hv : (G.neighborSet v).ncard = 3) :
    (deletePair G u v).edgeSet.ncard + 5 = G.edgeSet.ncard := by
  classical
  have hsubset : G.incidenceSet u ∪ G.incidenceSet v ⊆ G.edgeSet :=
    Set.union_subset (G.incidenceSet_subset u) (G.incidenceSet_subset v)
  have hcount := Set.ncard_union_add_ncard_inter (G.incidenceSet u) (G.incidenceSet v)
  have hleft : (G.incidenceSet u).ncard = 3 := by
    rwa [G.ncard_incidenceSet, ← G.ncard_neighborSet u]
  have hright : (G.incidenceSet v).ncard = 3 := by
    rwa [G.ncard_incidenceSet, ← G.ncard_neighborSet v]
  rw [G.incidenceSet_inter_incidenceSet_of_adj huv, Set.ncard_singleton, hleft, hright] at hcount
  have hd := Set.ncard_sdiff_add_ncard_of_subset hsubset
  rw [deletePair, G.edgeSet_deleteEdges]
  omega

private theorem card_erase_two {n : ℕ} (S : Finset (Fin n)) {u v : Fin n} (huv : u ≠ v) :
    ((S.erase u).erase v).card + (if u ∈ S then 1 else 0) +
      (if v ∈ S then 1 else 0) = S.card := by
  have one (T : Finset (Fin n)) (z : Fin n) :
      (T.erase z).card + (if z ∈ T then 1 else 0) = T.card := by
    by_cases hz : z ∈ T
    · simpa [hz] using Finset.card_erase_add_one hz
    · simp [hz]
  have h := one (S.erase u) v
  have h' := one S u
  have hm : v ∈ S.erase u ↔ v ∈ S := Finset.mem_erase.trans (and_iff_right huv.symm)
  simp only [hm] at h
  omega

private theorem cover_erase_pair {n : ℕ} {G : SimpleGraph (Fin n)} {u v : Fin n}
    {S : Finset (Fin n)} (hS : G.IsVertexCover (S : Set (Fin n))) :
    (deletePair G u v).IsVertexCover (((S.erase u).erase v : Finset (Fin n)) : Set (Fin n)) := by
  intro a b hab
  obtain ⟨hab, hau, hbu, hav, hbv⟩ := (deletePair_adj G u v a b).mp hab
  rcases hS hab with h | h
  · exact Or.inl (Finset.mem_erase.mpr ⟨hav, Finset.mem_erase.mpr ⟨hau, h⟩⟩)
  · exact Or.inr (Finset.mem_erase.mpr ⟨hbv, Finset.mem_erase.mpr ⟨hbu, h⟩⟩)

private theorem cover_insert_pair {n : ℕ} {G : SimpleGraph (Fin n)} {u v : Fin n}
    {T : Finset (Fin n)} (hT : (deletePair G u v).IsVertexCover (T : Set (Fin n))) :
    G.IsVertexCover ((insert u (insert v T) : Finset (Fin n)) : Set (Fin n)) := by
  intro a b hab
  by_cases ha : a = u ∨ a = v
  · exact Or.inl (by rcases ha with rfl | rfl <;> simp)
  by_cases hb : b = u ∨ b = v
  · exact Or.inr (by rcases hb with rfl | rfl <;> simp)
  push Not at ha hb
  have h := hT ((deletePair_adj G u v a b).mpr ⟨hab, ha.1, hb.1, ha.2, hb.2⟩)
  rcases h with h | h
  · exact Or.inl (by simpa using Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
  · exact Or.inr (by simpa using Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))

private theorem cover_insert_other {n : ℕ} {G : SimpleGraph (Fin n)} {u v : Fin n}
    {T : Finset (Fin n)} (hT : (deletePair G u v).IsVertexCover (T : Set (Fin n)))
    (hN : ∀ w, G.Adj u w → w ≠ v → w ∈ T) :
    G.IsVertexCover ((insert v T : Finset (Fin n)) : Set (Fin n)) := by
  intro a b hab
  by_cases hav : a = v
  · exact Or.inl (by simp [hav])
  by_cases hbv : b = v
  · exact Or.inr (by simp [hbv])
  by_cases hau : a = u
  · subst a
    exact Or.inr (by simpa using Finset.mem_insert_of_mem (b := v) (hN b hab hbv))
  by_cases hbu : b = u
  · subst b
    exact Or.inl (by simpa using Finset.mem_insert_of_mem (b := v) (hN a hab.symm hav))
  rcases hT ((deletePair_adj G u v a b).mpr ⟨hab, hau, hbu, hav, hbv⟩) with h | h
  · exact Or.inl (by simpa using Finset.mem_insert_of_mem (b := v) h)
  · exact Or.inr (by simpa using Finset.mem_insert_of_mem (b := v) h)

def hasNeighborCover {n : ℕ} (G : SimpleGraph (Fin n)) (u v : Fin n) : Prop :=
  ∃ T : Finset (Fin n), IsMinCover (deletePair G u v) T ∧
    ((∀ w, G.Adj u w → w ≠ v → w ∈ T) ∨ (∀ w, G.Adj v w → w ≠ u → w ∈ T))

private theorem cover_card_difference {n : ℕ} (G : SimpleGraph (Fin n)) {u v : Fin n}
    (huv : G.Adj u v) {S T : Finset (Fin n)}
    (hS : IsMinCover G S) (hT : IsMinCover (deletePair G u v) T) :
    T.card + 1 ≤ S.card ∧ S.card ≤ T.card + 2 ∧
      (S.card = T.card + 1 ↔ hasNeighborCover G u v) := by
  have hcount := card_erase_two S huv.ne
  have hle := hT.2 _ (cover_erase_pair (u := u) (v := v) hS.1)
  have huvS : u ∈ S ∨ v ∈ S := hS.1 huv
  have hlo : T.card + 1 ≤ S.card := by
    rcases huvS with h | h <;> simp [h] at hcount <;> omega
  have hhi : S.card ≤ T.card + 2 := by
    exact (hS.2 _ (cover_insert_pair hT.1)).trans
      (by have h1 := Finset.card_insert_le v T
          have h2 := Finset.card_insert_le u (insert v T)
          omega)
  refine ⟨hlo, hhi, ?_⟩
  constructor
  · intro hcard
    have hcov := cover_erase_pair (u := u) (v := v) hS.1
    have hone : (u ∈ S ∧ v ∉ S) ∨ (v ∈ S ∧ u ∉ S) := by
      by_cases hu : u ∈ S <;> by_cases hv : v ∈ S
      · simp [hu, hv] at hcount
        omega
      · exact Or.inl ⟨hu, hv⟩
      · exact Or.inr ⟨hv, hu⟩
      · exact (huvS.elim hu hv).elim
    have hkeep : ((S.erase u).erase v).card + 1 = S.card := by
      rcases hone with ⟨hu, hv⟩ | ⟨hv, hu⟩
      · simpa [hu, hv] using hcount
      · simpa [hu, hv] using hcount
    have herase := Nat.add_right_cancel (hkeep.trans hcard)
    refine ⟨(S.erase u).erase v, ⟨hcov, fun U hU => herase ▸ hT.2 U hU⟩, ?_⟩
    rcases hone with ⟨_, hv⟩ | ⟨_, hu⟩
    · right
      intro w hw hwu
      have hwS : w ∈ S := (hS.1 hw).resolve_left hv
      exact Finset.mem_erase.mpr ⟨hw.ne.symm, Finset.mem_erase.mpr ⟨hwu, hwS⟩⟩
    · left
      intro w hw hwv
      have hwS : w ∈ S := (hS.1 hw).resolve_left hu
      exact Finset.mem_erase.mpr ⟨hwv, Finset.mem_erase.mpr ⟨hw.ne.symm, hwS⟩⟩
  · rintro ⟨U, hU, hN⟩
    have hUT : U.card = T.card := le_antisymm (hU.2 T hT.1) (hT.2 U hU.1)
    have hle : S.card ≤ U.card + 1 := by
      rcases hN with hN | hN
      · exact (hS.2 _ (cover_insert_other hU.1 hN)).trans (Finset.card_insert_le v U)
      · have hcover : (deletePair G v u).IsVertexCover (U : Set (Fin n)) := by
          simpa only [deletePair_comm G v u] using hU.1
        exact (hS.2 _ (cover_insert_other hcover hN)).trans (Finset.card_insert_le u U)
    omega

-- The cover cost is one exactly when a minimum cover of the graph after
-- deletion already contains every other neighbor of one endpoint.
theorem deletion_cost {n : ℕ} (G : SimpleGraph (Fin n)) {u v : Fin n}
    (huv : G.Adj u v) (hu : (G.neighborSet u).ncard = 3)
    (hv : (G.neighborSet v).ncard = 3) {S T : Finset (Fin n)}
    (hS : IsMinCover G S) (hT : IsMinCover (deletePair G u v) T) :
    G.edgeSet.ncard + S.card =
      (deletePair G u v).edgeSet.ncard + T.card +
        (@ite ℕ (hasNeighborCover G u v) (Classical.propDecidable _) 6 7) := by
  classical
  have hedge := deletePair_edge_count G u v huv hu hv
  obtain ⟨hlo, hhi, hiff⟩ := cover_card_difference G huv hS hT
  by_cases h : hasNeighborCover G u v
  · have hr := hiff.mpr h
    simp only [h, ite_true]
    omega
  · have hr : S.card ≠ T.card + 1 := fun heq => h (hiff.mp heq)
    simp only [h, ite_false]
    omega

noncomputable def edgeValue {n : ℕ} (G : SimpleGraph (Fin n))
    (x : Fin n → Bool) : Bool :=
  @decide (∃ a b : Fin n, G.Adj a b ∧ x a = true ∧ x b = true) (Classical.propDecidable _)

theorem cofactor_false_false {n : ℕ} (G : SimpleGraph (Fin n)) {u v : Fin n}
    (huv : u ≠ v) (x : Fin n → Bool) :
    edgeValue G (Function.update (Function.update x u false) v false) =
      edgeValue (deletePair G u v) x := by
  apply Bool.eq_iff_iff.mpr
  simp only [edgeValue, decide_eq_true_eq]
  let y := Function.update (Function.update x u false) v false
  have hyu : y u = false := by simp [y, huv]
  have hyv : y v = false := by simp [y]
  have hy (w : Fin n) (hwu : w ≠ u) (hwv : w ≠ v) : y w = x w := by
    simp [y, hwu, hwv]
  change (∃ a b, G.Adj a b ∧ y a = true ∧ y b = true) ↔ _
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    have hau : a ≠ u := fun e => by simp [e, hyu] at ha
    have hbu : b ≠ u := fun e => by simp [e, hyu] at hb
    have hav : a ≠ v := fun e => by simp [e, hyv] at ha
    have hbv : b ≠ v := fun e => by simp [e, hyv] at hb
    exact ⟨a, b, (deletePair_adj G u v a b).mpr ⟨hab, hau, hbu, hav, hbv⟩,
      (hy a hau hav) ▸ ha, (hy b hbu hbv) ▸ hb⟩
  · rintro ⟨a, b, hab, ha, hb⟩
    obtain ⟨hab, hau, hbu, hav, hbv⟩ := (deletePair_adj G u v a b).mp hab
    exact ⟨a, b, hab, (hy a hau hav).symm ▸ ha, (hy b hbu hbv).symm ▸ hb⟩

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The gate simplifier and its correctness invariant are adapted from L_meta_522.lean.
private def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

private lemma wiresFrom_nil (w : List Bool) : wiresFrom [] w = w := rfl

private lemma wiresFrom_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wiresFrom (g :: gs) w =
      wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

private lemma wiresFrom_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) := by
  induction gs₁ generalizing w with
  | nil => rfl
  | cons g gs ih => simp only [List.cons_append, wiresFrom_cons, ih]

private lemma wiresFrom_length (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [wiresFrom]
  | cons g gs ih =>
    rw [wiresFrom_cons, ih]
    simp
    omega

private lemma getD_snoc_lt {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i < l.length) :
    (l ++ [x]).getD i d = l.getD i d := by
  simp [List.getD, List.getElem?_append_left hi]

private lemma getD_snoc_eq {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i = l.length) :
    (l ++ [x]).getD i d = x := by
  subst hi
  simp [List.getD]

private lemma getD_snoc_ne {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i ≠ l.length) :
    (l ++ [x]).getD i d = l.getD i d := by
  by_cases hlt : i < l.length
  · exact getD_snoc_lt l x d i hlt
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

private lemma wiresFrom_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [wiresFrom_cons, ih _ (by simp; omega)]
    exact getD_snoc_lt _ _ _ _ hi

private def OkGate (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

private def NOkGate (g : Gate) : Prop :=
  OkGate g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

private def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

private lemma normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [normGate]
  cases inputs <;> simp [GateOp.eval]

private lemma normGate_nok (g : Gate) (h : OkGate g) : NOkGate (normGate g) := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hlen⟩ := h
  rcases hop with h | h | h
  · have : op = GateOp.and := h
    subst this
    exact ⟨⟨Or.inl rfl, hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.or := h
    subst this
    exact ⟨⟨Or.inr (Or.inl rfl), hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.not := h
    subst this
    refine ⟨⟨Or.inr (Or.inr rfl), ?_⟩, fun _ => ?_⟩
    · simp [normGate]
    · simp [normGate]

private lemma wiresFrom_norm (gs : List Gate) (w : List Bool) :
    wiresFrom (gs.map normGate) w = wiresFrom gs w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.map_cons, wiresFrom_cons, wiresFrom_cons, normGate_eval, ih]

private def statVal (w : List Bool) : Bool ⊕ ℕ → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

private def statValid (m : ℕ) : Bool ⊕ ℕ → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

private def simpNot (m : ℕ) : List (Bool ⊕ ℕ) → Option Gate × (Bool ⊕ ℕ)
  | [] => (none, Sum.inl true)
  | Sum.inl c :: _ => (none, Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not, [j]⟩, Sum.inr m)

private def simpAnd (m : ℕ) : List (Bool ⊕ ℕ) → Option Gate × (Bool ⊕ ℕ)
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

private def simpOr (m : ℕ) : List (Bool ⊕ ℕ) → Option Gate × (Bool ⊕ ℕ)
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

private def simplifyGate (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ)) :
    Option Gate × (Bool ⊕ ℕ) :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Sum.inl false)

private lemma simplifyGate_ok (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ)) :
    ∀ g ∈ (simplifyGate op m ins).1, OkGate g := by
  intro g hg
  cases op <;> simp only [simplifyGate] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    subst hg; simp [OkGate]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    subst hg; simp [OkGate]
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg
    subst hg; simp [OkGate]
  · simp at hg
  · simp at hg

private lemma simplifyGate_none_of_const (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ))
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Sum.inl c ∈ ins) :
    (simplifyGate op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplifyGate, simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplifyGate, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplifyGate, simpNot]

private lemma simplifyGate_sound (op : GateOp)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List (Bool ⊕ ℕ)) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, statValid w.length s) :
    statValid (w.length + (simplifyGate op w.length ins).1.toList.length)
      (simplifyGate op w.length ins).2 ∧
    statVal (wiresFrom (simplifyGate op w.length ins).1.toList w)
      (simplifyGate op w.length ins).2 = op.eval (ins.map (statVal w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplifyGate, simpAnd, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplifyGate, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a with
      | inl c =>
        cases b with
        | inl d => simp_all [simplifyGate, simpAnd, statValid, statVal, GateOp.eval]
        | inr j => cases c <;> simp_all [simplifyGate, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
      | inr i =>
        cases b with
        | inl d => cases d <;> simp_all [simplifyGate, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
        | inr j => simp_all [simplifyGate, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplifyGate, simpOr, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplifyGate, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a with
      | inl c =>
        cases b with
        | inl d => simp_all [simplifyGate, simpOr, statValid, statVal, GateOp.eval]
        | inr j => cases c <;> simp_all [simplifyGate, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
      | inr i =>
        cases b with
        | inl d => cases d <;> simp_all [simplifyGate, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
        | inr j => simp_all [simplifyGate, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplifyGate, simpNot, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplifyGate, simpNot, statValid, statVal, GateOp.eval, wiresFrom]

private def elimStep (m : ℕ) (acc : List (Bool ⊕ ℕ) × List Gate) (g : Gate) :
    List (Bool ⊕ ℕ) × List Gate :=
  let r := simplifyGate g.op (m + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Sum.inl false))
  (acc.1 ++ [r.2], acc.2 ++ r.1.toList)

private def elimPass (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate) :
    List (Bool ⊕ ℕ) × List Gate :=
  gs.foldl (elimStep m) acc

private lemma elimPass_nil (m : ℕ) (acc : List (Bool ⊕ ℕ) × List Gate) :
    elimPass m [] acc = acc := rfl

private lemma elimPass_cons (m : ℕ) (g : Gate) (gs : List Gate)
    (acc : List (Bool ⊕ ℕ) × List Gate) :
    elimPass m (g :: gs) acc = elimPass m gs (elimStep m acc g) := rfl

private lemma elimPass_append (m : ℕ) (gs₁ gs₂ : List Gate)
    (acc : List (Bool ⊕ ℕ) × List Gate) :
    elimPass m (gs₁ ++ gs₂) acc = elimPass m gs₂ (elimPass m gs₁ acc) := by
  induction gs₁ generalizing acc with
  | nil => rfl
  | cons g gs ih => simp only [List.cons_append, elimPass_cons, ih]

private lemma toList_opt_len_le {α : Type*} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

private lemma elimPass_ok (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
    (h : ∀ g ∈ acc.2, OkGate g) : ∀ g ∈ (elimPass m gs acc).2, OkGate g := by
  induction gs generalizing acc with
  | nil => exact h
  | cons g gs ih =>
    rw [elimPass_cons]
    apply ih
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact simplifyGate_ok _ _ _ g' (by simpa using h1)

private def ElimInv (m : ℕ) (w_in w_old : List Bool)
    (acc : List (Bool ⊕ ℕ) × List Gate) : Prop :=
  w_in.length = m ∧
  acc.1.length = w_old.length ∧
  ∀ i : ℕ,
    statValid (m + acc.2.length) (acc.1.getD i (Sum.inl false)) ∧
    statVal (wiresFrom acc.2 w_in) (acc.1.getD i (Sum.inl false)) = w_old.getD i false

private lemma elimInv_step (m : ℕ) (w_in w_old : List Bool)
    (acc : List (Bool ⊕ ℕ) × List Gate) (g : Gate) (hok : OkGate g)
    (hinv : ElimInv m w_in w_old acc) :
    ElimInv m w_in (w_old ++ [g.op.eval (g.inputs.map fun i => w_old.getD i false)])
      (elimStep m acc g) := by
  obtain ⟨hwin, hlen, hi⟩ := hinv
  set w_new := wiresFrom acc.2 w_in with hw_new
  have hw_len : w_new.length = m + acc.2.length := by
    rw [hw_new, wiresFrom_length, hwin]
  set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
  have hins_len : ins.length ≤ 2 := by simp [hins]; exact hok.2
  have hins_val : ∀ s ∈ ins, statValid w_new.length s := by
    intro s hs
    obtain ⟨idx, _, rfl⟩ := List.mem_map.1 hs
    rw [hw_len]
    exact (hi idx).1
  have hsound := simplifyGate_sound g.op hok.1 w_new ins hins_len hins_val
  rw [hw_len] at hsound
  refine ⟨hwin, by simp [elimStep, hlen], ?_⟩
  intro i
  simp only [elimStep]
  by_cases hieq : i = acc.1.length
  · rw [getD_snoc_eq _ _ _ _ hieq, getD_snoc_eq _ _ _ _ (by omega)]
    refine ⟨?_, ?_⟩
    · rw [List.length_append, ← Nat.add_assoc]
      exact hsound.1
    · rw [wiresFrom_append, ← hw_new, hsound.2]
      congr 1
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro idx _
      exact (hi idx).2
  · rw [getD_snoc_ne _ _ _ _ hieq, getD_snoc_ne _ _ _ _ (by omega)]
    have ⟨hv, hval⟩ := hi i
    refine ⟨?_, ?_⟩
    · cases hst : acc.1.getD i (Sum.inl false) with
      | inl c => trivial
      | inr j =>
        rw [hst] at hv
        simp only [statValid, List.length_append] at hv ⊢
        omega
    · cases hst : acc.1.getD i (Sum.inl false) with
      | inl c =>
        rw [hst] at hval
        exact hval
      | inr j =>
        rw [hst] at hv hval
        simp only [statValid] at hv
        simp only [statVal] at hval ⊢
        rw [wiresFrom_append, ← hw_new, wiresFrom_getD_lt _ _ _ (by omega)]
        exact hval

private lemma elimInv_pass (m : ℕ) (w_in : List Bool) (gs : List Gate)
    (w_old : List Bool) (acc : List (Bool ⊕ ℕ) × List Gate)
    (hok : ∀ g ∈ gs, OkGate g) (hinv : ElimInv m w_in w_old acc) :
    ElimInv m w_in (wiresFrom gs w_old) (elimPass m gs acc) := by
  induction gs generalizing w_old acc with
  | nil => exact hinv
  | cons g gs ih =>
    rw [wiresFrom_cons, elimPass_cons]
    exact ih _ _ (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (elimInv_step m w_in w_old acc g (hok g List.mem_cons_self) hinv)

private lemma ofFn_getD_lt {α : Type*} {m : ℕ} (f : Fin m → α) (d : α) (i : ℕ) (hi : i < m) :
    (List.ofFn f).getD i d = f ⟨i, hi⟩ := by
  rw [List.getD_eq_getElem _ _ (by simp; exact hi), List.getElem_ofFn]

private def readsPair (u v : ℕ) (g : Gate) : Bool :=
  decide (u ∈ g.inputs ∨ v ∈ g.inputs)

def directReaders {n : ℕ} (C : Circuit) (u v : Fin n) : ℕ :=
  ((C.gates.map normGate).filter (readsPair u v)).length

private theorem elimPass_count_pair (n u v : ℕ) (gs : List Gate)
    (hgs : ∀ g ∈ gs, NOkGate g) (acc : List (Bool ⊕ ℕ) × List Gate)
    (hu : u < acc.1.length) (hv : v < acc.1.length)
    (hU : acc.1.getD u (Sum.inl false) = Sum.inl false)
    (hV : acc.1.getD v (Sum.inl false) = Sum.inl false) :
    (elimPass n gs acc).2.length + (gs.filter (readsPair u v)).length ≤
      acc.2.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp [elimPass]
  | cons g gs ih =>
    let next := elimStep n acc g
    have hu' : u < next.1.length := by
      simp only [next, elimStep, List.length_append, List.length_singleton]
      omega
    have hv' : v < next.1.length := by
      simp only [next, elimStep, List.length_append, List.length_singleton]
      omega
    have hU' : next.1.getD u (Sum.inl false) = Sum.inl false := by
      simpa only [next, elimStep, getD_snoc_lt _ _ _ _ hu] using hU
    have hV' : next.1.getD v (Sum.inl false) = Sum.inl false := by
      simpa only [next, elimStep, getD_snoc_lt _ _ _ _ hv] using hV
    have ht := ih (fun a ha => hgs a (List.mem_cons_of_mem _ ha)) next hu' hv' hU' hV'
    have hg := hgs g List.mem_cons_self
    rw [elimPass_cons, List.filter_cons, List.length_cons]
    change (elimPass n gs next).2.length + _ ≤ acc.2.length + (gs.length + 1)
    by_cases h : u ∈ g.inputs ∨ v ∈ g.inputs
    · have hc : Sum.inl false ∈ g.inputs.map (fun i => acc.1.getD i (Sum.inl false)) := by
        rcases h with h | h
        · exact List.mem_map.mpr ⟨u, h, hU⟩
        · exact List.mem_map.mpr ⟨v, h, hV⟩
      have hdrop := simplifyGate_none_of_const g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false)) hg.1.1
        (by simpa using hg.1.2) (by simpa using hg.2) ⟨false, hc⟩
      have hn : next.2.length = acc.2.length := by
        simp only [next, elimStep, hdrop, Option.toList_none, List.append_nil]
      simp [readsPair, h] at ht ⊢
      omega
    · have hn : next.2.length ≤ acc.2.length + 1 := by
        simp only [next, elimStep, List.length_append]
        exact Nat.add_le_add_left (toList_opt_len_le _) _
      simp [readsPair, h] at ht ⊢
      omega

private def initPair {n : ℕ} (u v : Fin n) : List (Bool ⊕ ℕ) :=
  List.ofFn fun i : Fin n => if i = u ∨ i = v then Sum.inl false else Sum.inr i.val

private theorem elimInv_initPair {n : ℕ} (u v : Fin n) (x : Fin n → Bool) :
    ElimInv n (List.ofFn x) (List.ofFn (Function.update (Function.update x u false) v false))
      (initPair u v, []) := by
  refine ⟨by simp, by simp [initPair], ?_⟩
  intro i
  by_cases hi : i < n
  · let p : Fin n := ⟨i, hi⟩
    have hget : (initPair u v).getD i (Sum.inl false) =
        if p = u ∨ p = v then Sum.inl false else Sum.inr i := by
      rw [initPair, ofFn_getD_lt _ _ _ hi]
    change statValid (n + 0) ((initPair u v).getD i (Sum.inl false)) ∧
      statVal (List.ofFn x) ((initPair u v).getD i (Sum.inl false)) =
        (List.ofFn (Function.update (Function.update x u false) v false)).getD i false
    rw [hget, ofFn_getD_lt _ _ _ hi]
    change _ ∧ _ = Function.update (Function.update x u false) v false p
    by_cases hv : p = v
    · simp [hv, statValid, statVal]
    · rw [Function.update_of_ne hv]
      by_cases hu : p = u
      · simp [hu, statValid, statVal]
      · simp [hu, hv, statValid, statVal, hi]
        rfl
  · change statValid (n + 0) ((initPair u v).getD i (Sum.inl false)) ∧
      statVal (List.ofFn x) ((initPair u v).getD i (Sum.inl false)) =
        (List.ofFn (Function.update (Function.update x u false) v false)).getD i false
    rw [List.getD_eq_default _ _ (by simpa [initPair] using Nat.le_of_not_gt hi),
      List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hi)]
    exact ⟨trivial, rfl⟩

theorem deletePair_circuit {n : ℕ} {G : SimpleGraph (Fin n)} {u v : Fin n}
    (huv : u ≠ v) (C : Circuit) (hgood : FanInTwo C)
    (heval : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = edgeValue G x) :
    ∃ D : Circuit, FanInTwo D ∧ D.size + directReaders C u v ≤ C.size ∧
      ∀ x : Fin n → Bool, D.eval (List.ofFn x) = edgeValue (deletePair G u v) x := by
  let gs := C.gates.map normGate
  let start : List (Bool ⊕ ℕ) × List Gate := (initPair u v, [])
  let acc := elimPass n gs start
  have hg : ∀ g ∈ gs, NOkGate g := by
    intro g hm
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hm
    exact normGate_nok a (hgood a ha)
  have hu : u.val < start.1.length := by simp [start, initPair]
  have hv : v.val < start.1.length := by simp [start, initPair]
  have hU : start.1.getD u.val (Sum.inl false) = Sum.inl false := by
    simp [start, initPair]
  have hV : start.1.getD v.val (Sum.inl false) = Sum.inl false := by
    simp [start, initPair]
  have hcount : acc.2.length + directReaders C u v ≤ C.size := by
    have h := elimPass_count_pair n u.val v.val gs hg start hu hv hU hV
    simpa [start, gs, directReaders, acc, Circuit.size] using h
  have hOk : ∀ g ∈ acc.2, OkGate g := elimPass_ok n gs start (by simp [start])
  have hval (x : Fin n → Bool) :
      statVal (wiresFrom acc.2 (List.ofFn x)) (acc.1.getD C.output (Sum.inl false)) =
        edgeValue (deletePair G u v) x := by
    have hi := elimInv_pass n (List.ofFn x) gs _ start
      (fun a ha => (hg a ha).1) (elimInv_initPair u v x)
    have he := (hi.2.2 C.output).2
    change statVal (wiresFrom acc.2 (List.ofFn x)) (acc.1.getD C.output (Sum.inl false)) =
      (wiresFrom (C.gates.map normGate)
        (List.ofFn (Function.update (Function.update x u false) v false))).getD C.output false at he
    rw [wiresFrom_norm] at he
    exact he.trans ((heval _).trans (cofactor_false_false G huv x))
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inr out =>
    refine ⟨⟨acc.2, out⟩, hOk, hcount, fun x => ?_⟩
    have hx := hval x
    rw [hst] at hx
    exact hx
  | inl b =>
    have hb : b = false := by
      have hx := hval (fun _ => false)
      rw [hst] at hx
      simpa [statVal, edgeValue] using hx
    refine ⟨⟨acc.2, n + acc.2.length⟩, hOk, hcount, fun x => ?_⟩
    change (wiresFrom acc.2 (List.ofFn x)).getD (n + acc.2.length) false = _
    rw [List.getD_eq_default _ _ (by simp [wiresFrom_length])]
    have hx := hval x
    rwa [hst, hb] at hx

private def readsFrozen (F : Finset ℕ) (g : Gate) : Bool :=
  g.inputs.any (fun j => decide (j ∈ F))

private theorem false_and (m : ℕ) (ins : List (Bool ⊕ ℕ)) (hlen : ins.length ≤ 2)
    (h : Sum.inl false ∈ ins) : (simplifyGate GateOp.and m ins).2 = Sum.inl false := by
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c,l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
    simp_all [simplifyGate,simpAnd]; grind

private theorem elimPass_count_frozen (n : ℕ) (gs : List Gate) (F : Finset ℕ)
    (hgs : ∀ g ∈ gs, NOkGate g) (acc : List (Bool ⊕ ℕ) × List Gate)
    (hf : ∀ j ∈ F, acc.1.getD j (Sum.inl false) = Sum.inl false)
    (hsrc : ∀ i : Fin gs.length, acc.1.length + i.val ∈ F →
      gs[i].op = .and ∧ ∃ j ∈ gs[i].inputs, j ∈ F) :
    (elimPass n gs acc).2.length + (gs.filter (readsFrozen F)).length ≤ acc.2.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp [elimPass]
  | cons g gs ih =>
    let next := elimStep n acc g
    have hg := hgs g List.mem_cons_self
    have hlen : next.1.length = acc.1.length + 1 := by simp [next,elimStep]
    let ins := g.inputs.map (fun j => acc.1.getD j (Sum.inl false))
    have hconst (h : ∃ j ∈ g.inputs, j ∈ F) : Sum.inl false ∈ ins := by
      obtain ⟨j,hj,hf'⟩ := h
      exact List.mem_map.mpr ⟨j,hj,hf j hf'⟩
    have hnext : ∀ j ∈ F, next.1.getD j (Sum.inl false) = Sum.inl false := by
      intro j hj
      by_cases e : j = acc.1.length
      · subst j
        obtain ⟨hop,hreads⟩ := hsrc ⟨0,by simp⟩ (by simpa using hj)
        change g.op = .and at hop
        change ∃ j ∈ g.inputs, j ∈ F at hreads
        simp only [next,elimStep,getD_snoc_eq _ _ _ _ rfl,hop]
        exact false_and _ ins (by simpa [ins] using hg.1.2) (hconst hreads)
      · simpa only [next,elimStep,getD_snoc_ne _ _ _ _ e] using hf j hj
    have hsrc' : ∀ i : Fin gs.length, next.1.length + i.val ∈ F →
        gs[i].op = .and ∧ ∃ j ∈ gs[i].inputs, j ∈ F := by
      intro i hi
      apply hsrc (i.succ)
      simpa only [hlen,Fin.val_succ,Nat.add_right_comm _ 1,Nat.add_assoc] using hi
    have ht := ih (fun a ha => hgs a (List.mem_cons_of_mem _ ha)) next hnext hsrc'
    rw [elimPass_cons,List.filter_cons,List.length_cons]
    change (elimPass n gs next).2.length + _ ≤ acc.2.length + (gs.length + 1)
    by_cases h : ∃ j ∈ g.inputs, j ∈ F
    · have hdrop := simplifyGate_none_of_const g.op (n + acc.2.length) ins hg.1.1
        (by simpa [ins] using hg.1.2) (by simpa [ins] using hg.2) ⟨false,hconst h⟩
      have hn : next.2.length = acc.2.length := by
        change (acc.2 ++ (simplifyGate g.op (n + acc.2.length) ins).1.toList).length = _
        rw [hdrop]; simp
      have hr : readsFrozen F g = true := by simpa [readsFrozen] using h
      simp [hr] at ht ⊢; omega
    · have hn : next.2.length ≤ acc.2.length + 1 := by
        simp only [next,elimStep,List.length_append]
        exact Nat.add_le_add_left (toList_opt_len_le _) _
      have hr : readsFrozen F g = false := Bool.eq_false_iff.mpr (by simpa [readsFrozen] using h)
      simp [hr] at ht ⊢; omega

def frozenReaders (C : Circuit) (F : Finset ℕ) : ℕ :=
  ((C.gates.map normGate).filter (readsFrozen F)).length

def frozenCertificate {n : ℕ} (C : Circuit) (u v : Fin n) (F : Finset ℕ) : Prop :=
  (∀ a : Fin n, a.val ∈ F → a = u ∨ a = v) ∧
  ∀ i : Fin (C.gates.map normGate).length, n + i.val ∈ F →
    (C.gates.map normGate)[i].op = .and ∧ ∃ j ∈ (C.gates.map normGate)[i].inputs, j ∈ F

theorem deletePair_circuit_frozen {n : ℕ} {G : SimpleGraph (Fin n)} {u v : Fin n}
    (huv : u ≠ v) (C : Circuit) (hgood : FanInTwo C)
    (F : Finset ℕ) (hF : frozenCertificate C u v F)
    (heval : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = edgeValue G x) :
    ∃ D : Circuit, FanInTwo D ∧ D.size + frozenReaders C F ≤ C.size ∧
      ∀ x : Fin n → Bool, D.eval (List.ofFn x) = edgeValue (deletePair G u v) x := by
  let gs := C.gates.map normGate
  let start : List (Bool ⊕ ℕ) × List Gate := (initPair u v, [])
  let acc := elimPass n gs start
  have hg : ∀ g ∈ gs, NOkGate g := by
    intro g hm
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hm
    exact normGate_nok a (hgood a ha)
  have hf : ∀ j ∈ F, start.1.getD j (Sum.inl false) = Sum.inl false := by
    intro j hj
    by_cases lt : j < n
    · let a : Fin n := ⟨j,lt⟩
      change (initPair u v).getD j (Sum.inl false) = _
      rw [initPair, ofFn_getD_lt _ _ _ lt]
      exact ite_eq_left (hF.1 a hj)
    · apply List.getD_eq_default
      simpa [start,initPair] using Nat.le_of_not_gt lt
  have hsource : ∀ i : Fin gs.length, start.1.length + i.val ∈ F →
      gs[i].op = .and ∧ ∃ j ∈ gs[i].inputs, j ∈ F := by
    intro i hi
    exact hF.2 i (by simpa [start,initPair] using hi)
  have hcount : acc.2.length + frozenReaders C F ≤ C.size := by
    have h := elimPass_count_frozen n gs F hg start hf hsource
    simpa [start,gs,frozenReaders,acc,Circuit.size] using h
  have hOk : ∀ g ∈ acc.2, OkGate g := elimPass_ok n gs start (by simp [start])
  have hval (x : Fin n → Bool) :
      statVal (wiresFrom acc.2 (List.ofFn x)) (acc.1.getD C.output (Sum.inl false)) =
        edgeValue (deletePair G u v) x := by
    have hi := elimInv_pass n (List.ofFn x) gs _ start
      (fun a ha => (hg a ha).1) (elimInv_initPair u v x)
    have he := (hi.2.2 C.output).2
    change statVal (wiresFrom acc.2 (List.ofFn x)) (acc.1.getD C.output (Sum.inl false)) =
      (wiresFrom (C.gates.map normGate)
        (List.ofFn (Function.update (Function.update x u false) v false))).getD C.output false at he
    rw [wiresFrom_norm] at he
    exact he.trans ((heval _).trans (cofactor_false_false G huv x))
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inr out =>
    refine ⟨⟨acc.2, out⟩, hOk, hcount, fun x => ?_⟩
    have hx := hval x
    rw [hst] at hx
    exact hx
  | inl b =>
    have hb : b = false := by
      have hx := hval (fun _ => false)
      rw [hst] at hx
      simpa [statVal, edgeValue] using hx
    refine ⟨⟨acc.2, n + acc.2.length⟩, hOk, hcount, fun x => ?_⟩
    change (wiresFrom acc.2 (List.ofFn x)).getD (n + acc.2.length) false = _
    rw [List.getD_eq_default _ _ (by simp [wiresFrom_length])]
    have hx := hval x
    rwa [hst, hb] at hx

-- If the original circuit has enough direct readers, their elimination pays
-- exactly the graph-side cost and the lower bound transfers from the cofactor.
theorem lower_bound_of_direct_readers {n : ℕ} (G : SimpleGraph (Fin n)) {u v : Fin n}
    (huv : G.Adj u v) (hu : (G.neighborSet u).ncard = 3)
    (hv : (G.neighborSet v).ncard = 3) {S T : Finset (Fin n)}
    (hS : IsMinCover G S) (hT : IsMinCover (deletePair G u v) T)
    (hcofactor : ∀ r, HasCircuitSize n (edgeValue (deletePair G u v)) r →
      (deletePair G u v).edgeSet.ncard + T.card ≤ r + 1)
    (C : Circuit) (hgood : FanInTwo C)
    (heval : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = edgeValue G x)
    (hread : (@ite ℕ (hasNeighborCover G u v) (Classical.propDecidable _) 6 7) ≤
      directReaders C u v) :
    G.edgeSet.ncard + S.card ≤ C.size + 1 := by
  have hcost := deletion_cost G huv hu hv hS hT
  obtain ⟨D, hD, hcount, he⟩ := deletePair_circuit huv.ne C hgood heval
  have hbound := hcofactor D.size ⟨D, hD, le_rfl, he⟩
  omega

theorem lower_bound_of_frozen_readers {n : ℕ} (G : SimpleGraph (Fin n)) {u v : Fin n}
    (huv : G.Adj u v) (hu : (G.neighborSet u).ncard = 3)
    (hv : (G.neighborSet v).ncard = 3) {S T : Finset (Fin n)}
    (hS : IsMinCover G S) (hT : IsMinCover (deletePair G u v) T)
    (hcofactor : ∀ r, HasCircuitSize n (edgeValue (deletePair G u v)) r →
      (deletePair G u v).edgeSet.ncard + T.card ≤ r + 1)
    (C : Circuit) (hgood : FanInTwo C)
    (F : Finset ℕ) (hF : frozenCertificate C u v F)
    (heval : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = edgeValue G x)
    (hread : (@ite ℕ (hasNeighborCover G u v) (Classical.propDecidable _) 6 7) ≤
      frozenReaders C F) :
    G.edgeSet.ncard + S.card ≤ C.size + 1 := by
  have hcost := deletion_cost G huv hu hv hS hT
  obtain ⟨D, hD, hcount, he⟩ := deletePair_circuit_frozen huv.ne C hgood F hF heval
  have hbound := hcofactor D.size ⟨D, hD, le_rfl, he⟩
  omega

private theorem count_positions {α : Type} (l : List α) (p : α → Bool) :
    (Finset.univ.filter (fun i : Fin l.length => p l[i] = true)).card = (l.filter p).length := by
  classical
  have count : (∑ i : Fin l.length, if p l[i] then (1 : ℕ) else 0) = (l.filter p).length := by
    induction l with
    | nil => simp
    | cons a l ih =>
      change (∑ i : Fin (l.length + 1), if p (a :: l)[i.val] then 1 else 0) = _
      rw [Fin.sum_univ_succ]
      simp only [List.getElem_cons_zero, Fin.val_zero, Fin.val_succ, List.getElem_cons_succ]
      change (if p a then 1 else 0) + (∑ i : Fin l.length, if p l[i] then 1 else 0) = _
      rw [ih,List.filter_cons]
      split <;> simp_all [Nat.add_comm]
  simpa using count

-- Five distinct raw AND gates freeze at zero. Each live output has a reader,
-- and a two-input gate can read at most two of the frozen outputs.
theorem saving_eight_of_five_live_products {n : ℕ} (C : Circuit)
    (fan : FanInTwo C) (u v : Fin n)
    (S : Finset (Fin (C.gates.map normGate).length)) (hfive : 5 ≤ S.card)
    (hs : ∀ i ∈ S, (C.gates.map normGate)[i].op = .and ∧
      (u.val ∈ (C.gates.map normGate)[i].inputs ∨ v.val ∈ (C.gates.map normGate)[i].inputs) ∧
      ∀ j ∈ (C.gates.map normGate)[i].inputs, j < n)
    (hlive : ∀ i ∈ S, ∃ j : Fin (C.gates.map normGate).length,
      n + i.val ∈ (C.gates.map normGate)[j].inputs) :
    ∃ F : Finset ℕ, frozenCertificate C u v F ∧ 8 ≤ frozenReaders C F := by
  classical
  let gs := C.gates.map normGate
  let wire : Fin gs.length → ℕ := fun i => n + i.val
  have hinj : Function.Injective wire := by intro i j h; apply Fin.ext; exact Nat.add_left_cancel h
  let W := S.image wire
  let F : Finset ℕ := {u.val,v.val} ∪ W
  have hw (i : Fin gs.length) : wire i ∈ W ↔ i ∈ S := by
    simp [W,Finset.mem_image,hinj.eq_iff]
  have ha (i : Fin gs.length) : wire i ∈ F ↔ i ∈ S := by
    have hn : n ≤ wire i := Nat.le_add_right _ _
    have h1 := u.isLt; have h2 := v.isLt
    simp [F, (show wire i ≠ u.val by omega), (show wire i ≠ v.val by omega), hw]
  have hf : frozenCertificate C u v F := by
    constructor
    · intro a h
      rcases Finset.mem_union.mp h with h | h
      · simpa [Fin.ext_iff] using h
      · obtain ⟨j,_,hj⟩ := Finset.mem_image.mp h
        have := a.isLt; dsimp [wire] at hj; omega
    · intro i hi
      have hm := (ha i).mp hi
      obtain ⟨hop,hraw,_⟩ := hs i hm
      refine ⟨hop,?_⟩
      rcases hraw with h | h
      · exact ⟨u.val,h,by simp [F]⟩
      · exact ⟨v.val,h,by simp [F]⟩
  let I := Finset.univ.filter fun i : Fin gs.length => readsFrozen F gs[i] = true
  have hI (i : Fin gs.length) : i ∈ I ↔ ∃ j ∈ gs[i].inputs, j ∈ F := by simp [I,readsFrozen]
  have hSI : S ⊆ I := by
    intro i hi
    exact (hI i).mpr ((hf.2 i ((ha i).mpr hi)).2)
  let R := I \ S
  have hc : W ⊆ R.biUnion (fun j => gs[j].inputs.toFinset) := by
    intro w h
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp h
    obtain ⟨j,hj⟩ := hlive i hi
    have hjI : j ∈ I := (hI j).mpr ⟨wire i,hj,(ha i).mpr hi⟩
    have hjS : j ∉ S := by
      intro hjS
      have lt := (hs j hjS).2.2 (wire i) hj
      dsimp [wire] at lt; omega
    exact Finset.mem_biUnion.mpr ⟨j,Finset.mem_sdiff.mpr ⟨hjI,hjS⟩,List.mem_toFinset.mpr hj⟩
  have hg (j : Fin gs.length) : gs[j].inputs.toFinset.card ≤ 2 := by
    have hm : gs[j] ∈ gs := List.getElem_mem _
    obtain ⟨a,ha,he⟩ := List.mem_map.mp hm
    exact (List.toFinset_card_le _).trans (he ▸ (normGate_nok a (fan a ha)).1.2)
  have hh : S.card ≤ R.card * 2 := by
    calc
      S.card = W.card := (Finset.card_image_of_injective _ hinj).symm
      _ ≤ _ := Finset.card_le_card hc
      _ ≤ _ := Finset.card_biUnion_le
      _ ≤ ∑ _j ∈ R, 2 := Finset.sum_le_sum fun j _ => hg j
      _ = _ := by simp
  have hsplit : R.card + S.card = I.card := Finset.card_sdiff_add_card_eq_card hSI
  have hcount : I.card = frozenReaders C F := count_positions gs (readsFrozen F)
  exact ⟨F,hf,by omega⟩

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
      g.op.eval (g.inputs.map fun j => (wiresFrom pre x).getD j false) =
      g.op.eval (g.inputs.map fun j => (wiresFrom pre y).getD j false)) :
    agreeOff (wiresFrom gs x) (wiresFrom gs y) v := by
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
    change agreeOff (wiresFrom gs (x ++ [eval x])) (wiresFrom gs (y ++ [eval y])) v
    apply ih _ _ (by simp [hl])
    · rw [hg]; exact agreeOff_snoc hl h
    · intro pre g' tail he hr
      exact hread (g :: pre) g' tail (by simp [he]) hr

private theorem run_input (gs : List Gate) (x : List Bool) {j : ℕ} (hj : j < x.length) :
    (wiresFrom gs x).getD j false = x.getD j false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    change (wiresFrom gs (x ++ [_])).getD j false = _
    rw [ih _ (by simp; omega), List.getD_append _ _ _ _ hj]

private def pin {n : ℕ} (x : Fin n → Bool) (v : Fin n) (c : Bool) :=
  List.ofFn (Function.update x v c)

private theorem raw_get {n : ℕ} (x : Fin n → Bool) (a : Fin n) :
    (List.ofFn x).getD a.val false = x a := by
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]

private theorem pin_agree {n : ℕ} (x : Fin n → Bool) (v : Fin n) :
    agreeOff (pin x v false) (pin x v true) v.val := by
  intro j hj
  by_cases hj' : j < n
  · have hn : (⟨j,hj'⟩ : Fin n) ≠ v := by intro e; exact hj (congrArg Fin.val e)
    change (List.ofFn _).getD (⟨j,hj'⟩ : Fin n).val false = (List.ofFn _).getD (⟨j,hj'⟩ : Fin n).val false
    rw [raw_get, raw_get, Function.update_of_ne hn, Function.update_of_ne hn]
  · rw [List.getD_eq_default _ _ (by simp [pin]; omega),
        List.getD_eq_default _ _ (by simp [pin]; omega)]

private theorem pin_get {n : ℕ} (x : Fin n → Bool) (v a : Fin n) (c : Bool) (pre : List Gate) :
    (wiresFrom pre (pin x v c)).getD a.val false = Function.update x v c a := by
  rw [run_input _ _ (by simp [pin])]
  exact raw_get _ _

-- A controlling raw input fixes the output of this AND or OR gate.
def blockedBy {n : ℕ} (v a : Fin n) (p : Bool) (g : Gate) : Prop :=
  (g.inputs = [v.val,a.val] ∨ g.inputs = [a.val,v.val]) ∧
    ((g.op = .and ∧ p = false) ∨ (g.op = .or ∧ p = true))

private theorem blocked_eval {n : ℕ} {v a : Fin n} (ha : v ≠ a) {p : Bool}
    {g : Gate} (hb : blockedBy v a p g) {x : Fin n → Bool} (hx : x a = p) (pre : List Gate) :
    g.op.eval (g.inputs.map fun j => (wiresFrom pre (pin x v false)).getD j false) =
    g.op.eval (g.inputs.map fun j => (wiresFrom pre (pin x v true)).getD j false) := by
  rcases hb with ⟨hin, hop⟩
  rcases hin with hin | hin <;> rcases hop with ⟨hop,rfl⟩ | ⟨hop,rfl⟩ <;>
    simp only [hin, hop, List.map_cons, List.map_nil, pin_get, Function.update_of_ne ha.symm, hx] <;>
    simp [GateOp.eval]

def productAt {n : ℕ} (v w : Fin n) (g : Gate) : Prop :=
  g.op = .and ∧ (g.inputs = [v.val,w.val] ∨ g.inputs = [w.val,v.val])

def pairReadersAt {n : ℕ} (gs : List Gate) (v : Fin n) : Prop :=
  ∀ g ∈ gs, v.val ∈ g.inputs → ∃ a : Fin n, v ≠ a ∧ productAt v a g

theorem every_incident_product {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate)
    (out : ℕ) (heval : ∀ x : Fin n → Bool, (wiresFrom gs (List.ofFn x)).getD out false = edgeValue G x)
    {v w : Fin n} (hw : G.Adj v w) (hread : pairReadersAt gs v) :
    ∃ g ∈ gs, productAt v w g := by
  classical
  let x : Fin n → Bool := fun a => decide (a = w)
  have hlow : edgeValue G (Function.update x v false) = false := by
    simp only [edgeValue,decide_eq_false_iff_not]
    rintro ⟨i,j,hij,hi,hj⟩
    have hfix (a : Fin n) (h : Function.update x v false a = true) : a = w := by
      by_cases e : a = v
      · subst a; simp at h
      · simpa [x,Function.update_of_ne e] using h
    exact hij.ne ((hfix i hi).trans (hfix j hj).symm)
  have hhigh : edgeValue G (Function.update x v true) = true := by
    simp only [edgeValue,decide_eq_true_eq]
    exact ⟨v,w,hw,by simp,by simp [x,Function.update_of_ne hw.ne.symm]⟩
  have hout : out ≠ v.val := by
    intro e; subst out
    let y : Fin n → Bool := fun a => decide (a = v)
    have h := heval y
    rw [run_input _ _ (by simp),raw_get] at h
    simpa [y,edgeValue] using h
  by_contra! hmiss
  have h := run_agreeOff gs (pin x v false) (pin x v true) v.val
    (by simp [pin]) (pin_agree x v) (by
      intro pre g tail e hraw
      have hm : g ∈ gs := by rw [e]; simp
      obtain ⟨a,hva,hp⟩ := hread g hm hraw
      have haw : a ≠ w := by intro h; subst a; exact hmiss g hm hp
      exact blocked_eval hva ⟨hp.2,Or.inl ⟨hp.1,rfl⟩⟩ (by simp [x,haw]) pre)
  have hh := h out hout
  change (wiresFrom gs (List.ofFn (Function.update x v false))).getD out false =
    (wiresFrom gs (List.ofFn (Function.update x v true))).getD out false at hh
  rw [heval,heval,hlow,hhigh] at hh
  contradiction

end PEqualNP.Outside.L_meta_519

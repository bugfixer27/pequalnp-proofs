import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_652

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

private def readsOne (u : ℕ) (g : Gate) : Bool := decide (u ∈ g.inputs)

def inputReaders {n : ℕ} (C : Circuit) (u : Fin n) : ℕ :=
  ((C.gates.map normGate).filter (readsOne u.val)).length

private theorem elimPass_count_pin (n u : ℕ) (b : Bool) (gs : List Gate)
    (hgs : ∀ g ∈ gs, NOkGate g) (acc : List (Bool ⊕ ℕ) × List Gate)
    (hu : u < acc.1.length)
    (hU : acc.1.getD u (Sum.inl false) = Sum.inl b)
    :
    (elimPass n gs acc).2.length + (gs.filter (readsOne u)).length ≤
      acc.2.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp [elimPass]
  | cons g gs ih =>
    let next := elimStep n acc g
    have hu' : u < next.1.length := by
      simp only [next, elimStep, List.length_append, List.length_singleton]
      omega
    have hU' : next.1.getD u (Sum.inl false) = Sum.inl b := by
      simpa only [next, elimStep, getD_snoc_lt _ _ _ _ hu] using hU
    have ht := ih (fun a ha => hgs a (List.mem_cons_of_mem _ ha)) next hu' hU'
    have hg := hgs g List.mem_cons_self
    rw [elimPass_cons, List.filter_cons, List.length_cons]
    change (elimPass n gs next).2.length + _ ≤ acc.2.length + (gs.length + 1)
    by_cases h : u ∈ g.inputs
    · have hc : Sum.inl b ∈ g.inputs.map (fun i => acc.1.getD i (Sum.inl false)) := by
        exact List.mem_map.mpr ⟨u,h,hU⟩
      have hdrop := simplifyGate_none_of_const g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false)) hg.1.1
        (by simpa using hg.1.2) (by simpa using hg.2) ⟨b, hc⟩
      have hn : next.2.length = acc.2.length := by
        simp only [next, elimStep, hdrop, Option.toList_none, List.append_nil]
      simp [readsOne, h] at ht ⊢
      omega
    · have hn : next.2.length ≤ acc.2.length + 1 := by
        simp only [next, elimStep, List.length_append]
        exact Nat.add_le_add_left (toList_opt_len_le _) _
      simp [readsOne, h] at ht ⊢
      omega

private def initProjection {n m : ℕ} (π : Fin n → Bool ⊕ Fin m) : List (Bool ⊕ ℕ) :=
  List.ofFn fun i => (π i).map id Fin.val

def liftProjection {n m : ℕ} (π : Fin n → Bool ⊕ Fin m) (x : Fin m → Bool) (i : Fin n) : Bool :=
  (π i).elim id x

private theorem elimInv_projection {n m : ℕ} (π : Fin n → Bool ⊕ Fin m) (x : Fin m → Bool) :
    ElimInv m (List.ofFn x) (List.ofFn (liftProjection π x)) (initProjection π, []) := by
  refine ⟨by simp,by simp [initProjection],?_⟩
  intro i
  by_cases hi : i < n
  · change statValid (m + 0) ((initProjection π).getD i (Sum.inl false)) ∧
      statVal (List.ofFn x) ((initProjection π).getD i (Sum.inl false)) = _
    rw [initProjection,ofFn_getD_lt _ _ _ hi,ofFn_getD_lt _ _ _ hi]
    cases h : π ⟨i,hi⟩ with
    | inl b => simp [statValid,statVal,liftProjection,h]
    | inr j =>
      simp only [Sum.map_inr,statValid,Nat.add_zero,statVal,liftProjection,h,Sum.elim_inr]
      exact ⟨j.isLt,ofFn_getD_lt _ _ _ j.isLt⟩
  · change statValid (m + 0) ((initProjection π).getD i (Sum.inl false)) ∧
      statVal (List.ofFn x) ((initProjection π).getD i (Sum.inl false)) = _
    rw [List.getD_eq_default _ _ (by simpa [initProjection] using Nat.le_of_not_gt hi),
        List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hi)]
    exact ⟨trivial,rfl⟩

-- One projection works simultaneously for every chosen output wire.
theorem project_outputs {n m t : ℕ} (π : Fin n → Bool ⊕ Fin m) (v : Fin n) (b : Bool)
    (hp : π v = Sum.inl b) (C : Circuit) (fan : FanInTwo C) (out : Fin t → ℕ)
    (hz : ∀ i, ∃ x : Fin m → Bool, (C.wires (List.ofFn (liftProjection π x))).getD (out i) false = false) :
    ∃ D : Circuit, FanInTwo D ∧ D.size + inputReaders C v ≤ C.size ∧ ∃ out' : Fin t → ℕ,
      ∀ x : Fin m → Bool, ∀ i, (D.wires (List.ofFn x)).getD (out' i) false =
        (C.wires (List.ofFn (liftProjection π x))).getD (out i) false := by
  let gs := C.gates.map normGate
  let start : List (Bool ⊕ ℕ) × List Gate := (initProjection π,[])
  let acc := elimPass m gs start
  have hg : ∀ g ∈ gs, NOkGate g := by
    intro g hm; obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm; exact normGate_nok a (fan a ha)
  have hv : v.val < start.1.length := by simp [start,initProjection]
  have hval : start.1.getD v.val (Sum.inl false) = Sum.inl b := by
    change (initProjection π).getD v.val (Sum.inl false) = _
    rw [initProjection,ofFn_getD_lt _ _ _ v.isLt]; simp [hp]
  have hc : acc.2.length + inputReaders C v ≤ C.size := by
    have h := elimPass_count_pin m v.val b gs hg start hv hval
    simpa [gs,acc,start,inputReaders,Circuit.size] using h
  have hgood := elimPass_ok m gs start (by simp [start])
  let D : Circuit := ⟨acc.2,0⟩
  let out' (i : Fin t) := (acc.1.getD (out i) (Sum.inl false)).elim (fun _ => m + acc.2.length) id
  have hs (x : Fin m → Bool) (i : Fin t) :
      statVal (wiresFrom acc.2 (List.ofFn x)) (acc.1.getD (out i) (Sum.inl false)) =
        (C.wires (List.ofFn (liftProjection π x))).getD (out i) false := by
    have h := ((elimInv_pass m (List.ofFn x) gs _ start
      (fun a ha => (hg a ha).1) (elimInv_projection π x)).2.2 (out i)).2
    change _ = (wiresFrom (C.gates.map normGate) (List.ofFn (liftProjection π x))).getD (out i) false at h
    rwa [wiresFrom_norm] at h
  refine ⟨D,hgood,hc,out',?_⟩
  intro x i
  cases h : acc.1.getD (out i) (Sum.inl false) with
  | inr j =>
    change (wiresFrom acc.2 (List.ofFn x)).getD (out' i) false = _
    simpa only [out',h,Sum.elim_inr,id_eq,statVal] using hs x i
  | inl c =>
    obtain ⟨x0,h0⟩ := hz i
    have hcx := hs x0 i
    rw [h,h0] at hcx
    have hb : c = false := hcx
    change (wiresFrom acc.2 (List.ofFn x)).getD (out' i) false = _
    rw [show out' i = m + acc.2.length by simp only [out',h,Sum.elim_inl]]
    rw [List.getD_eq_default _ _ (by simp [wiresFrom_length])]
    have hx := hs x i; rwa [h,hb] at hx

theorem readers_le_two_of_cofactor_twelve {n m t : ℕ} (π : Fin n → Bool ⊕ Fin m)
    (v : Fin n) (hp : π v = Sum.inl true) (C : Circuit) (fan : FanInTwo C)
    (hsmall : C.size ≤ 14) (out : Fin t → ℕ) (f : (Fin m → Bool) → Fin t → Bool)
    (heval : ∀ x i, (C.wires (List.ofFn (liftProjection π x))).getD (out i) false = f x i)
    (hz : ∀ i, ∃ x, f x i = false)
    (hmin : ∀ D : Circuit, FanInTwo D → ∀ out' : Fin t → ℕ,
      (∀ x i, (D.wires (List.ofFn x)).getD (out' i) false = f x i) → 12 ≤ D.size) :
    inputReaders C v ≤ 2 := by
  obtain ⟨D,hD,hcount,out',h⟩ := project_outputs π v true hp C fan out (fun i => by
    obtain ⟨x,hx⟩ := hz i
    exact ⟨x,(heval x i).trans hx⟩)
  have hd := hmin D hD out' (fun x i => (h x i).trans (heval x i))
  omega

end PEqualNP.Outside.L_meta_652

import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_652

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev Word := BitVec 64
abbrev Code := Fin 3 × Fin 22 × Fin 22

def column : Fin 6 → Word := ![12297829382473034410,14757395258967641292,
  17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320]

private def row (r : Fin 64) (v : Fin 6) : Bool := (column v).getLsbD r.val

private def port (j : Option ℕ) (defaultOne : Bool) : Fin 22 :=
  match j with
  | none => if defaultOne then 1 else 0
  | some t => if ht : t+2 < 22 then ⟨t+2,ht⟩ else 0

private def encode (g : Gate) : Code :=
  let a := g.inputs[0]?
  let b := g.inputs[1]?
  match g.op with
  | .and => (0,port a true,port b true)
  | .or => (1,port a false,port b false)
  | _ => (2,port a false,0)

private def evalBool (c : Code) (w : List Bool) : Bool :=
  let a := w.getD c.2.1.val false
  let b := w.getD c.2.2.val false
  if c.1 = 0 then a && b else if c.1 = 1 then a || b else !a

def evalWord (c : Code) (w : List Word) : Word :=
  let a := w.getD c.2.1.val 0
  let b := w.getD c.2.2.val 0
  if c.1 = 0 then a &&& b else if c.1 = 1 then a ||| b else ~~~a

private theorem port_get (w : List Bool) (h : w.length ≤ 20) (j : Option ℕ) (d : Bool) :
    (false :: true :: w).getD (port j d).val false = (j.map (fun t => w.getD t false)).getD d := by
  cases j with
  | none => cases d <;> rfl
  | some j =>
    by_cases hj : j + 2 < 22
    · simp only [port,dite_eq_left hj,Option.map_some,Option.getD_some]
      rfl
    · simp only [port,dite_eq_right hj,Option.map_some,Option.getD_some]
      exact (List.getD_eq_default w false (show w.length ≤ j by omega)).symm

private theorem gate_ok (g : Gate)
    (h : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (w : List Bool) (hlen : w.length ≤ 20) :
    evalBool (encode g) (false :: true :: w) = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  obtain ⟨op,ins⟩ := g
  obtain ⟨hop,hlen'⟩ := h
  change op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not at hop
  change ins.length ≤ 2 at hlen'
  rcases hop with rfl | rfl | rfl <;>
    rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨c,l⟩⟩⟩ <;>
    first | (exfalso; simp only [List.length_cons] at hlen'; omega) | (simp only [evalBool,encode]; simp only [port_get w hlen]; simp [GateOp.eval])

private def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun l g => l ++ [g.op.eval (g.inputs.map fun i => l.getD i false)]) w

private def boolRun (codes : List Code) (w : List Bool) : List Bool :=
  codes.foldl (fun l c => l ++ [evalBool c l]) w

def wordRun (codes : List Code) (w : List Word) : List Word :=
  codes.foldl (fun l c => l ++ [evalWord c l]) w

private theorem encode_ok (gs : List Gate) (w : List Bool) (hlen : w.length + gs.length ≤ 20)
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    boolRun (gs.map encode) (false :: true :: w) = false :: true :: run gs w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change boolRun (gs.map encode) ((false :: true :: w) ++ [evalBool (encode g) _]) =
      false :: true :: run gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    have h' := gate_ok g (hg g List.mem_cons_self) w (by omega)
    rw [h']
    exact ih _ (by simp at hlen ⊢; omega) (fun a ha => hg a (List.mem_cons_of_mem _ ha))

private def bits (r : Fin 64) (w : List Word) : List Bool := w.map (fun v => v.getLsbD r.val)

private theorem bits_get (w : List Word) (r : Fin 64) (j : ℕ) :
    (w.getD j 0).getLsbD r.val = (bits r w).getD j false := by
  by_cases h : j < w.length
  · rw [List.getD_eq_getElem _ _ h,List.getD_eq_getElem _ _ (by simpa [bits] using h)]
    simp [bits]
  · rw [List.getD_eq_default _ _ (by omega),List.getD_eq_default _ _ (by simp [bits]; omega)]
    simp

private theorem bit_eval (r : Fin 64) (w : List Word) (c : Code) :
    (evalWord c w).getLsbD r.val = evalBool c (bits r w) := by
  simp only [evalBool,evalWord]
  by_cases h : c.1 = 0 <;> by_cases k : c.1 = 1 <;> simp only [h,k,show (1 : Fin 3) ≠ 0 by decide,ite_true,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_or,BitVec.getLsbD_not,decide_eq_true r.isLt,Bool.true_and,bits_get]

private theorem bit_run (r : Fin 64) (codes : List Code) (w : List Word) :
    bits r (wordRun codes w) = boolRun codes (bits r w) := by
  induction codes generalizing w with
  | nil => rfl
  | cons c cs ih =>
    change bits r (wordRun cs (w ++ [evalWord c w])) = boolRun cs ((bits r w) ++ [evalBool c (bits r w)])
    rw [ih]; congr 1
    change List.map _ (w ++ [_]) = _
    rw [List.map_append]; exact congrArg (fun b => bits r w ++ [b]) (bit_eval r w c)

def initWords : List Word := 0 :: (~~~0) :: List.ofFn column

private theorem bits_init (r : Fin 64) :
    bits r initWords = false :: true :: List.ofFn (row r) := by
  change List.map _ (0 :: (~~~(0 : Word)) :: List.ofFn column) = _
  simp only [List.map_cons,BitVec.getLsbD_not,decide_eq_true r.isLt]
  have hz : (0 : Word).getLsbD r.val = false := by simp
  rw [hz]; simp [row]

private theorem run_length (gs : List Gate) (w : List Bool) :
    (run gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [run]
  | cons g gs ih =>
    change (run gs (w ++ [_])).length = _
    rw [ih]; simp; omega

theorem table_reduction (C : Circuit) (fan : FanInTwo C) (hs : C.size ≤ 14) (out : Fin 3 → ℕ) :
    ∃ codes : List Code, codes.length = C.size ∧ ∃ ports : Fin 3 → Fin 22,
      ∀ r : Fin 64, ∀ i, ((wordRun codes initWords).getD (ports i).val 0).getLsbD r.val =
        (C.wires (List.ofFn (row r))).getD (out i) false := by
  refine ⟨C.gates.map encode, by simp [Circuit.size], fun i => port (some (out i)) false,?_⟩
  intro r i
  rw [bits_get,bit_run,bits_init,encode_ok _ _ (by simpa [Circuit.size] using (show 6 + C.size ≤ 20 by omega)) fan]
  exact port_get (run C.gates (List.ofFn (row r))) (by rw [run_length]; simp; change 6 + C.size ≤ 20; omega)
    (some (out i)) false

def targetWord : Fin 3 → Word := ![
  ((column 0 &&& column 3) ||| (column 1 &&& column 4) ||| (column 2 &&& column 5)),
  ((column 0 &&& column 4) ||| (column 1 &&& column 5) ||| (column 2 &&& column 3)),
  ((column 0 &&& column 5) ||| (column 1 &&& column 3) ||| (column 2 &&& column 4))]

def realizes (cs : List Code) : Prop :=
  ∃ ports : Fin 3 → Fin 22, ∀ i, (wordRun cs initWords).getD (ports i).val 0 = targetWord i

theorem lower_of_table_exclusion
    (hexcl : ∀ cs : List Code, cs.length ≤ 14 → ¬realizes cs) :
    ¬ (∃ C : Circuit, FanInTwo C ∧ C.size ≤ 14 ∧ ∃ o0 o1 o2 : ℕ, ∀ x : Fin 6 → Bool,
      (C.wires (List.ofFn x)).getD o0 false = ((x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5)) ∧
      (C.wires (List.ofFn x)).getD o1 false = ((x 0 && x 4) || (x 1 && x 5) || (x 2 && x 3)) ∧
      (C.wires (List.ofFn x)).getD o2 false = ((x 0 && x 5) || (x 1 && x 3) || (x 2 && x 4))) := by
  rintro ⟨C, hf, hs, a,b,c,hw⟩
  obtain ⟨cs,hlen,ports,hp⟩ := table_reduction C hf hs ![a,b,c]
  apply hexcl cs (hlen ▸ hs)
  refine ⟨ports, fun i => BitVec.eq_of_getLsbD_eq (fun j hj => ?_)⟩
  let r : Fin 64 := ⟨j,hj⟩
  apply (hp r i).trans
  obtain ⟨ha,hb,hc⟩ := hw (row r)
  fin_cases i
  · simpa [row,targetWord,r] using ha
  · simpa [row,targetWord,r] using hb
  · simpa [row,targetWord,r] using hc

/-- Distinct possible next truth tables.  Equal tables share a single branch. -/
def moves (H : List Word) : List Word :=
  ((H.flatMap fun a => (~~~a) :: H.flatMap (fun b => [a &&& b,a ||| b])).eraseDups).filter
    (fun v => !(H.contains v))

private theorem move_ok (c : Code) (w H : List Word) (hz : (0 : Word) ∈ H)
    (hw : ∀ v ∈ w, v ∈ H) (hnew : evalWord c w ∉ H) : evalWord c w ∈ moves H := by
  have read (i : Nat) : w.getD i 0 ∈ H := by
    by_cases h : i < w.length
    · rw [List.getD_eq_getElem _ _ h]
      exact hw _ (List.getElem_mem _)
    · rw [List.getD_eq_default _ _ (by omega)]
      exact hz
  simp only [moves,List.mem_filter,List.mem_eraseDups]
  refine ⟨?_,by simpa using hnew⟩
  apply List.mem_flatMap.mpr
  refine ⟨_,read c.2.1.val,?_⟩
  unfold evalWord
  split
  · exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨_,read c.2.2.val,by simp⟩)
  · split
    · exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨_,read c.2.2.val,by simp⟩)
    · exact List.mem_cons_self

def matchingTargets : List Word := List.ofFn targetWord

section
variable (wanted : List Word)

def reaches : Nat → List Word → Bool
  | 0,H => wanted.all H.contains
  | n+1,H => wanted.all H.contains || (moves H).any (fun v => reaches n (v :: H))

private theorem reaches_more (n : Nat) (H : List Word) (h : reaches wanted n H = true) :
    reaches wanted (n+1) H = true := by
  induction n generalizing H with
  | zero =>
    exact Bool.or_eq_true_iff.mpr (Or.inl h)
  | succ n ih =>
    rcases Bool.or_eq_true_iff.mp h with doneH | branch
    · exact Bool.or_eq_true_iff.mpr (Or.inl doneH)
    · apply Bool.or_eq_true_iff.mpr
      right
      obtain ⟨v,hv,hr⟩ := List.any_eq_true.mp branch
      exact List.any_eq_true.mpr ⟨v,hv,ih _ hr⟩

private theorem reaches_complete (cs : List Code) (w H : List Word) (hz : (0 : Word) ∈ H)
    (hw : ∀ v ∈ w, v ∈ H) (ht : ∀ t ∈ wanted, t ∈ wordRun cs w ∨ t ∈ H) :
    reaches wanted cs.length H = true := by
  induction cs generalizing H w with
  | nil =>
    apply List.all_eq_true.mpr
    intro t h
    exact List.contains_iff_mem.mpr ((ht t h).elim (hw t) id)
  | cons c cs ih =>
    let v := evalWord c w
    have htail : wordRun (c :: cs) w = wordRun cs (w ++ [v]) := rfl
    by_cases h : v ∈ H
    · apply reaches_more wanted
      apply ih (w ++ [v]) H hz _ (htail ▸ ht)
      intro a ha
      rcases List.mem_append.mp ha with h₁ | h₂
      · exact hw _ h₁
      · simpa only [List.mem_singleton.mp h₂] using h
    · apply Bool.or_eq_true_iff.mpr
      right
      apply List.any_eq_true.mpr
      refine ⟨v,move_ok c w H hz hw h,?_⟩
      apply ih (w ++ [v]) (v::H) (List.mem_cons_of_mem _ hz)
      · intro a ha
        rcases List.mem_append.mp ha with h₁ | h₂
        · exact List.mem_cons_of_mem _ (hw _ h₁)
        · simpa only [List.mem_singleton.mp h₂] using (List.mem_cons_self : v ∈ v::H)
      · intro t ht'
        exact ((htail ▸ ht) t ht').imp_right (List.mem_cons_of_mem _)

theorem exclusion_of_search (no : reaches matchingTargets 14 initWords = false) :
    ∀ cs : List Code, cs.length ≤ 14 → ¬realizes cs := by
  rintro cs hlen ⟨ports,hp⟩
  have hz : (0 : Word) ∈ initWords := List.mem_cons_self
  have hr := reaches_complete matchingTargets cs initWords initWords hz (fun _ h => h) (by
    intro v h
    obtain ⟨i,hi⟩ := List.mem_ofFn.mp h
    rw [← hi,← hp]
    by_cases hv : (ports i).val < (wordRun cs initWords).length
    · left
      rw [List.getD_eq_getElem _ _ hv]
      exact List.getElem_mem _
    · right
      rw [List.getD_eq_default _ _ (by omega)]
      exact hz)
  obtain ⟨d,hd⟩ := Nat.exists_eq_add_of_le hlen
  have up (j : ℕ) : reaches matchingTargets (cs.length + j) initWords = true := by
    induction j with
    | zero => exact hr
    | succ j ih => exact reaches_more matchingTargets _ _ ih
  have clash := up d
  rw [←hd,no] at clash
  exact Bool.noConfusion clash

private def missing (H : List Word) := wanted.toFinset \ H.toFinset

private theorem missing_step (H : List Word) (v : Word) :
    (missing wanted H).card ≤ (missing wanted (v :: H)).card + 1 := by
  have h : missing wanted H ⊆ insert v (missing wanted (v :: H)) := by
    intro w hw
    by_cases e : w = v
    · simp [e]
    · apply Finset.mem_insert_of_mem
      simp only [missing,Finset.mem_sdiff,List.mem_toFinset] at hw ⊢
      exact ⟨hw.1, by simpa [e] using hw.2⟩
  exact (Finset.card_le_card h).trans (Finset.card_insert_le ..)

private theorem missing_nil_of_done (H : List Word) (h : wanted.all H.contains = true) :
    (missing wanted H).card = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.sdiff_eq_empty_iff_subset.mpr
  intro v hv
  exact List.mem_toFinset.mpr (List.contains_iff_mem.mp (List.all_eq_true.mp h v (List.mem_toFinset.mp hv)))

private theorem missing_bound (n : ℕ) (H : List Word) (h : reaches wanted n H = true) :
    (missing wanted H).card ≤ n := by
  induction n generalizing H with
  | zero => exact Nat.le_of_eq (missing_nil_of_done wanted H h)
  | succ n ih =>
    rcases Bool.or_eq_true_iff.mp h with hd | hb
    · rw [missing_nil_of_done wanted H hd]; omega
    · obtain ⟨v,_,hv⟩ := List.any_eq_true.mp hb
      exact (missing_step wanted H v).trans (Nat.succ_le_succ (ih _ hv))

-- When all remaining gates must be outputs, skip every other move.
def boundedSearch : Nat → List Word → Bool
  | 0,H => wanted.all H.contains
  | n+1,H =>
    if (missing wanted H).card > n+1 then false else
    wanted.all H.contains || (moves H).any (fun v =>
      ((missing wanted H).card ≤ n || wanted.contains v) && boundedSearch n (v::H))

theorem bounded_complete (n : ℕ) (H : List Word) (hr : reaches wanted n H = true) :
    boundedSearch wanted n H = true := by
  induction n generalizing H with
  | zero => exact hr
  | succ n ih =>
    have bound := missing_bound wanted _ _ hr
    simp only [boundedSearch,show ¬(missing wanted H).card > n+1 by omega,ite_false]
    rcases Bool.or_eq_true_iff.mp hr with hd | hb
    · exact Bool.or_eq_true_iff.mpr (Or.inl hd)
    · apply Bool.or_eq_true_iff.mpr
      right
      obtain ⟨v,hv,hn⟩ := List.any_eq_true.mp hb
      refine List.any_eq_true.mpr ⟨v,hv,Bool.and_eq_true_iff.mpr ⟨?_,ih _ hn⟩⟩
      by_cases h : v ∈ wanted
      · exact Bool.or_eq_true_iff.mpr (Or.inr (List.contains_iff_mem.mpr h))
      · have eq : missing wanted (v::H) = missing wanted H := by
          ext t
          by_cases ht : t = v
          · simp [missing,ht,h]
          · simp [missing,ht]
        have hb' := missing_bound wanted _ _ hn
        rw [eq] at hb'
        exact Bool.or_eq_true_iff.mpr (Or.inl (decide_eq_true hb'))

end

-- A row map can repeat or permute input assignments.
def permRows (f : Fin 64 → Fin 64) (w : Word) : Word :=
  (BitVec.ofBoolListLE (List.ofFn fun i => w.getLsbD (f i).val)).cast (by simp)

private theorem perm_bit (f : Fin 64 → Fin 64) (w : Word) (i : Fin 64) :
    (permRows f w).getLsbD i.val = w.getLsbD (f i).val := by
  simp only [permRows,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE]
  rw [List.getD_eq_getElem _ _ (by simp only [List.length_ofFn]; exact i.isLt),List.getElem_ofFn]

private theorem perm_and (f : Fin 64 → Fin 64) (a b : Word) :
    permRows f (a &&& b) = permRows f a &&& permRows f b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and,perm_bit f _ (⟨i,hi⟩ : Fin 64)]

private theorem perm_or (f : Fin 64 → Fin 64) (a b : Word) :
    permRows f (a ||| b) = permRows f a ||| permRows f b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_or,perm_bit f _ (⟨i,hi⟩ : Fin 64)]

private theorem perm_not (f : Fin 64 → Fin 64) (a : Word) :
    permRows f (~~~a) = ~~~(permRows f a) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_not,perm_bit f _ (⟨i,hi⟩ : Fin 64),decide_eq_true hi,
    decide_eq_true (f ⟨i,hi⟩).isLt,Bool.true_and]

private theorem move_project (f : Fin 64 → Fin 64) (H K : List Word)
    (hh : ∀ w ∈ H, permRows f w ∈ K) (v : Word) (hv : v ∈ moves H) (hn : permRows f v ∉ K) :
    permRows f v ∈ moves K := by
  simp only [moves,List.mem_filter,List.mem_eraseDups,List.mem_flatMap] at hv ⊢
  obtain ⟨⟨a,ha,h⟩,_⟩ := hv
  refine ⟨⟨_,hh a ha,?_⟩,by simpa using hn⟩
  rcases List.mem_cons.mp h with rfl | h
  · rw [perm_not]
    exact List.mem_cons_self
  · obtain ⟨b,hb,hab⟩ := List.mem_flatMap.mp h
    apply List.mem_cons_of_mem
    apply List.mem_flatMap.mpr
    refine ⟨_,hh b hb,?_⟩
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hab
    rcases hab with rfl | rfl
    · simp [perm_and]
    · simp [perm_or]

private theorem mapped_done (f : Fin 64 → Fin 64) (T H K : List Word)
    (hH : ∀ w ∈ H, permRows f w ∈ K)
    (doneH : T.all H.contains = true) : (T.map (permRows f)).all K.contains = true := by
    apply List.all_eq_true.mpr
    intro t ht
    obtain ⟨u,hu,rfl⟩ := List.mem_map.mp ht
    exact List.contains_iff_mem.mpr (hH _ (List.contains_iff_mem.mp (List.all_eq_true.mp doneH _ hu)))

theorem reaches_projection (f : Fin 64 → Fin 64) (n : ℕ) (H K : List Word)
    (T : List Word) (hH : ∀ w ∈ H, permRows f w ∈ K)
    (hr : reaches T n H = true) : reaches (T.map (permRows f)) n K = true := by
  induction n generalizing H K with
  | zero => exact mapped_done f T H K hH hr
  | succ n ih =>
    rcases Bool.or_eq_true_iff.mp hr with hd | hb
    · exact Bool.or_eq_true_iff.mpr (Or.inl (mapped_done f T H K hH hd))
    · obtain ⟨v,hv,hs⟩ := List.any_eq_true.mp hb
      by_cases hold : permRows f v ∈ K
      · apply reaches_more
        apply ih (v::H) K _ hs
        intro w hw
        rcases List.mem_cons.mp hw with rfl | hw
        · exact hold
        · exact hH _ hw
      · apply Bool.or_eq_true_iff.mpr
        right
        refine List.any_eq_true.mpr ⟨_,move_project f H K hH v hv hold,?_⟩
        apply ih (v::H) (permRows f v::K) _ hs
        intro w hw
        rcases List.mem_cons.mp hw with rfl | hw
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (hH _ hw)

theorem projected_exclusion (f : Fin 64 → Fin 64) (n : ℕ) (K T : List Word)
    (raw : initWords.all (fun v => K.contains (permRows f v)) = true)
    (targets : matchingTargets.map (permRows f) = T) (check : boundedSearch T n K = false) :
    reaches matchingTargets n initWords = false := by
  cases h : reaches matchingTargets n initWords with
  | false => rfl
  | true =>
    have p := reaches_projection f n initWords K matchingTargets
      (fun w hw => List.contains_iff_mem.mp (List.all_eq_true.mp raw w hw)) h
    rw [targets] at p
    exact Bool.noConfusion (check.symm.trans (bounded_complete _ _ _ p))

private theorem projection_id (a : Word) : permRows id a = a := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact perm_bit id a ⟨j,hj⟩

private theorem bank_mono (T : List Word) (n : ℕ) (H K : List Word) (h : ∀ v ∈ H, v ∈ K)
    (r : reaches T n H = true) : reaches T n K = true := by
  have p := reaches_projection id n H K T (fun v hv => by rw [projection_id]; exact h v hv) r
  simpa only [List.map_congr_left (g := id) (fun v _ => projection_id v), List.map_id_fun,id_eq] using p

private theorem next_word (T H : List Word) (v : Word) (n : ℕ)
    (hv : v ∈ moves H ∨ v ∈ H) (hr : reaches T n (v::H) = true) : reaches T (n+1) H = true := by
  rcases hv with new | old
  · exact Bool.or_eq_true_iff.mpr (Or.inr (List.any_eq_true.mpr ⟨v,new,hr⟩))
  · apply reaches_more
    apply bank_mono T n (v::H) H _ hr
    intro w hw
    exact (List.mem_cons.mp hw).elim (fun e => e ▸ old) id

private theorem simple_member (H : List Word) (a b : Word) (ha : a ∈ H) (hb : b ∈ H) (t : Word)
    (r : t = ~~~a ∨ t = a &&& b ∨ t = a ||| b) : t ∈ moves H ∨ t ∈ H := by
  by_cases h : t ∈ H
  · exact Or.inr h
  left
  simp only [moves,List.mem_filter,List.mem_eraseDups]
  refine ⟨List.mem_flatMap.mpr ⟨a,ha,?_⟩,by simpa using h⟩
  rcases r with rfl | rfl | rfl
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨b,hb,by simp⟩)
  · exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨b,hb,by simp⟩)

private theorem constant_move (f : Fin 64 → Fin 64) (H K : List Word) (x g : Word)
    (hH : ∀ w ∈ H, permRows f w ∈ K) (z : (0 : Word) ∈ K) (o : (~~~(0 : Word)) ∈ K)
    (c : permRows f x = 0 ∨ permRows f x = ~~~0) (hg : g ∈ moves (x::H)) :
    g ∈ moves H ∨ g ∈ H ∨ permRows f g ∈ K := by
  change permRows f x = 0#64 ∨ permRows f x = BitVec.allOnes 64 at c
  simp only [moves,List.mem_filter,List.mem_eraseDups] at hg
  obtain ⟨a,ha,how⟩ := List.mem_flatMap.mp hg.1
  rcases List.mem_cons.mp how with rfl | op
  · rcases List.mem_cons.mp ha with rfl | ha
    · right; right; rw [perm_not]
      rcases c with hc | hc <;> rw [hc] <;> simp_all
    · exact (simple_member H a a ha ha _ (Or.inl rfl)).imp_right Or.inl
  · obtain ⟨b,hb,hg'⟩ := List.mem_flatMap.mp op
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hg'
    rcases List.mem_cons.mp ha with rfl | ha <;> rcases List.mem_cons.mp hb with rfl | hb
    · right; right
      rcases hg' with rfl | rfl <;> simp <;> rcases c with hc | hc <;> simpa [hc] using (by assumption : _)
    · right; right
      have known := hH _ hb
      rcases hg' with rfl | rfl <;> rcases c with hc | hc <;>
        simp only [perm_and,perm_or,hc,BitVec.zero_and,BitVec.zero_or,
          BitVec.allOnes_and,BitVec.allOnes_or] <;> assumption
    · right; right
      have known : permRows f a ∈ K := hH _ (by assumption)
      rcases hg' with rfl | rfl <;> rcases c with hc | hc <;>
        simp only [perm_and,perm_or,hc,BitVec.and_zero,BitVec.or_zero,
          BitVec.and_allOnes,BitVec.or_allOnes] <;> assumption
    · exact (simple_member H a b (by assumption) (by assumption) _ (Or.inr hg')).imp_right Or.inl

private theorem done_any (T H : List Word) (h : T.all H.contains = true) (n : ℕ) :
    reaches T n H = true := by
  cases n with
  | zero => exact h
  | succ n => exact Bool.or_eq_true_iff.mpr (Or.inl h)

-- Removing a constant first gate also removes one consumer, unless the first gate was dispensable.
theorem unused_or_saved (f : Fin 64 → Fin 64) (T : List Word) (x : Word) (nx : x ∉ T)
    (c : permRows f x = 0 ∨ permRows f x = ~~~0) (n : ℕ) (H K : List Word)
    (hH : ∀ w ∈ H, permRows f w ∈ K) (z : (0 : Word) ∈ K) (o : (~~~(0 : Word)) ∈ K)
    (r : reaches T n (x::H) = true) :
    reaches T n H = true ∨ ∃ m, n = m+1 ∧ reaches (T.map (permRows f)) m K = true := by
  have remove_hit (L : List Word) (h : T.all (x::L).contains = true) : T.all L.contains = true := by
    apply List.all_eq_true.mpr
    intro w hw
    have e := List.contains_iff_mem.mp (List.all_eq_true.mp h _ hw)
    exact List.contains_iff_mem.mpr ((List.mem_cons.mp e).resolve_left fun q => nx (q ▸ hw))
  induction n generalizing H K with
  | zero => exact Or.inl (remove_hit H r)
  | succ n ih =>
    rcases Bool.or_eq_true_iff.mp r with hit | step
    · exact Or.inl (done_any T H (remove_hit H hit) _)
    obtain ⟨g,hg,hs⟩ := List.any_eq_true.mp step
    have knownX : permRows f x ∈ K := c.elim (fun e => e.symm ▸ z) (fun e => e.symm ▸ o)
    rcases constant_move f H K x g hH z o c hg with independent | cheap
    · have pg : permRows f g ∈ moves K ∨ permRows f g ∈ K := by
        by_cases h : permRows f g ∈ K
        · exact Or.inr h
        · exact Or.inl (move_project f H K hH g independent h)
      have s' := bank_mono T n (g::x::H) (x::g::H)
        (by intro w hw; simpa only [List.mem_cons,or_left_comm] using hw) hs
      have lifted (w : Word) (hw : w ∈ g::H) : permRows f w ∈ permRows f g::K := by
        rcases List.mem_cons.mp hw with rfl | hw
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (hH _ hw)
      rcases ih (g::H) (permRows f g::K) lifted (List.mem_cons_of_mem _ z) (List.mem_cons_of_mem _ o) s'
        with plain | ⟨m,hm,sm⟩
      · exact Or.inl (next_word T H g n (Or.inl independent) plain)
      · right
        refine ⟨n,rfl,?_⟩
        rw [hm]
        exact next_word _ K _ m pg sm
    · have pg : permRows f g ∈ K := cheap.elim (hH _) id
      refine Or.inr ⟨n,rfl,reaches_projection f n (g::x::H) K T ?_ hs⟩
      intro w hw
      rcases List.mem_cons.mp hw with rfl | hw
      · exact pg
      rcases List.mem_cons.mp hw with rfl | hw
      · exact knownX
      · exact hH _ hw

def selectRows (keep : Word) (anchor : Fin 64) (r : Fin 64) : Fin 64 :=
  if keep.getLsbD r.val then r else anchor

def maskWord (keep : Word) (anchor : Fin 64) (w : Word) : Word :=
  (w &&& keep) ||| (if w.getLsbD anchor.val then ~~~keep else 0)

theorem maskWord_eq (keep : Word) (anchor : Fin 64) (w : Word) :
    permRows (selectRows keep anchor) w = maskWord keep anchor w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [perm_bit _ _ (⟨i,hi⟩ : Fin 64)]
  cases e : keep.getLsbD i <;> cases a : w.getLsbD anchor.val <;>
    simp only [selectRows,maskWord,Fin.val_mk,e,a,Bool.false_eq_true,
      ite_true,ite_false,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,decide_eq_true hi,
      Bool.and_false,Bool.and_true,Bool.not_true,Bool.not_false,Bool.or_true,Bool.or_false,
      Bool.false_or] <;> simp

-- Every first move can use its own row map.  A constant result saves a second gate
-- whenever the original unextended bank could not already finish one gate sooner.
theorem exclude_first (T H : List Word) (n : ℕ)
    (shorter : reaches T (n+1) H = false)
    (cover : ∀ x ∈ moves H, ∃ (f : Fin 64 → Fin 64) (K : List Word),
      (∀ w ∈ H, permRows f w ∈ K) ∧ (
        (permRows f x ∈ K ∧ reaches (T.map (permRows f)) (n+1) K = false) ∨
        (x ∉ T ∧ (permRows f x = 0 ∨ permRows f x = ~~~0) ∧
          (0 : Word) ∈ K ∧ (~~~(0 : Word)) ∈ K ∧ reaches (T.map (permRows f)) n K = false))) :
    reaches T (n+2) H = false := by
  cases h : reaches T (n+2) H with
  | false => rfl
  | true =>
    rcases Bool.or_eq_true_iff.mp h with hd | step
    · exact Bool.noConfusion (shorter.symm.trans (done_any T H hd _))
    obtain ⟨x,hx,ht⟩ := List.any_eq_true.mp step
    obtain ⟨f,K,hK,case1 | case2⟩ := cover x hx
    · obtain ⟨hx',bad⟩ := case1
      have p := reaches_projection f (n+1) (x::H) K T (by
        intro v hv
        rcases List.mem_cons.mp hv with rfl | hv
        · exact hx'
        · exact hK _ hv) ht
      exact Bool.noConfusion (bad.symm.trans p)
    · obtain ⟨nx,c,z,o,bad⟩ := case2
      rcases unused_or_saved f T x nx c (n+1) H K hK z o ht with plain | ⟨m,hm,ok⟩
      · exact Bool.noConfusion (shorter.symm.trans plain)
      · have eq : n = m := Nat.succ.inj hm
        subst m
        exact Bool.noConfusion (bad.symm.trans ok)

-- An input set determines a word if agreeing on that set forces the output bits to agree.
def determines (L : Finset Word) (t : Word) : Prop :=
  ∀ i j : Fin 64, (∀ w ∈ L, w.getLsbD i.val = w.getLsbD j.val) →
    t.getLsbD i.val = t.getLsbD j.val

private theorem move_inputs (H : List Word) (g : Word) (h : g ∈ moves H) :
    ∃ a ∈ H, ∃ b ∈ H, g = ~~~a ∨ g = a &&& b ∨ g = a ||| b := by
  simp only [moves,List.mem_filter,List.mem_eraseDups] at h
  obtain ⟨a,ha,op⟩ := List.mem_flatMap.mp h.1
  rcases List.mem_cons.mp op with rfl | op
  · exact ⟨a,ha,a,ha,Or.inl rfl⟩
  · obtain ⟨b,hb,hg⟩ := List.mem_flatMap.mp op
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hg
    exact ⟨a,ha,b,hb,Or.inr hg⟩

private theorem depends_two {a b g : Word} (op : g = ~~~a ∨ g = a &&& b ∨ g = a ||| b)
    (i j : Fin 64) (ha : a.getLsbD i.val = a.getLsbD j.val)
    (hb : b.getLsbD i.val = b.getLsbD j.val) : g.getLsbD i.val = g.getLsbD j.val := by
  rcases op with rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_not,BitVec.getLsbD_and,BitVec.getLsbD_or,
      decide_eq_true i.isLt,decide_eq_true j.isLt,ha,hb]

theorem small_determining_set (t : Word) (n : ℕ) (H : List Word) (r : reaches [t] n H = true) :
    ∃ L : Finset Word, L ⊆ H.toFinset ∧ L.card ≤ n+1 ∧ determines L t := by
  have base (A : List Word) (h : [t].all A.contains = true) (k : ℕ) :
      ∃ L : Finset Word, L ⊆ A.toFinset ∧ L.card ≤ k+1 ∧ determines L t := by
    have ht : t ∈ A := by simpa using h
    exact ⟨{t},by simpa using ht,by simp,fun i j p => p t (by simp)⟩
  induction n generalizing H with
  | zero => exact base H r 0
  | succ n ih =>
    rcases Bool.or_eq_true_iff.mp r with doneH | step
    · exact base H doneH _
    obtain ⟨g,hg,hs⟩ := List.any_eq_true.mp step
    obtain ⟨L,hL,cl,dL⟩ := ih _ hs
    by_cases used : g ∈ L
    · obtain ⟨a,ha,b,hb,op⟩ := move_inputs H g hg
      let D := insert a (insert b (L.erase g))
      have rest : L.erase g ⊆ H.toFinset := by
        intro w hw
        exact List.mem_toFinset.mpr ((List.mem_cons.mp (List.mem_toFinset.mp (hL (Finset.mem_erase.mp hw).2))).resolve_left (Finset.mem_erase.mp hw).1)
      refine ⟨D,?_,?_,?_⟩
      · exact Finset.insert_subset (List.mem_toFinset.mpr ha) (Finset.insert_subset (List.mem_toFinset.mpr hb) rest)
      · have h₁ := Finset.card_insert_le a (insert b (L.erase g))
        have h₂ := Finset.card_insert_le b (L.erase g)
        have h₃ := Finset.card_erase_add_one used
        dsimp [D]; omega
      · intro i j p
        apply dL i j
        intro w hw
        by_cases e : w = g
        · subst w
          apply depends_two op i j
          · exact p a (by simp [D])
          · exact p b (by simp [D])
        · exact p w (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨e,hw⟩)))
    · refine ⟨L,?_,by omega,dL⟩
      intro w hw
      exact List.mem_toFinset.mpr ((List.mem_cons.mp (List.mem_toFinset.mp (hL hw))).resolve_left (fun e => used (e ▸ hw)))

end PEqualNP.Outside.L_meta_652
namespace PEqualNP.Outside.L_meta_652

-- Restricted six-input cube **0011
set_option maxHeartbeats 1000000 in
theorem small_cube_2 : boundedSearch [14757395258967641292, 17216961135462248174, 12297829382473034410] 0 [0, 18446744073709551615, 12297829382473034410, 14757395258967641292] = false := by
  decide +kernel

-- Restricted six-input cube **0111
set_option maxHeartbeats 1000000 in
theorem small_cube_3 : boundedSearch [17216961135462248174, 17216961135462248174, 17216961135462248174] 0 [0, 18446744073709551615, 12297829382473034410, 14757395258967641292] = false := by
  decide +kernel

-- Restricted six-input cube **1011
set_option maxHeartbeats 1000000 in
theorem small_cube_6 : boundedSearch [18446744073709551615, 17216961135462248174, 18446744073709551615] 0 [0, 18446744073709551615, 12297829382473034410, 14757395258967641292] = false := by
  decide +kernel

-- Restricted six-input cube *00*00
set_option maxHeartbeats 1000000 in
theorem small_cube_8 : boundedSearch [9838263505978427528, 0, 0] 0 [0, 18446744073709551615, 12297829382473034410, 14757395258967641292] = false := by
  decide +kernel

-- Restricted six-input cube *00*01
set_option maxHeartbeats 1000000 in
theorem small_cube_9 : boundedSearch [9838263505978427528, 0, 12297829382473034410] 0 [0, 18446744073709551615, 12297829382473034410, 14757395258967641292] = false := by
  decide +kernel

-- Restricted six-input cube *00*11
set_option maxHeartbeats 1000000 in
theorem small_cube_10 : boundedSearch [9838263505978427528, 12297829382473034410, 12297829382473034410] 0 [0, 18446744073709551615, 12297829382473034410, 14757395258967641292] = false := by
  decide +kernel

-- Restricted six-input cube *01*10
set_option maxHeartbeats 1000000 in
theorem small_cube_12 : boundedSearch [9838263505978427528, 17216961135462248174, 18446744073709551615] 1 [0, 18446744073709551615, 12297829382473034410, 14757395258967641292] = false := by
  decide +kernel

-- Restricted six-input cube *01*11
set_option maxHeartbeats 1000000 in
theorem small_cube_13 : boundedSearch [18446744073709551615, 17216961135462248174, 18446744073709551615] 0 [0, 18446744073709551615, 12297829382473034410, 14757395258967641292] = false := by
  decide +kernel

-- Restricted six-input cube ***011
set_option maxHeartbeats 1000000 in
theorem small_cube_17 : boundedSearch [18229723555195321596, 17216961135462248174, 18085043209519168250] 2 [0, 18446744073709551615, 12297829382473034410, 14757395258967641292, 17361641481138401520] = false := by
  decide +kernel

-- Restricted six-input cube ***111
set_option maxHeartbeats 1000000 in
theorem small_cube_18 : boundedSearch [18374403900871474942, 18374403900871474942, 18374403900871474942] 1 [0, 18446744073709551615, 12297829382473034410, 14757395258967641292, 17361641481138401520] = false := by
  decide +kernel

-- Restricted six-input cube **0*00
set_option maxHeartbeats 1000000 in
theorem small_cube_19 : boundedSearch [11574427654092267680, 0, 13889313184910721216] 1 [0, 18446744073709551615, 12297829382473034410, 14757395258967641292, 17361641481138401520] = false := by
  decide +kernel

-- Restricted six-input cube **0*01
set_option maxHeartbeats 1000000 in
theorem small_cube_20 : boundedSearch [11574427654092267680, 14757395258967641292, 16927600444109941482] 2 [0, 18446744073709551615, 12297829382473034410, 14757395258967641292, 17361641481138401520] = false := by
  decide +kernel

-- Restricted six-input cube **0*11
set_option maxHeartbeats 1000000 in
theorem small_cube_21 : boundedSearch [17072280789786094828, 17216961135462248174, 16927600444109941482] 3 [0, 18446744073709551615, 12297829382473034410, 14757395258967641292, 17361641481138401520] = false := by
  decide +kernel

-- Restricted six-input cube **1*00
set_option maxHeartbeats 1000000 in
theorem small_cube_22 : boundedSearch [11574427654092267680, 17361641481138401520, 13889313184910721216] 1 [0, 18446744073709551615, 12297829382473034410, 14757395258967641292, 17361641481138401520] = false := by
  decide +kernel

-- Restricted six-input cube **1*01
set_option maxHeartbeats 1000000 in
theorem small_cube_23 : boundedSearch [18446744073709551615, 18229723555195321596, 16927600444109941482] 2 [0, 18446744073709551615, 12297829382473034410, 14757395258967641292, 17361641481138401520] = false := by
  decide +kernel

-- Restricted six-input cube **1*11
set_option maxHeartbeats 1000000 in
theorem small_cube_24 : boundedSearch [18446744073709551615, 18374403900871474942, 18446744073709551615] 1 [0, 18446744073709551615, 12297829382473034410, 14757395258967641292, 17361641481138401520] = false := by
  decide +kernel

-- Restricted six-input cube ****00
set_option maxHeartbeats 1000000 in
theorem small_cube_25 : boundedSearch [12249977906276641280, 17294086455919964160, 14699973487531969536] 2 [0, 18446744073709551615, 12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920] = false := by
  decide +kernel

-- Restricted six-input cube ****01
set_option maxHeartbeats 1200000 in
theorem small_cube_26 : boundedSearch [18082228416801733360, 18216212550151634124, 17197820544983690922] 5 [0, 18446744073709551615, 12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920] = false := by
  decide +kernel

-- Restricted six-input cube **0**0
set_option maxHeartbeats 1200000 in
theorem small_cube_28 : boundedSearch [17050888365133589664, 12249977906276641280, 13889313184910721216] 4 [0, 18446744073709551615, 12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920] = false := by
  decide +kernel

end PEqualNP.Outside.L_meta_652

namespace PEqualNP.Outside.L_meta_652

private theorem bank_larger (T : List Word) (n : ℕ) (H K : List Word) (h : ∀ v ∈ H, v ∈ K)
    (r : reaches T n H = true) : reaches T n K = true := by
  have idw (w : Word) : permRows id w = w := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    simp only [permRows,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE]
    rw [List.getD_eq_getElem _ _ (by simp only [List.length_ofFn]; exact hj),List.getElem_ofFn]
    rfl
  have p := reaches_projection id n H K T (fun v hv => by rw [idw]; exact h v hv) r
  simpa only [List.map_congr_left (g := id) (fun v _ => idw v), List.map_id_fun,id_eq] using p

private theorem more_local (wanted : List Word) (n : Nat) (H : List Word) (h : reaches wanted n H = true) :
    reaches wanted (n+1) H = true := by
  induction n generalizing H with
  | zero =>
    exact Bool.or_eq_true_iff.mpr (Or.inl h)
  | succ n ih =>
    rcases Bool.or_eq_true_iff.mp h with doneH | branch
    · exact Bool.or_eq_true_iff.mpr (Or.inl doneH)
    · apply Bool.or_eq_true_iff.mpr
      right
      obtain ⟨v,hv,hr⟩ := List.any_eq_true.mp branch
      exact List.any_eq_true.mpr ⟨v,hv,ih _ hr⟩

private theorem can_step_more (T H : List Word) (v : Word) (n : ℕ)
    (hv : v ∈ moves H ∨ v ∈ H) (hr : reaches T n (v::H) = true) : reaches T (n+1) H = true := by
  rcases hv with new | old
  · exact Bool.or_eq_true_iff.mpr (Or.inr (List.any_eq_true.mpr ⟨v,new,hr⟩))
  · apply more_local T n H
    apply bank_larger T n (v::H) H _ hr
    intro w hw
    exact (List.mem_cons.mp hw).elim (fun e => e ▸ old) id

private theorem old_move (H : List Word) (w v : Word) (hg : v ∈ moves H) :
    v ∈ moves (w::H) ∨ v ∈ w::H := by
  by_cases h : v ∈ w::H
  · exact Or.inr h
  left
  simp only [moves,List.mem_filter,List.mem_eraseDups] at hg ⊢
  refine ⟨?_,by simpa using h⟩
  obtain ⟨a,ha,op⟩ := List.mem_flatMap.mp hg.1
  apply List.mem_flatMap.mpr
  refine ⟨_,List.mem_cons_of_mem w ha,?_⟩
  rcases List.mem_cons.mp op with rfl | op
  · exact List.mem_cons_self
  · obtain ⟨b,hb,r⟩ := List.mem_flatMap.mp op
    exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨_,List.mem_cons_of_mem w hb,r⟩)

-- If an output is already one gate away, an optimal circuit can buy it first.
theorem prepaid_output (T : List Word) (v : Word) (vt : v ∈ T) (n : ℕ) (H : List Word)
    (absent : v ∉ H) (r : reaches T (n+1) H = true) : reaches T n (v::H) = true := by
  induction n generalizing H with
  | zero =>
    rcases Bool.or_eq_true_iff.mp r with finished | branch
    · exact False.elim (absent (List.contains_iff_mem.mp (List.all_eq_true.mp finished v vt)))
    obtain ⟨g,hg,h⟩ := List.any_eq_true.mp branch
    have mem := List.contains_iff_mem.mp (List.all_eq_true.mp h v vt)
    have e := (List.mem_cons.mp mem).resolve_right absent
    exact e ▸ h
  | succ n ih =>
    rcases Bool.or_eq_true_iff.mp r with finished | branch
    · exact False.elim (absent (List.contains_iff_mem.mp (List.all_eq_true.mp finished v vt)))
    obtain ⟨g,hg,h⟩ := List.any_eq_true.mp branch
    by_cases e : v = g
    · exact e ▸ h
    have no : v ∉ g::H := by simpa [e] using absent
    have h' := ih (g::H) no h
    apply can_step_more T (v::H) g n (old_move H v g hg)
    apply bank_larger _ _ (v::g::H) _ _ h'
    intro w hw
    simpa only [List.mem_cons,or_left_comm] using hw

private def producible (H : List Word) (t : Word) : Bool :=
  H.any fun a => (~~~a == t) || H.any fun b => ((a &&& b) == t || (a ||| b) == t)

private theorem produced_of_move {H : List Word} {t : Word} (m : t ∈ moves H) : producible H t = true := by
  obtain ⟨hg,_⟩ := List.mem_filter.mp m
  obtain ⟨a,ha,h⟩ := List.mem_flatMap.mp (List.mem_eraseDups.mp hg)
  apply List.any_eq_true.mpr
  refine ⟨a,ha,?_⟩
  rcases List.mem_cons.mp h with rfl | h
  · simp
  · obtain ⟨b,hb,op⟩ := List.mem_flatMap.mp h
    apply Bool.or_eq_true_iff.mpr
    right
    apply List.any_eq_true.mpr
    refine ⟨b,hb,?_⟩
    simp only [List.mem_cons,List.not_mem_nil,or_false] at op
    rcases op with rfl | rfl <;> simp

private def unseen (T H : List Word) : Finset Word := T.toFinset \ H.toFinset

def compactSearch (T : List Word) : ℕ → List Word → Bool
  | 0,H => T.all H.contains
  | n+1,H =>
    let missing := unseen T H
    if missing.card > n+1 then false else
    if T.all H.contains then true else
    match T.find? (fun t => !(H.contains t) && producible H t) with
    | some v => compactSearch T n (v::H)
    | none =>
      if missing.card > n then false else
      (moves H).any (fun v => compactSearch T n (v::H))

private theorem output_count (T H : List Word) (n : Nat) (r : reaches T n H = true) :
    (unseen T H).card ≤ n := by
  induction n generalizing H with
  | zero =>
    have h : T.toFinset ⊆ H.toFinset := by
      intro t ht
      exact List.mem_toFinset.mpr (List.contains_iff_mem.mp (List.all_eq_true.mp r t (List.mem_toFinset.mp ht)))
    simp [unseen,Finset.sdiff_eq_empty_iff_subset.mpr h]
  | succ n ih =>
    rcases Bool.or_eq_true_iff.mp r with hd | hb
    · have h : T.toFinset ⊆ H.toFinset := by
        intro t ht
        exact List.mem_toFinset.mpr (List.contains_iff_mem.mp (List.all_eq_true.mp hd t (List.mem_toFinset.mp ht)))
      simp [unseen,Finset.sdiff_eq_empty_iff_subset.mpr h]
    obtain ⟨v,hv,hs⟩ := List.any_eq_true.mp hb
    have sub : unseen T H ⊆ insert v (unseen T (v::H)) := by
      intro w hw
      by_cases e : w = v
      · simp [e]
      · apply Finset.mem_insert_of_mem
        simp only [unseen,Finset.mem_sdiff,List.mem_toFinset] at hw ⊢
        exact ⟨hw.1,by simpa [e] using hw.2⟩
    exact (Finset.card_le_card sub).trans ((Finset.card_insert_le ..).trans (Nat.succ_le_succ (ih _ hs)))

theorem compact_complete (T : List Word) (n : ℕ) (H : List Word) (r : reaches T n H = true) :
    compactSearch T n H = true := by
  induction n generalizing H with
  | zero => exact r
  | succ n ih =>
    have count := output_count T H _ r
    simp only [compactSearch,show ¬(unseen T H).card > n+1 by omega,ite_false]
    by_cases hd : T.all H.contains = true
    · simp [hd]
    simp only [hd,Bool.false_eq_true,ite_false]
    split
    next v eq =>
      have props := List.find?_some eq
      have abs : v ∉ H := by simpa using (Bool.and_eq_true_iff.mp props).1
      exact ih _ (prepaid_output T v (List.mem_of_find?_eq_some eq) n H abs r)
    next eq =>
      obtain ⟨v,hv,hs⟩ := List.any_eq_true.mp ((Bool.or_eq_true_iff.mp r).resolve_left hd)
      have vt : v ∉ T := by
        intro h
        have ab : v ∉ H := by
          have p := (List.mem_filter.mp hv).2
          simpa using p
        have f := List.find?_eq_none.mp eq v h
        simp [ab,produced_of_move hv] at f
      have same : unseen T (v::H) = unseen T H := by
        ext w
        by_cases e : w = v
        · simp [unseen,e,vt]
        · simp [unseen,e]
      have co := output_count T (v::H) n hs
      rw [same] at co
      simp only [show ¬(unseen T H).card > n by omega,ite_false]
      exact List.any_eq_true.mpr ⟨v,hv,ih _ hs⟩

set_option maxHeartbeats 1200000 in
theorem small_cube_30 : compactSearch [18446744073709551615, 18373840942327987964, 18440833009002938346] 5 [0, 18446744073709551615, 12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920] = false := by
  decide +kernel

set_option maxHeartbeats 1200000 in
theorem small_cube_27 : compactSearch [18373840942327987964, 18369900232523579118, 18373277983784500986] 6 [0, 18446744073709551615, 12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920] = false := by
  decide +kernel

set_option maxHeartbeats 1200000 in
theorem small_cube_29 : compactSearch [17050888365133589664, 17207390840222969548, 16927600444109941482] 6 [0, 18446744073709551615, 12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920] = false := by
  decide +kernel


end PEqualNP.Outside.L_meta_652

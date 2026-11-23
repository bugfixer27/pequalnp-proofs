import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_652

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

private def circuit : Circuit :=
  ⟨[
    ⟨.and, [0, 3]⟩, ⟨.and, [1, 4]⟩, ⟨.and, [2, 5]⟩,
    ⟨.or, [6, 7]⟩, ⟨.or, [9, 8]⟩,
    ⟨.and, [0, 4]⟩, ⟨.and, [1, 5]⟩, ⟨.and, [2, 3]⟩,
    ⟨.or, [11, 12]⟩, ⟨.or, [14, 13]⟩,
    ⟨.and, [0, 5]⟩, ⟨.and, [1, 3]⟩, ⟨.and, [2, 4]⟩,
    ⟨.or, [16, 17]⟩, ⟨.or, [19, 18]⟩
  ], 20⟩

set_option maxHeartbeats 2000000 in
theorem upper_bound :
    ∃ C : Circuit, FanInTwo C ∧ C.size ≤ 15 ∧ ∃ o0 o1 o2 : ℕ, ∀ x : Fin 6 → Bool,
      (C.wires (List.ofFn x)).getD o0 false = ((x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5)) ∧
      (C.wires (List.ofFn x)).getD o1 false = ((x 0 && x 4) || (x 1 && x 5) || (x 2 && x 3)) ∧
      (C.wires (List.ofFn x)).getD o2 false = ((x 0 && x 5) || (x 1 && x 3) || (x 2 && x 4)) := by
  refine ⟨circuit, ?_, by decide, 10, 15, 20, ?_⟩
  · intro g hg
    simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl <;> simp
  · intro x
    simp [circuit, Circuit.wires, GateOp.eval, List.ofFn_succ]

end PEqualNP.Outside.L_meta_652

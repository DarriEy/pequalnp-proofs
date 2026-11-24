import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4620

open PEqualNP.CircuitLowerBounds

def R (a b : ℕ) : ℕ → ℕ → Prop := fun x5 x6 => x6 = x5 + 1 ∨ x6 = 0 ∧ (x5 = a ∨ x5 = b)

theorem inp (a0 b0 a1 b1 : ℕ) : ∀ (is js0 js1 : List ℕ),
    List.Forall₂ (R a0 b0) is js0 → List.Forall₂ (R a1 b1) is js1 →
    ∃ es : List (ℕ × Bool × Bool), es.map (fun e => e.1) = is.map (min 18) ∧
      es.map (fun e => bif e.2.1 then 0 else e.1 + 1) = js0.map (min 19) ∧
      es.map (fun e => bif e.2.2 then 0 else e.1 + 1) = js1.map (min 19) ∧
      ∀ e ∈ es, (e.2.1 = true → e.1 = min 18 a0 ∨ e.1 = min 18 b0) ∧
        (e.2.2 = true → e.1 = min 18 a1 ∨ e.1 = min 18 b1) := by
  intro is js0 js1 h0
  induction h0 generalizing js1 with
  | nil =>
    intro h1
    cases h1
    exact ⟨[], by simp⟩
  | @cons i j0 is js0 r0 _ ih =>
    intro h1
    cases h1 with
    | @cons _ j1 _ js1 r1 t1 =>
      obtain ⟨es, e1, e2, e3, e4⟩ := ih js1 t1
      refine ⟨(min 18 i, decide (j0 = 0), decide (j1 = 0)) :: es, ?_, ?_, ?_, ?_⟩
      · simp [e1]
      · simp only [List.map_cons, e2, List.cons.injEq, and_true]
        unfold R at r0
        rcases r0 with r | ⟨r, _⟩
        · subst r; simp; omega
        · subst r; simp
      · simp only [List.map_cons, e3, List.cons.injEq, and_true]
        unfold R at r1
        rcases r1 with r | ⟨r, _⟩
        · subst r; simp; omega
        · subst r; simp
      · intro e he
        rcases List.mem_cons.mp he with rfl | he
        · unfold R at r0 r1
          refine ⟨fun h => ?_, fun h => ?_⟩
          · simp at h
            rcases r0 with r | ⟨_, r | r⟩
            · omega
            · left; simp [r]
            · right; simp [r]
          · simp at h
            rcases r1 with r | ⟨_, r | r⟩
            · omega
            · left; simp [r]
            · right; simp [r]
        · exact e4 e he

def G (a b : ℕ) (g h : Gate) : Prop := g.op = h.op ∧ List.Forall₂ (R a b) g.inputs h.inputs

theorem gat (a0 b0 a1 b1 : ℕ) : ∀ (gs hs0 hs1 : List Gate),
    List.Forall₂ (G a0 b0) gs hs0 → List.Forall₂ (G a1 b1) gs hs1 →
    ∃ x8 : List (GateOp × List (ℕ × Bool × Bool)),
      x8.map (fun t => (⟨t.1, t.2.map (fun e => e.1)⟩ : Gate)) =
        gs.map (fun g => (⟨g.op, g.inputs.map (min 18)⟩ : Gate)) ∧
      x8.map (fun t => (⟨t.1, t.2.map (fun e => bif e.2.1 then 0 else e.1 + 1)⟩ : Gate)) =
        hs0.map (fun g => (⟨g.op, g.inputs.map (min 19)⟩ : Gate)) ∧
      x8.map (fun t => (⟨t.1, t.2.map (fun e => bif e.2.2 then 0 else e.1 + 1)⟩ : Gate)) =
        hs1.map (fun g => (⟨g.op, g.inputs.map (min 19)⟩ : Gate)) ∧
      ∀ t ∈ x8, ∀ e ∈ t.2, (e.2.1 = true → e.1 = min 18 a0 ∨ e.1 = min 18 b0) ∧
        (e.2.2 = true → e.1 = min 18 a1 ∨ e.1 = min 18 b1) := by
  intro gs hs0 hs1 h0
  induction h0 generalizing hs1 with
  | nil =>
    intro h1
    cases h1
    exact ⟨[], by simp⟩
  | @cons g k0 gs hs0 r0 _ ih =>
    intro h1
    cases h1 with
    | @cons _ k1 _ hs1 r1 t1 =>
      obtain ⟨x8, e1, e2, e3, e4⟩ := ih hs1 t1
      obtain ⟨es, f1, f2, f3, f4⟩ := inp a0 b0 a1 b1 g.inputs k0.inputs k1.inputs r0.2 r1.2
      refine ⟨(g.op, es) :: x8, ?_, ?_, ?_, ?_⟩
      · simp only [List.map_cons, e1, f1]
      · simp only [List.map_cons, e2, f2, r0.1]
      · simp only [List.map_cons, e3, f3, r1.1]
      · intro t ht
        rcases List.mem_cons.mp ht with rfl | ht
        · exact f4
        · exact e4 t ht

end PEqualNP.Outside.L_meta_4620

theorem PEqualNP.Outside.L_meta_4620 : have x1 : ℕ → ℕ → PEqualNP.CircuitLowerBounds.Gate → PEqualNP.CircuitLowerBounds.Gate → Prop := fun (x1 x2 : ℕ) (x3 x4 : PEqualNP.CircuitLowerBounds.Gate) => x3.op = x4.op ∧ List.Forall₂ (fun (x5 x6 : ℕ) => x6 = x5 + (1 : ℕ) ∨ x6 = (0 : ℕ) ∧ (x5 = x1 ∨ x5 = x2)) x3.inputs x4.inputs; have x2 : Option Bool → PEqualNP.CircuitLowerBounds.GateOp × List (ℕ × Bool × Bool) → PEqualNP.CircuitLowerBounds.Gate := fun (x2 : Option Bool) (x3 : PEqualNP.CircuitLowerBounds.GateOp × List (ℕ × Bool × Bool)) => { op := x3.1, inputs := List.map (fun (x4 : ℕ × Bool × Bool) => x2.elim x4.1 fun (x5 : Bool) => bif bif x5 then x4.2.2 else x4.2.1 then (0 : ℕ) else x4.1 + (1 : ℕ)) x3.2 : PEqualNP.CircuitLowerBounds.Gate }; ∀ (x3 : List PEqualNP.CircuitLowerBounds.Gate) (x4 : Bool → List PEqualNP.CircuitLowerBounds.Gate) (x5 x6 : Bool → ℕ), (∀ (x7 : Bool), List.Forall₂ (x1 (x5 x7) (x6 x7)) x3 (x4 x7)) → ∃ (x8 : List (PEqualNP.CircuitLowerBounds.GateOp × List (ℕ × Bool × Bool))), List.map (x2 Option.none) x8 = List.map (fun (x9 : PEqualNP.CircuitLowerBounds.Gate) => { op := x9.op, inputs := List.map (Min.min (18 : ℕ)) x9.inputs : PEqualNP.CircuitLowerBounds.Gate }) x3 ∧ (∀ (x9 : Bool), List.map (x2 (Option.some x9)) x8 = List.map (fun (x10 : PEqualNP.CircuitLowerBounds.Gate) => { op := x10.op, inputs := List.map (Min.min (19 : ℕ)) x10.inputs : PEqualNP.CircuitLowerBounds.Gate }) (x4 x9)) ∧ ∀ (x9 : Bool), ∀ x10 ∈ x8, ∀ x12 ∈ x10.2, (bif x9 then x12.2.2 else x12.2.1) = Bool.true → x12.1 = Min.min (18 : ℕ) (x5 x9) ∨ x12.1 = Min.min (18 : ℕ) (x6 x9) := by
  intro x1 x2 x3 x4 x5 x6 h
  obtain ⟨x8, e1, e2, e3, e4⟩ := PEqualNP.Outside.L_meta_4620.gat (x5 false) (x6 false)
    (x5 true) (x6 true) x3 (x4 false) (x4 true) (h false) (h true)
  refine ⟨x8, ?_, ?_, ?_⟩
  · exact e1
  · intro v
    cases v
    · exact e2
    · exact e3
  · intro v t ht e he hv
    cases v
    · exact (e4 t ht e he).1 hv
    · exact (e4 t ht e he).2 hv

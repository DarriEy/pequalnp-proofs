import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2764

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- One evaluation step of a circuit, exactly as in Circuit.wires.
def ev (g : Gate) (w : List Bool) : Bool := g.op.eval (g.inputs.map fun i => w.getD i false)

def step (w : List Bool) (g : Gate) : List Bool := w ++ [ev g w]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

theorem fold_len (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp [List.foldl_cons, ih, step]; omega

theorem fold_ext (gs : List Gate) (w : List Bool) :
    ∃ t, gs.foldl step w = w ++ t := by
  induction gs generalizing w with
  | nil => exact ⟨[], by simp⟩
  | cons g gs ih =>
    obtain ⟨t, ht⟩ := ih (step w g)
    exact ⟨[ev g w] ++ t, by rw [List.foldl_cons, ht]; simp [step]⟩

theorem fold_keep (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  obtain ⟨t, ht⟩ := fold_ext gs w
  rw [ht, List.getD_append _ _ _ _ hi]

-- Two gate lists that agree gate by gate along the run give the same wires.
theorem fold_congr : ∀ (gs hs : List Gate) (w : List Bool), gs.length = hs.length →
    (∀ i (hi : i < gs.length) (hi' : i < hs.length),
      ev hs[i] ((gs.take i).foldl step w) = ev gs[i] ((gs.take i).foldl step w)) →
    hs.foldl step w = gs.foldl step w := by
  intro gs
  induction gs with
  | nil =>
    intro hs w hl _
    cases hs with
    | nil => rfl
    | cons _ _ => simp at hl
  | cons g gs ih =>
    intro hs w hl h
    cases hs with
    | nil => simp at hl
    | cons k hs =>
      have h0 := h 0 (by simp) (by simp)
      simp only [List.take_zero, List.foldl_nil, List.getElem_cons_zero] at h0
      simp only [List.foldl_cons]
      have e : step w k = step w g := by simp [step, h0]
      rw [e]
      apply ih hs (step w g) (by simpa using hl)
      intro i hi hi'
      have := h (i + 1) (by simp; omega) (by simp; omega)
      simpa [List.take_succ_cons, List.foldl_cons] using this

-- Reads that fall past the current prefix are sent to wire 24, which also reads false.
def fx (j a : ℕ) : ℕ := if a < 9 + j then a else 24

def rk (a : ℕ) : ℕ := if a < 9 then a else if a = 24 then 9 else a + 1

def two (op : GateOp) (a b : ℕ) : Gate := if rk a ≤ rk b then ⟨op, [a, b]⟩ else ⟨op, [b, a]⟩

def nrm (j : ℕ) (g : Gate) : Gate :=
  match g with
  | ⟨.and, []⟩ => ⟨.and, []⟩
  | ⟨.and, [a]⟩ => ⟨.and, [fx j a, fx j a]⟩
  | ⟨.and, [a, b]⟩ => two .and (fx j a) (fx j b)
  | ⟨.or, []⟩ => ⟨.or, [24, 24]⟩
  | ⟨.or, [a]⟩ => ⟨.or, [fx j a, fx j a]⟩
  | ⟨.or, [a, b]⟩ => two .or (fx j a) (fx j b)
  | ⟨.not, []⟩ => ⟨.and, []⟩
  | ⟨.not, [a]⟩ => ⟨.not, [fx j a]⟩
  | ⟨.not, [a, _]⟩ => ⟨.not, [fx j a]⟩
  | _ => ⟨.and, []⟩

def Sh (j : ℕ) (g : Gate) : Prop :=
  g = ⟨.and, []⟩ ∨ (∃ a, (a < 9 + j ∨ a = 24) ∧ g = ⟨.not, [a]⟩) ∨
    ∃ a b, (a < 9 + j ∨ a = 24) ∧ (b < 9 + j ∨ b = 24) ∧ rk a ≤ rk b ∧
      (g = ⟨.and, [a, b]⟩ ∨ g = ⟨.or, [a, b]⟩)

theorem fit_fx (j a : ℕ) : fx j a < 9 + j ∨ fx j a = 24 := by
  unfold fx; split_ifs with h
  · exact Or.inl h
  · exact Or.inr rfl

theorem sh_two {j a b : ℕ} {op : GateOp} (ha : a < 9 + j ∨ a = 24) (hb : b < 9 + j ∨ b = 24)
    (hop : op = .and ∨ op = .or) : Sh j (two op a b) := by
  unfold two
  split_ifs with h
  · right; right
    rcases hop with rfl | rfl
    · exact ⟨a, b, ha, hb, h, Or.inl rfl⟩
    · exact ⟨a, b, ha, hb, h, Or.inr rfl⟩
  · right; right
    rcases hop with rfl | rfl
    · exact ⟨b, a, hb, ha, by omega, Or.inl rfl⟩
    · exact ⟨b, a, hb, ha, by omega, Or.inr rfl⟩

theorem nrm_sh (j : ℕ) (g : Gate) : Sh j (nrm j g) := by
  rcases g with ⟨op, ins⟩
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩ <;> cases op <;> dsimp only [nrm]
  all_goals first
    | exact Or.inl rfl
    | exact Or.inr (Or.inl ⟨_, fit_fx j a, rfl⟩)
    | exact Or.inr (Or.inr ⟨_, _, fit_fx j a, fit_fx j a, le_refl _, Or.inl rfl⟩)
    | exact Or.inr (Or.inr ⟨_, _, fit_fx j a, fit_fx j a, le_refl _, Or.inr rfl⟩)
    | exact sh_two (fit_fx j a) (fit_fx j b) (Or.inl rfl)
    | exact sh_two (fit_fx j a) (fit_fx j b) (Or.inr rfl)
    | exact Or.inr (Or.inr ⟨24, 24, Or.inr rfl, Or.inr rfl, le_refl _, Or.inr rfl⟩)

theorem getD_fx {j a : ℕ} {w : List Bool} (hw : w.length = 9 + j) (hj : j ≤ 14) :
    w.getD (fx j a) false = w.getD a false := by
  unfold fx
  split_ifs with h
  · rfl
  · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]

theorem ev_two (op : GateOp) (hop : op = .and ∨ op = .or) (a b : ℕ) (w : List Bool) :
    ev (two op a b) w = ev ⟨op, [a, b]⟩ w := by
  unfold two
  split_ifs
  · rfl
  · rcases hop with rfl | rfl <;> simp [ev, GateOp.eval, Bool.and_comm, Bool.or_comm]

theorem nrm_ev {j : ℕ} {w : List Bool} (hw : w.length = 9 + j) (hj : j ≤ 14) (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    ev (nrm j g) w = ev g w := by
  have h24 : w.getD 24 false = false := List.getD_eq_default _ _ (by omega)
  have hf := fun a => getD_fx (a := a) hw hj
  simp only [List.getD_eq_getElem?_getD] at hf h24
  rcases g with ⟨op, ins⟩
  obtain ⟨hop, hl⟩ := hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · rcases hop with rfl | rfl | rfl <;> simp [nrm, ev, GateOp.eval, h24]
  · rcases hop with rfl | rfl | rfl <;> simp [nrm, ev, GateOp.eval, hf]
  · rcases hop with rfl | rfl | rfl
    · simp only [nrm]; rw [ev_two _ (Or.inl rfl)]; simp [ev, GateOp.eval, hf]
    · simp only [nrm]; rw [ev_two _ (Or.inr rfl)]; simp [ev, GateOp.eval, hf]
    · simp [nrm, ev, GateOp.eval, hf]
  · simp at hl

theorem main (C : Circuit) (hfan : FanInTwo C) (hsize : C.size ≤ 15)
    (h9 : ∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x 0 || x 3))
    (ho1 : 9 ≤ C.output) (ho2 : C.output < 9 + C.gates.length) :
    ∃ D : Circuit, D.gates.length = 15 ∧ D.output = 23 ∧ D.gates[0]? = some ⟨.or, [0, 3]⟩ ∧
      (∀ (j : ℕ) (hj : j < D.gates.length), Sh j D.gates[j]) ∧
      circuitFun 9 D = circuitFun 9 C := by
  set G := C.gates with hGdef
  set o := C.output with hodef
  have hGl : G.length ≤ 15 := hsize
  set k := o - 9 with hk
  have hko : o = 9 + k := by omega
  have hkG : k + 1 ≤ G.length := by omega
  set L := G.take (k + 1) with hL
  have hLl : L.length = k + 1 := by simp [hL]; omega
  set T := L.mapIdx (fun j g => if j = 0 then (⟨.or, [0, 3]⟩ : Gate) else nrm j g) with hT
  have hTl : T.length = k + 1 := by simp [hT, hLl]
  have hTg : ∀ j (h : j < T.length), T[j] = if j = 0 then (⟨.or, [0, 3]⟩ : Gate)
      else nrm j (L[j]'(by simp [hT] at h; exact h)) := by
    intro j h; simp [hT]
  have hT0 : T[0]? = some ⟨.or, [0, 3]⟩ := by
    rw [List.getElem?_eq_getElem (by omega), hTg 0 (by omega)]; simp
  -- shape of T
  have hTs : ∀ j (h : j < T.length), Sh j T[j] := by
    intro j h
    rw [hTg j h]
    split_ifs with hj0
    · subst hj0
      exact Or.inr (Or.inr ⟨0, 3, by omega, by omega, by decide, Or.inr rfl⟩)
    · exact nrm_sh j _
  -- the run over T is the run over L
  have hrun : ∀ x : Fin 9 → Bool, T.foldl step (List.ofFn x) = L.foldl step (List.ofFn x) := by
    intro x
    apply fold_congr L T _ (by omega)
    intro i hi hi'
    have hlen : ((L.take i).foldl step (List.ofFn x)).length = 9 + i := by
      rw [fold_len]; simp; omega
    rw [hTg i hi']
    split_ifs with hi0
    · subst hi0
      have hG0 : 0 < G.length := by omega
      obtain ⟨g0, rest, hGc⟩ : ∃ g0 rest, G = g0 :: rest := by
        cases hG : G with
        | nil => rw [hG] at hG0; simp at hG0
        | cons g0 rest => exact ⟨g0, rest, rfl⟩
      have hL0 : L[0] = g0 := by simp [hL, hGc]
      simp only [List.take_zero, List.foldl_nil, hL0]
      have hw := h9 x
      rw [wires_eq, ← hGdef, hGc, List.foldl_cons,
        fold_keep _ _ _ (by simp [step])] at hw
      have hv : (step (List.ofFn x) g0).getD 9 false = ev g0 (List.ofFn x) := by
        simp [step]
      rw [hv] at hw
      rw [hw]
      simp [ev, GateOp.eval, List.getD_eq_getElem?_getD]
    · have hmem : L[i] ∈ G := List.mem_of_mem_take (List.getElem_mem _)
      exact nrm_ev hlen (by omega) _ (hfan _ hmem)
  -- value of C is read off the run over L
  have hval : ∀ x : Fin 9 → Bool, circuitFun 9 C x = (T.foldl step (List.ofFn x)).getD o false := by
    intro x
    rw [hrun x]
    show (C.wires (List.ofFn x)).getD o false = _
    rw [wires_eq, ← hGdef, ← List.take_append_drop (k + 1) G, List.foldl_append, ← hL]
    exact fold_keep _ _ _ (by rw [fold_len]; simp; omega)
  have hTlen : ∀ x : Fin 9 → Bool, (T.foldl step (List.ofFn x)).length = 9 + (k + 1) := by
    intro x; rw [fold_len]; simp [hTl]
  by_cases hk14 : k = 14
  · refine ⟨⟨T, 23⟩, by simp [hTl, hk14], rfl, hT0, hTs, ?_⟩
    funext x
    rw [hval x]
    show (T.foldl step (List.ofFn x)).getD 23 false = _
    rw [hko, hk14]
  · have hk13 : k ≤ 13 := by omega
    let P : List Gate := List.replicate (13 - k) ⟨.and, []⟩ ++ [⟨.and, [o, o]⟩]
    refine ⟨⟨T ++ P, 23⟩, by simp [P, hTl]; omega, rfl, ?_, ?_, ?_⟩
    · rw [List.getElem?_append_left (by omega)]; exact hT0
    · intro j hj
      show Sh j (T ++ P)[j]
      rw [List.getElem_append]
      split_ifs with hjT
      · exact hTs j hjT
      · simp only [P]
        rw [List.getElem_append]
        split_ifs with hjR
        · rw [List.getElem_replicate]; exact Or.inl rfl
        · simp only [List.getElem_singleton]
          exact Or.inr (Or.inr ⟨o, o, Or.inl (by omega), Or.inl (by omega), le_refl _, Or.inl rfl⟩)
    · funext x
      rw [hval x]
      show ((T ++ P).foldl step (List.ofFn x)).getD 23 false = _
      rw [List.foldl_append]
      simp only [P]
      rw [List.foldl_append]
      set W := T.foldl step (List.ofFn x) with hW
      set V := (List.replicate (13 - k) (⟨.and, []⟩ : Gate)).foldl step W with hV
      have hVl : V.length = 23 := by rw [hV, fold_len, hTlen]; simp; omega
      have hVo : V.getD o false = W.getD o false := by
        rw [hV]; exact fold_keep _ _ _ (by rw [hW, hTlen]; omega)
      simp only [List.foldl_cons, List.foldl_nil, step]
      rw [List.getD_append_right _ _ _ _ (by omega)]
      simp only [List.getD_eq_getElem?_getD] at hVo
      simp [hVl, ev, GateOp.eval, hVo]

end PEqualNP.Outside.L_meta_2764

theorem PEqualNP.Outside.L_meta_2764 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.FanInTwo x1 →     x1.size ≤ (15 : ℕ) →       (∀ (x4 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x4)).getD (9 : ℕ) Bool.false = (x4 (0 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)))) →         (9 : ℕ) ≤ x1.output →           x1.output < (9 : ℕ) + x1.gates.length →             ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit),               x7.gates.length = (15 : ℕ) ∧                 x7.output = (23 : ℕ) ∧                   x7.gates[(0 : ℕ)]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [(0 : ℕ), (3 : ℕ)] : PEqualNP.CircuitLowerBounds.Gate } ∧                     (∀ (x8 : ℕ) (x9 : x8 < x7.gates.length),                         have x10 : PEqualNP.CircuitLowerBounds.Gate := x7.gates[x8];                         have x11 : ℕ → Prop := fun (x11 : ℕ) => x11 < (9 : ℕ) + x8 ∨ x11 = (24 : ℕ);                         have x12 : ℕ → ℕ := fun (x12 : ℕ) => if x12 < (9 : ℕ) then x12 else if x12 = (24 : ℕ) then (9 : ℕ) else x12 + (1 : ℕ);                         x10 = { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [] : PEqualNP.CircuitLowerBounds.Gate } ∨ (∃ (x13 : ℕ), x11 x13 ∧ x10 = { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [x13] : PEqualNP.CircuitLowerBounds.Gate }) ∨ ∃ (x13 : ℕ) (x14 : ℕ), x11 x13 ∧ x11 x14 ∧ x12 x13 ≤ x12 x14 ∧ (x10 = { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x13, x14] : PEqualNP.CircuitLowerBounds.Gate } ∨ x10 = { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [x13, x14] : PEqualNP.CircuitLowerBounds.Gate })) ∧                       PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x7 = PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 := by
  intro C hfan hsize h9 ho1 ho2
  obtain ⟨D, h1, h2, h3, h4, h5⟩ := PEqualNP.Outside.L_meta_2764.main C hfan hsize h9 ho1 ho2
  exact ⟨D, h1, h2, h3, fun j hj => h4 j hj, h5⟩

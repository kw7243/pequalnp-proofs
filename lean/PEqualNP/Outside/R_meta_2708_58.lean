import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
set_option maxRecDepth 12000 in
set_option maxHeartbeats 6000000 in
theorem PEqualNP.Outside.R_meta_2708_58
    (boundary : ∀ x : Fin 14 → Bool, ¬ (∃ a b : Fin 14, (([1408,8832,12544,6272,11264,5632,2816] : List ℕ).getD a.val 0).testBit b.val = true ∧ x a = true ∧ x b = true) →
      ∃ r ∈ ([127, 244, 314, 432, 541, 660, 792, 1102, 1220, 1290, 1548, 2087, 2212, 2338, 2565, 3078, 3716, 4179, 4304, 4370, 4625, 5008, 5186, 6147, 7426, 8297, 8416, 8488, 8713, 9288, 9992, 10273, 10656, 12353, 13504, 14849, 16256] : List ℕ), ∀ i : Fin 14, x i = true → r.testBit i.val = true)
    (sensitivity : ∀ (f g : (Fin 14 → Bool) → Bool),
      (∀ x, (f x = true ∧ g x = true) ↔ ∃ a b : Fin 14, (([1408,8832,12544,6272,11264,5632,2816] : List ℕ).getD a.val 0).testBit b.val = true ∧ x a = true ∧ x b = true) →
      let full := fun f : (Fin 14 → Bool) → Bool => ∀ i : Fin 14, ∃ x : Fin 14 → Bool, f (Function.update x i false) ≠ f (Function.update x i true)
      full f ∨ full g)
    (finite : ∀ (C : Circuit) (u v : ℕ), Monotone2 C →
      let val := fun (i : ℕ) (x : Fin 14 → Bool) => (C.wires (List.ofFn x)).getD i false
      let row := fun (i r : ℕ) => val i (fun j => r.testBit j.val)
      let neg : List ℕ := [127, 244, 314, 432, 541, 660, 792, 1102, 1220, 1290, 1548, 2087, 2212, 2338, 2565, 3078, 3716, 4179, 4304, 4370, 4625, 5008, 5186, 6147, 7426, 8297, 8416, 8488, 8713, 9288, 9992, 10273, 10656, 12353, 13504, 14849, 16256]
      (∀ r ∈ ([129, 257, 1025, 130, 514, 8194, 260, 4100, 8196, 136, 2056, 4104, 1040, 2064, 8208, 544, 1056, 4128, 320, 576, 2112] : List ℕ), row u r = true ∧ row v r = true) →
      (∀ r ∈ neg, row u r = false ∨ row v r = false) →
      (∃ r ∈ neg, row u r = false ∧ row v r = true) →
      (∃ r ∈ neg, row v r = false ∧ row u r = true) →
      (∀ i : Fin 14, ∃ x : Fin 14 → Bool, val u (Function.update x i false) ≠ val u (Function.update x i true)) →
      26 ≤ C.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x1 →     x2 < (14 : ℕ) + x1.size →       x3 < (14 : ℕ) + x1.size →         have x7 : List (ℕ × ℕ) := [((0 : ℕ), (7 : ℕ)), ((0 : ℕ), (8 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (7 : ℕ)), ((1 : ℕ), (9 : ℕ)), ((1 : ℕ), (13 : ℕ)), ((2 : ℕ), (8 : ℕ)), ((2 : ℕ), (12 : ℕ)), ((2 : ℕ), (13 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((3 : ℕ), (11 : ℕ)), ((3 : ℕ), (12 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)), ((4 : ℕ), (13 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((5 : ℕ), (10 : ℕ)), ((5 : ℕ), (12 : ℕ)), ((6 : ℕ), (8 : ℕ)), ((6 : ℕ), (9 : ℕ)), ((6 : ℕ), (11 : ℕ))];         have x8 : (Fin (14 : ℕ) → Bool) → Prop := fun (x8 : Fin (14 : ℕ) → Bool) => ∃ (x9 : Fin (14 : ℕ)) (x10 : Fin (14 : ℕ)), (↑x9, ↑x10) ∈ x7 ∧ x8 x9 = Bool.true ∧ x8 x10 = Bool.true;         have x9 : ℕ → (Fin (14 : ℕ) → Bool) → Bool := fun (x9 : ℕ) (x10 : Fin (14 : ℕ) → Bool) => (x1.wires (List.ofFn x10)).getD x9 Bool.false;         (∀ (x10 : Fin (14 : ℕ) → Bool), x8 x10 → x9 x2 x10 = Bool.true ∧ x9 x3 x10 = Bool.true) → (∀ (x11 : Fin (14 : ℕ) → Bool), ¬x8 x11 → x9 x2 x11 = Bool.false ∨ x9 x3 x11 = Bool.false) → (∃ (x12 : Fin (14 : ℕ) → Bool), ¬x8 x12 ∧ x9 x2 x12 = Bool.false ∧ x9 x3 x12 = Bool.true) → (∃ (x13 : Fin (14 : ℕ) → Bool), ¬x8 x13 ∧ x9 x3 x13 = Bool.false ∧ x9 x2 x13 = Bool.true) → (26 : ℕ) ≤ x1.size := by

  intro C u v monoC hu hv E hit val both no diffU diffV
  let B := fun (x : Fin 14 → Bool) => ∃ a b : Fin 14, (([1408,8832,12544,6272,11264,5632,2816] : List ℕ).getD a.val 0).testBit b.val = true ∧ x a = true ∧ x b = true
  let full := fun f : (Fin 14 → Bool) → Bool => ∀ i : Fin 14, ∃ x : Fin 14 → Bool, f (Function.update x i false) ≠ f (Function.update x i true)
  let mask (r : ℕ) (i : Fin 14) := r.testBit i.val
  let P : List ℕ := [129, 257, 1025, 130, 514, 8194, 260, 4100, 8196, 136, 2056, 4104, 1040, 2064, 8208, 544, 1056, 4128, 320, 576, 2112]
  let N : List ℕ := [127, 244, 314, 432, 541, 660, 792, 1102, 1220, 1290, 1548, 2087, 2212, 2338, 2565, 3078, 3716, 4179, 4304, 4370, 4625, 5008, 5186, 6147, 7426, 8297, 8416, 8488, 8713, 9288, 9992, 10273, 10656, 12353, 13504, 14849, 16256]
  have adj_eq : ∀ a b : Fin 14, (a.val,b.val) ∈ E ↔ (([1408,8832,12544,6272,11264,5632,2816] : List ℕ).getD a.val 0).testBit b.val = true := by decide
  have graphEq (x : Fin 14 → Bool) : hit x ↔ B x := by
    simp only [hit,B,adj_eq]
  have posOK : ∀ r ∈ P, B (mask r) := by decide +kernel
  have negOK : ∀ r ∈ N, ¬ B (mask r) := by decide +kernel
  -- The wire-monotonicity induction is adapted from R_meta_1988_2.
  have eval_and (l : List Bool) : GateOp.and.eval l = l.all id := rfl
  have eval_or (l : List Bool) : GateOp.or.eval l = l.any id := rfl
  have getD_snoc (xs : List Bool) (a : Bool) (k : ℕ) :
      (xs ++ [a]).getD k false =
        if k < xs.length then xs.getD k false else if k = xs.length then a else false := by
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
    split_ifs with h1 h2
    · rw [List.getElem?_append_left h1]
    · subst h2; simp
    · rw [List.getElem?_append_right (by omega)]
      rw [List.getElem?_eq_none (by simp; omega)]
      simp

  have wires_mono (C : PEqualNP.CircuitLowerBounds.Circuit) (hC : PEqualNP.MetaComplexity.Monotone2 C) (xs ys : List Bool)
      (hlen : xs.length = ys.length)
      (hxy : ∀ k, xs.getD k false = true → ys.getD k false = true) :
      ∀ k, (C.wires xs).getD k false = true → (C.wires ys).getD k false = true := by
    obtain ⟨gs, o⟩ := C
    unfold PEqualNP.CircuitLowerBounds.Circuit.wires
    induction gs generalizing xs ys with
    | nil => simpa using hxy
    | cons g gs ih =>
      simp only [List.foldl_cons]
      apply ih
      · simpa only [List.length_append, List.length_singleton] using congrArg (fun n => n + 1) hlen
      · intro k hk
        simp only [getD_snoc, hlen] at hk ⊢
        split_ifs at hk ⊢ with h1 h2
        · exact hxy k hk
        · have hop := (hC g List.mem_cons_self).1
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
          rcases hop with hop | hop
          · simp only [hop, eval_and, List.all_map, Function.comp_apply, id,
              List.all_eq_true] at hk ⊢
            exact fun j hj => hxy j (hk j hj)
          · simp only [hop, eval_or, List.any_map, Function.comp_apply, id,
              List.any_eq_true] at hk ⊢
            obtain ⟨j, hj, hjv⟩ := hk
            exact ⟨j, hj, hxy j hjv⟩
      · intro g' hg'
        exact hC g' (List.mem_cons_of_mem _ hg')


  have monot (w : ℕ) {x y : Fin 14 → Bool} (leXY : ∀ i, x i = true → y i = true) :
      val w x = true → val w y = true :=
    wires_mono C monoC (List.ofFn x) (List.ofFn y) (by simp) (by
      intro k hk
      by_cases h : k < 14
      · rw [List.getD_eq_getElem _ _ (by simpa using h)] at hk ⊢
        simp only [List.getElem_ofFn] at hk ⊢
        exact leXY ⟨k,h⟩ hk
      · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt h)] at hk
        cases hk) w
  have ext {i j : ℕ} (disagree : ∃ x, ¬hit x ∧ val i x = false ∧ val j x = true)
      (separates : ∀ x, ¬hit x → val i x = false ∨ val j x = false) :
      ∃ r ∈ N, val i (mask r) = false ∧ val j (mask r) = true := by
    obtain ⟨x,hx,_,high⟩ := disagree
    obtain ⟨r,hr,sup⟩ := boundary x (fun yes => hx ((graphEq x).mpr yes))
    have hj := monot j (x:=x) (y:=mask r) sup high
    exact ⟨r,hr,(separates _ (fun h => negOK r hr ((graphEq _).mp h))).resolve_right
      (by simp [hj]),hj⟩
  have d1 := ext diffU no
  have d2 := ext diffV (fun x hx => (no x hx).symm)
  have posRows (r : ℕ) (hr : r ∈ P) := both _ ((graphEq _).mpr (posOK r hr))
  have negRows (r : ℕ) (hr : r ∈ N) := no _ (fun h => negOK r hr ((graphEq _).mp h))
  have combine (x : Fin 14 → Bool) : (val u x = true ∧ val v x = true) ↔ B x := by
    constructor
    · rintro ⟨yes1,yes2⟩
      by_contra fail
      rcases no x (fun h => fail ((graphEq x).mp h)) with h | h
      · exact Bool.noConfusion (yes1.symm.trans h)
      · exact Bool.noConfusion (yes2.symm.trans h)
    · exact fun h => both x ((graphEq x).mpr h)
  rcases sensitivity (val u) (val v) combine with large | large
  · exact finite C u v monoC posRows negRows d1 d2 large
  · exact finite C v u monoC (fun r hr => (posRows r hr).symm)
      (fun r hr => (negRows r hr).symm) d2 d1 large

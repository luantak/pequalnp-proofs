import Mathlib

namespace PEqualNP.Alternatives.FiveCycleDepthThree

abbrev Mask := BitVec 32
abbrev Input := Fin 5 → Bool

-- Bit a is the value of an input wire on the five-bit assignment a.
def wire : Fin 5 → Mask :=
  ![2863311530, 3435973836, 4042322160, 4278255360, 4294901760]

def goalMask : Mask :=
  (wire 0 &&& wire 1) ||| (wire 1 &&& wire 2) ||| (wire 2 &&& wire 3) |||
    (wire 3 &&& wire 4) ||| (wire 4 &&& wire 0)

def inputs := List.ofFn wire

def next (s : List Mask) : List Mask :=
  (s.flatMap fun p => s.flatMap fun q => [p &&& q, p ||| q]).eraseDups

lemma pair_mem (s : List Mask) (p q : Mask) (hp : p ∈ s) (hq : q ∈ s) :
    (p &&& q) ∈ next s ∧ (p ||| q) ∈ next s := by
  constructor <;> apply List.mem_eraseDups.mpr <;>
    apply List.mem_flatMap.mpr <;> refine ⟨p, hp, List.mem_flatMap.mpr ⟨q, hq, ?_⟩⟩ <;> simp

def allowed : ℕ → Mask → Prop
  | 0, p => p ∈ inputs
  | 1, p => p ∈ next inputs
  | 2, p => p ∈ next (next inputs)
  | 3, p => p ≠ goalMask
  | _ + 4, _ => True

-- Each child of a final AND must contain every true assignment of the target.
-- Each child of a final OR must be contained in those assignments.
def below (p : Mask) : Bool := (p &&& goalMask) == p
def above (p : Mask) : Bool := (p &&& goalMask) == goalMask

set_option maxRecDepth 100000 in
lemma lastGate :
    let s := next (next inputs)
    ((s.filter above).all (fun p => (s.filter above).all (fun q => (p &&& q) != goalMask))) ∧
    ((s.filter below).all (fun p => (s.filter below).all (fun q => (p ||| q) != goalMask))) := by
  decide +kernel

lemma combine (k : ℕ) (p q : Mask) (hp : allowed k p) (hq : allowed k q) :
    allowed (k + 1) (p &&& q) ∧ allowed (k + 1) (p ||| q) := by
  match k with
  | 0 => exact pair_mem _ _ _ hp hq
  | 1 => exact pair_mem _ _ _ hp hq
  | 2 =>
    constructor
    · intro eq
      have both : above p ∧ above q := by
        simp only [above, ← eq, beq_iff_eq]
        constructor <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
          simp only [BitVec.getLsbD_and] <;>
          cases p.getLsbD i <;> cases q.getLsbD i <;> rfl
      exact (bne_iff_ne.mp (List.all_eq_true.mp (List.all_eq_true.mp lastGate.1 p
        (List.mem_filter.mpr ⟨hp, both.1⟩)) q (List.mem_filter.mpr ⟨hq, both.2⟩))) eq
    · intro eq
      have both : below p ∧ below q := by
        simp only [below, ← eq, beq_iff_eq]
        constructor <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
          simp only [BitVec.getLsbD_and, BitVec.getLsbD_or] <;>
          cases p.getLsbD i <;> cases q.getLsbD i <;> rfl
      exact (bne_iff_ne.mp (List.all_eq_true.mp (List.all_eq_true.mp lastGate.2 p
        (List.mem_filter.mpr ⟨hp, both.1⟩)) q (List.mem_filter.mpr ⟨hq, both.2⟩))) eq
  | 3 => exact ⟨True.intro, True.intro⟩
  | k + 4 => exact ⟨True.intro, True.intro⟩

def family (k : ℕ) : Set (Input → Bool) :=
  {f | ∃ p, allowed k p ∧ ∀ a : Fin 32, p.getLsbD a = f (fun i => (wire i).getLsbD a)}

lemma family_step (k : ℕ) (f g : Input → Bool) (hf : f ∈ family k) (hg : g ∈ family k) :
    (fun x => f x && g x) ∈ family (k+1) ∧ (fun x => f x || g x) ∈ family (k+1) := by
  obtain ⟨p, hp, fp⟩ := hf
  obtain ⟨q, hq, fq⟩ := hg
  obtain ⟨hand, hor⟩ := combine k p q hp hq
  exact ⟨⟨p &&& q, hand, fun a => by simp only [BitVec.getLsbD_and, fp a, fq a]⟩,
    ⟨p ||| q, hor, fun a => by simp only [BitVec.getLsbD_or, fp a, fq a]⟩⟩

end PEqualNP.Alternatives.FiveCycleDepthThree

open PEqualNP.Alternatives.FiveCycleDepthThree

theorem PEqualNP.Alternatives.FiveCycleDepthThree : ¬ (∀ T : ℕ → Set ((Fin 5 → Bool) → Bool),
    (∀ i : Fin 5, (fun x : Fin 5 → Bool => x i) ∈ T 0) →
    (∀ (k : ℕ) (f : (Fin 5 → Bool) → Bool), f ∈ T k → f ∈ T (k + 1)) →
    (∀ (k : ℕ) (f g : (Fin 5 → Bool) → Bool), f ∈ T k → g ∈ T k →
      (fun y : Fin 5 → Bool => f y && g y) ∈ T (k + 1) ∧
      (fun y : Fin 5 → Bool => f y || g y) ∈ T (k + 1)) →
    (fun z : Fin 5 → Bool =>
      (z 0 && z 1) || (z 1 && z 2) || (z 2 && z 3) || (z 3 && z 4) || (z 4 && z 0)) ∈ T 3) := by
  intro universal
  have leaves (i : Fin 5) : (fun x : Input => x i) ∈ family 0 :=
    ⟨wire i, List.mem_ofFn.mpr ⟨i, rfl⟩, fun _ => rfl⟩
  have lift (k : ℕ) (f : Input → Bool) (h : f ∈ family k) : f ∈ family (k+1) := by
    simpa using (family_step k f f h h).1
  obtain ⟨p, hp, heq⟩ := universal family leaves lift family_step
  apply hp
  apply BitVec.eq_of_getLsbD_eq
  intro a ha
  simpa [goalMask] using heq ⟨a, ha⟩

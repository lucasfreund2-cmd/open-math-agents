import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Powerset

/-!
# Union-closed families and co-Horn formulas

Problem: https://lefttosolve.com/p/mo-171753
Source: https://mathoverflow.net/questions/171753

The definitions and main statement below are those of the site's statement.
For each excluded assignment, we construct a co-Horn clause that excludes it
while preserving every member of the family. The conjunction of these clauses
therefore defines exactly the family. The converse establishes a full
characterization: a family is union-closed if and only if it is definable by a
finite conjunction of co-Horn clauses.

Pinned environment: Lean 4.33.1; Mathlib commit
0df444a360eaa60ab8c11dca51a86af692955474.
-/

namespace OMA.S_mo_171753

open Finset

structure CoHornClause (n : ℕ) where
  positive : Finset (Fin n)
  negative : Option (Fin n)

def SatisfiesCoHorn {n : ℕ} (s : Finset (Fin n)) (c : CoHornClause n) : Prop :=
  (∃ i ∈ c.positive, i ∈ s) ∨ ∃ i : Fin n, c.negative = some i ∧ i ∉ s

/-- A nonempty finite union of members remains in a union-closed family. -/
theorem finite_union_mem {n : ℕ} (F : Set (Finset (Fin n)))
    (hF : ∀ s ∈ F, ∀ t ∈ F, s ∪ t ∈ F)
    (G : Finset (Finset (Fin n))) (hne : G.Nonempty)
    (hG : ∀ s ∈ G, s ∈ F) : G.biUnion id ∈ F := by
  classical
  induction G using Finset.induction_on with
  | empty => simp at hne
  | @insert a G ha ih =>
      by_cases hneG : G.Nonempty
      · rw [Finset.biUnion_insert]
        exact hF a (hG a (Finset.mem_insert_self a G)) _
          (ih hneG (fun s hs => hG s (Finset.mem_insert_of_mem hs)))
      · have hzero : G = ∅ := Finset.not_nonempty_iff_eq_empty.mp hneG
        subst G
        simpa using hG a (Finset.mem_insert_self a ∅)

/-- Every excluded assignment can be separated by one valid co-Horn clause. -/
theorem separating_clause (n : ℕ) (F : Set (Finset (Fin n)))
    (hF : ∀ s ∈ F, ∀ t ∈ F, s ∪ t ∈ F)
    (s : Finset (Fin n)) (hs : s ∉ F) :
    ∃ c : CoHornClause n,
      (∀ t ∈ F, SatisfiesCoHorn t c) ∧ ¬ SatisfiesCoHorn s c := by
  classical
  let G : Finset (Finset (Fin n)) := Finset.univ.filter (fun t => t ∈ F ∧ t ⊆ s)
  by_cases hne : G.Nonempty
  · let u : Finset (Fin n) := G.biUnion id
    have huF : u ∈ F := finite_union_mem F hF G hne
      (fun t ht => (Finset.mem_filter.mp ht).2.1)
    have hus : u ⊆ s := by
      intro i hi
      obtain ⟨t, ht, hit⟩ := Finset.mem_biUnion.mp hi
      exact (Finset.mem_filter.mp ht).2.2 hit
    have hsu : ¬ s ⊆ u := by
      intro hsub
      have heq : s = u := Finset.Subset.antisymm hsub hus
      exact hs (heq ▸ huF)
    obtain ⟨i, his, hiu⟩ := Finset.not_subset.mp hsu
    refine ⟨⟨Finset.univ \ s, some i⟩, ?_, ?_⟩
    · intro t ht
      by_cases hts : t ⊆ s
      · right
        refine ⟨i, rfl, ?_⟩
        intro hit
        apply hiu
        exact Finset.mem_biUnion.mpr ⟨t, by simp [G, ht, hts], hit⟩
      · obtain ⟨j, hjt, hjs⟩ := Finset.not_subset.mp hts
        exact Or.inl ⟨j, by simp [hjs], hjt⟩
    · rintro (⟨j, hjp, hjs⟩ | ⟨j, hji, hjs⟩)
      · exact (Finset.mem_sdiff.mp hjp).2 hjs
      · have hij : i = j := Option.some.inj hji
        exact hjs (hij ▸ his)
  · refine ⟨⟨Finset.univ \ s, none⟩, ?_, ?_⟩
    · intro t ht
      have hts : ¬ t ⊆ s := by
        intro hsub
        exact hne ⟨t, by simp [G, ht, hsub]⟩
      obtain ⟨j, hjt, hjs⟩ := Finset.not_subset.mp hts
      exact Or.inl ⟨j, by simp [hjs], hjt⟩
    · rintro (⟨j, hjp, hjs⟩ | ⟨j, hji, _⟩)
      · exact (Finset.mem_sdiff.mp hjp).2 hjs
      · cases hji

/-- Conjoin one separating clause for every excluded assignment. -/
theorem cohorn_representation (n : ℕ) (F : Set (Finset (Fin n)))
    (hF : ∀ s ∈ F, ∀ t ∈ F, s ∪ t ∈ F) :
    ∃ clauses : List (CoHornClause n),
      ∀ s : Finset (Fin n), (∀ c ∈ clauses, SatisfiesCoHorn s c) ↔ s ∈ F := by
  classical
  let bad : Finset (Finset (Fin n)) := Finset.univ.filter (fun s => s ∉ F)
  let C : {s // s ∈ bad} → CoHornClause n := fun b =>
    Classical.choose (separating_clause n F hF b.val (Finset.mem_filter.mp b.property).2)
  have hC : ∀ b : {s // s ∈ bad},
      (∀ t ∈ F, SatisfiesCoHorn t (C b)) ∧ ¬ SatisfiesCoHorn b.val (C b) := by
    intro b
    exact Classical.choose_spec (separating_clause n F hF b.val
      (Finset.mem_filter.mp b.property).2)
  refine ⟨bad.attach.toList.map C, ?_⟩
  intro s
  constructor
  · intro hmodels
    by_contra hs
    let b : {t // t ∈ bad} := ⟨s, by simp [bad, hs]⟩
    have hb : C b ∈ bad.attach.toList.map C :=
      List.mem_map.mpr ⟨b, by simp, rfl⟩
    exact (hC b).2 (hmodels (C b) hb)
  · intro hs c hc
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hc
    exact (hC b).1 s hs

/-- The exact statement of LeftToSolve problem mo-171753. -/
theorem main : ∀ (n : ℕ) (F : Set (Finset (Fin n))),
    (∀ s ∈ F, ∀ t ∈ F, s ∪ t ∈ F) →
      ∃ clauses : List (CoHornClause n),
        ∀ s : Finset (Fin n), (∀ c ∈ clauses, SatisfiesCoHorn s c) ↔ s ∈ F := by
  exact cohorn_representation

/-- The models of a single co-Horn clause are closed under union. -/
theorem satisfiesCoHorn_union {n : ℕ} {s t : Finset (Fin n)}
    {c : CoHornClause n} (hs : SatisfiesCoHorn s c) (ht : SatisfiesCoHorn t c) :
    SatisfiesCoHorn (s ∪ t) c := by
  rcases hs with ⟨i, hi, his⟩ | ⟨i, hi, his⟩
  · exact Or.inl ⟨i, hi, Finset.mem_union.mpr (Or.inl his)⟩
  · rcases ht with ⟨j, hj, hjt⟩ | ⟨j, hj, hjt⟩
    · exact Or.inl ⟨j, hj, Finset.mem_union.mpr (Or.inr hjt)⟩
    · have hij : i = j := Option.some.inj (hi.symm.trans hj)
      subst j
      exact Or.inr ⟨i, hi, fun h ↦ (Finset.mem_union.mp h).elim his hjt⟩

/-- A finite conjunction of co-Horn clauses defines a union-closed family. -/
theorem cohorn_models_union_closed (n : ℕ) (F : Set (Finset (Fin n)))
    (hF : ∃ clauses : List (CoHornClause n),
      ∀ s : Finset (Fin n), (∀ c ∈ clauses, SatisfiesCoHorn s c) ↔ s ∈ F) :
    ∀ s ∈ F, ∀ t ∈ F, s ∪ t ∈ F := by
  obtain ⟨clauses, hclauses⟩ := hF
  intro s hs t ht
  apply (hclauses (s ∪ t)).mp
  intro c hc
  exact satisfiesCoHorn_union ((hclauses s).mpr hs c hc) ((hclauses t).mpr ht c hc)

/-- The full equivalence, strengthening the site's one-directional statement. -/
theorem characterization (n : ℕ) (F : Set (Finset (Fin n))) :
    (∀ s ∈ F, ∀ t ∈ F, s ∪ t ∈ F) ↔
      ∃ clauses : List (CoHornClause n),
        ∀ s : Finset (Fin n), (∀ c ∈ clauses, SatisfiesCoHorn s c) ↔ s ∈ F := by
  exact ⟨cohorn_representation n F, cohorn_models_union_closed n F⟩

end OMA.S_mo_171753

#print axioms OMA.S_mo_171753.main
#print axioms OMA.S_mo_171753.characterization

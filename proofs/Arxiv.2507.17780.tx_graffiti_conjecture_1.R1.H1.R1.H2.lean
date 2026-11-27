import OMAReductions.R_Arxiv_2507_17780_tx_graffiti_conjecture_1_R1_H1_R1

theorem OMA.solution : OMA.R_Arxiv_2507_17780_tx_graffiti_conjecture_1_R1_H1_R1.H2 := by
  intro s
  have bound : ∀ n : ℕ, ∀ s : List ℕ, s.length = n →
      SimpleGraph.residueAux s ≤ n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro s hs
      cases s with
      | nil => simp [SimpleGraph.residueAux]
      | cons d rest =>
        cases d with
        | zero =>
          simp only [SimpleGraph.residueAux]
          simp only [List.length_cons] at hs
          omega
        | succ d =>
          rw [SimpleGraph.residueAux] <;> try omega
          have hlt : (SimpleGraph.havelHakimiStep ((d + 1) :: rest)).length < n := by
            rw [SimpleGraph.havelHakimiStep_length_cons]
            simp only [List.length_cons] at hs
            omega
          exact (ih _ hlt _ rfl).trans (Nat.le_of_lt hlt)
  exact bound _ s rfl

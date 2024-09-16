import Mathlib

def O (f : ℕ -> ℕ) (g : ℕ -> ℕ) 
  := ∃ C : ℝ, C > 0 ∧ ∃ N : ℕ, N > 0 ∧ ∀ n : ℕ, n > N -> f n ≤ C * (g n)

def Ω (f : ℕ -> ℕ) (g : ℕ -> ℕ) 
  := ∃ C : ℝ, C > 0 ∧ ∃ N : ℕ, N > 0 ∧ ∀ n : ℕ, n > N -> C * (g n) ≤ f n

def Θ (f : ℕ -> ℕ) (g : ℕ -> ℕ) 
  := ∃ C₁: ℝ, C₁ > 0 ∧ ∃ C₂ : ℝ, C₂ > 0 ∧ ∃ N : ℕ, N > 0 ∧ ∀ n : ℕ, 
  n > N -> C₁ * (g n) ≤ f n ∧ f n ≤ C₂ * (g n)


lemma nat_linear (n₁ n₂ : ℕ) : n₁ ≤ n₂ ∨ n₂ < n₁ :=  by
  by_contra H
  simp at H
  linarith

lemma max_of_pos_is_pos (n₁ : ℕ) (n₂ : ℕ) : n₁ > 0 ∧ n₂ > 0 -> max n₁ n₂ > 0 := by
  intro h
  let ⟨n₁gz, n₂gz⟩ := h
  rw [max, Nat.instMax, maxOfLe]
  simp
  cases nat_linear n₁ n₂ with
  | inl h => 
    have ifisn₂ : (if n₁ ≤ n₂ then n₂ else n₁) = n₂ := by
      apply if_pos h
    rw [ifisn₂]
    assumption
  | inr h =>
    have ifisn₁ : (if n₁ ≤ n₂ then n₂ else n₁) = n₁ := by
      have notlt : ¬ n₁ ≤ n₂ := by
        simp
        assumption
      apply if_neg notlt
    rw [ifisn₁]
    assumption

lemma max_gt (n n₁ n₂ : ℕ) : n > max n₁ n₂ -> n > n₁ ∧ n > n₂  := by
  intro ngt
  rw [max, Nat.instMax, maxOfLe] at ngt
  simp at ngt
  cases nat_linear n₁ n₂ with
  | inl h =>
    have ifisn₂ : (if n₁ ≤ n₂ then n₂ else n₁) = n₂ := by
      apply if_pos h
    rw [ifisn₂] at ngt
    split_ands
    . simp
      eapply lt_of_le_of_lt h ngt
    . assumption
  | inr h =>
    have ifisn₁ : (if n₁ ≤ n₂ then n₂ else n₁) = n₁ := by
      have notlt : ¬ n₁ ≤ n₂ := by
        simp
        assumption
      apply if_neg notlt
    rw [ifisn₁] at ngt
    split_ands
    . assumption
    . simp
      eapply lt_trans h ngt

example : O f g ∧ Ω f g -> Θ f g := by
  intro h
  let ⟨hO, hΩ⟩ := h

  let ⟨hOC, ⟨hOCPos, hO⟩⟩ := hO
  let ⟨hΩC, ⟨hΩCPos, hΩ⟩⟩ := hΩ

  let ⟨hON, ⟨hONPos, hO⟩⟩ := hO
  let ⟨hΩN, ⟨hΩNPos, hΩ⟩⟩ := hΩ

  use hΩC
  split_ands
  . eapply hΩCPos

  use hOC
  split_ands
  . exact hOCPos

  let N := Nat.max hON hΩN
  use N
  split_ands
  . apply max_of_pos_is_pos
    split_ands; assumption'

  intro n ngN
  
  split_ands
  . have ngtN : n > hΩN := by
      have gt_max := max_gt n hON hΩN ngN
      exact gt_max.right
    exact hΩ n ngtN
  . have ngtN : n > hON := by
      have gt_max := max_gt n hON hΩN ngN
      exact gt_max.left
    exact hO n ngtN

import Mathlib

universe u

inductive BTree (k : Type) [Ord k] : Type
  | leaf : BTree k
  | branch (l : BTree k) (x : k) (r : BTree k) : BTree k

def BTree.height [Ord k] (t : BTree k) : Nat := match t with
  | leaf => 0
  | branch l _ r => max l.height r.height + 1

def hDiff [Ord k] (l : BTree k) (r : BTree k) := Int.natAbs $ Int.ofNat l.height - Int.ofNat r.height

inductive Avl (k : Type) [Ord k] : BTree k -> Prop
  | leaf : Avl k BTree.leaf
  | branch (l : BTree k) (r : BTree k) :
    Avl k l -> Avl k r -> (hDiff l r <= 1) ->
    Avl k (BTree.branch l x r)

def fixAvl [Ord k] (l : BTree k) (x : k) (r : BTree k) :
  Avl k l -> Avl k r -> (hDiff l r <= 2) -> exists t' : BTree k, Avl k t' :=
  fun lAvl rAvl hH =>
    match diff : Int.ofNat (l.height) - Int.ofNat (r.height) with
    | -2 => match r, rAvl with
      | BTree.leaf, _ => by
          contradiction
      | BTree.branch rl xr rr, Avl.branch _ _ rlAvl rrAvl rhH =>
        match rDiff : Int.ofNat rl.height - Int.ofNat rr.height with
          | -1 => by
              exists BTree.branch (BTree.branch l x rl) xr rr

              repeat constructor
              repeat assumption
              unfold hDiff at *
              conv at diff => lhs; rhs; unfold BTree.height
              have rr_rl : Int.ofNat rr.height = Int.ofNat rl.height + 1 := by
                linarith
              have l_max_rr_rl_2 : Int.ofNat l.height = Int.ofNat (max rr.height rl.height + 1) - 2 := by
                simp_all
                linarith
              rewrite [l_max_rr_rl_2]
              injection rr_rl with rr_rl
              rewrite [rr_rl]
              simp_all
              have H₁ : Int.ofNat rl.height + 1 + 1 - 2 - Int.ofNat rl.height = 0 := by
                grind_linarith
              simp_all
              
              assumption
              unfold hDiff at *
              conv at diff => lhs; rhs; unfold BTree.height
              conv => lhs; rhs; lhs; unfold BTree.height
              simp_all
              have rr_rl : Int.ofNat rr.height = Int.ofNat rl.height + 1 := by
                grind_linarith
              injection rr_rl with rr_rl
              rewrite [rr_rl] at diff
              rewrite [rr_rl]
              simp_all
              have l_rl : Int.ofNat l.height = Int.ofNat rl.height := by
                grind_linarith
              injection l_rl with l_rl
              rewrite [l_rl]
              simp_all
          | 0 => by
              exists BTree.branch (BTree.branch l x rl) xr rr

              repeat constructor
              repeat assumption
              unfold hDiff at *
              conv at diff => lhs; rhs; unfold BTree.height
              have rr_rl : Int.ofNat rr.height = Int.ofNat rl.height := by
                linarith
              have l_max_rr_rl_2 : Int.ofNat l.height = Int.ofNat (max rr.height rl.height + 1) - 2 := by
                simp_all
                linarith
              rewrite [l_max_rr_rl_2]
              injection rr_rl with rr_rl
              rewrite [rr_rl]
              simp_all
              grind
              
              assumption

              unfold hDiff at *
              conv at diff => lhs; rhs; unfold BTree.height
              conv => lhs; rhs; lhs; unfold BTree.height
              simp_all
              have rr_rl : Int.ofNat rr.height = Int.ofNat rl.height := by
                grind_linarith
              injection rr_rl with rr_rl
              rewrite [rr_rl] at diff
              rewrite [rr_rl]
              simp_all
              have l_rl : Int.ofNat l.height = Int.ofNat rl.height - 1 := by
                grind_linarith
              grind
          | 1 => 
            match rl, rlAvl with
              | BTree.leaf, _ => by
                unfold hDiff at *
                simp_all
                grind_linarith
              | BTree.branch rll xrl rlr, Avl.branch _ _ rllAvl rlrAvl rlhH => by
                  exists BTree.branch (BTree.branch l x rll) xrl (BTree.branch rlr xr rr);

                  repeat constructor
                  repeat assumption
                  unfold hDiff at *
                  conv at diff => lhs; rhs; unfold BTree.height; rhs; lhs; lhs; unfold BTree.height
                  conv at rDiff => lhs; lhs; rhs; unfold BTree.height
                  simp_all
                  have rr_max_rll_rlr : Int.ofNat rr.height = Int.ofNat (max rll.height rlr.height) := by
                    grind
                  injection rr_max_rll_rlr with rr_max_rll_rlr
                  rewrite [rr_max_rll_rlr] at diff
                  simp_all
                  grind

                  constructor
                  assumption

                  assumption

                  unfold hDiff at *
                  conv at diff => lhs; rhs; unfold BTree.height; rhs; lhs; lhs; unfold BTree.height
                  conv at rDiff => lhs; lhs; unfold BTree.height
                  simp_all
                  grind
                  
                  unfold hDiff at *
                  conv at diff => lhs; rhs; unfold BTree.height; rhs; lhs; lhs; unfold BTree.height
                  conv at rDiff => lhs; lhs; unfold BTree.height
                  conv => lhs; unfold BTree.height
                  grind
          | Int.negSucc (Nat.succ _) => by
              unfold hDiff at *
              rewrite [rDiff] at rhH
              contradiction
          | Int.ofNat (Nat.succ (Nat.succ _)) => by
              unfold hDiff at *
              rewrite [rDiff] at rhH
              contradiction
    | -1 => by
        exists BTree.branch l x r

        constructor
        assumption
        assumption

        unfold hDiff at *
        rewrite [diff] at *
        simp
    | 0 => by
        exists BTree.branch l x r

        constructor
        assumption
        assumption

        unfold hDiff at *
        rewrite [diff] at *
        simp
    | 1 => by
        exists BTree.branch l x r

        constructor
        assumption
        assumption

        unfold hDiff at *
        rewrite [diff] at *
        simp
    | 2 => match l, lAvl with
      | BTree.leaf, _ => by
        unfold hDiff at *
        unfold BTree.height at diff
        grind
      | BTree.branch ll lx lr, Avl.branch _ _ llAvl lrAvl lhH =>
        match lDiff : Int.ofNat ll.height - Int.ofNat lr.height with
          | -1 =>
            match lr, lrAvl with
              | BTree.leaf, _ => by
                unfold hDiff at *
                simp_all
              | BTree.branch lrl lrx lrr, Avl.branch _ _ lrlAvl lrrAvl lrhH => by
                  exists BTree.branch (BTree.branch ll lx lrl) lrx (BTree.branch lrr x r);

                  repeat constructor
                  repeat assumption

                  unfold hDiff at *
                  conv at diff => lhs; lhs; unfold BTree.height; rhs; lhs; rhs; unfold BTree.height
                  conv at lDiff => lhs; rhs; unfold BTree.height
                  simp_all
                  grind

                  constructor
                  assumption

                  assumption

                  unfold hDiff at *
                  conv at diff => lhs; lhs; rhs; unfold BTree.height; lhs; rhs; unfold BTree.height
                  conv at lDiff => lhs; rhs; unfold BTree.height
                  simp_all
                  grind

                  unfold hDiff at *
                  conv at diff => lhs; lhs; rhs; unfold BTree.height; lhs; rhs; unfold BTree.height
                  conv at lDiff => lhs; rhs; unfold BTree.height
                  conv => lhs; unfold BTree.height
                  simp_all
                  grind
          | 0 => by
              exists BTree.branch ll lx (BTree.branch lr x r);

              constructor
              assumption
              constructor
              assumption
              assumption
              
              unfold hDiff at *
              conv at diff => lhs; lhs; unfold BTree.height
              simp_all
              grind

              unfold hDiff at *
              conv at diff => lhs; lhs; unfold BTree.height
              conv => lhs; rhs; rhs; unfold BTree.height
              simp_all
              grind
          | 1 => by
              exists BTree.branch ll lx (BTree.branch lr x r);

              constructor
              assumption
              constructor
              assumption
              assumption
              
              unfold hDiff at *
              conv at diff => lhs; lhs; unfold BTree.height
              simp_all
              grind

              unfold hDiff at *
              conv at diff => lhs; lhs; unfold BTree.height
              conv => lhs; rhs; rhs; unfold BTree.height
              simp_all
              grind
          | Int.negSucc (Nat.succ _) => by
            unfold hDiff at *
            grind
          | Int.ofNat (Nat.succ (Nat.succ _)) => by
            unfold hDiff at *
            grind
    | (Int.negSucc (Nat.succ (Nat.succ _))) => by
      unfold hDiff at *
      rewrite [diff] at hH
      contradiction
    | (Int.ofNat (Nat.succ (Nat.succ (Nat.succ _)))) => by
      unfold hDiff at *
      rewrite [diff] at hH
      contradiction

def insert [Ord k] (t : BTree k) (x : k) : Avl k t -> ∃ t' : BTree k, hDiff t t' <= 1 ∧ Avl k t' :=
  fun tAvl => match t'' : t, tAvl with
    | BTree.leaf, _ => by
        exists BTree.branch BTree.leaf x BTree.leaf
        
        split_ands
        constructor
        constructor
        repeat assumption

        unfold hDiff at *
        grind
    | BTree.branch l y r, Avl.branch _ _ lAvl rAvl hH =>
        match compare x y with
          | Ordering.eq => by
              exists t
              split_ands

              rewrite [t'']
              unfold hDiff
              grind

              assumption
          | Ordering.lt => 
            let ⟨l', ⟨t'diff, l'Avl⟩⟩ := insert l x lAvl; by 
              let ⟨t', t'Avl⟩ := fixAvl l' y r l'Avl rAvl $ by
                unfold hDiff at *
                grind
              exists t'

              split_ands
              unfold hDiff at *
              conv => lhs; rhs; lhs; unfold BTree.height
              simp_all

              sorry
              sorry
          | Ordering.gt => sorry


import Mathlib.Tactic.Common

inductive Tree (k : Type) [LT k] : Type
  | leaf : Tree k
  | branch (l : Tree k) (x : k) (r : Tree k) : Tree k

def Tree.height [LT k] (t : Tree k) : Nat := match t with
  | leaf => 0
  | branch l _ r => max l.height r.height + 1

def hDiff [LT k] (l : Tree k) (r : Tree k) := Int.natAbs $ Int.ofNat l.height - Int.ofNat r.height

inductive Avl (k : Type) [LT k] : Tree k -> Type
  | leaf : Avl k Tree.leaf
  | branch (l : Tree k) (r : Tree k) :
    Avl k l -> Avl k r -> (hDiff l r <= 1) ->
    Avl k (Tree.branch l x r)

-- def rotLeft [LT k] (l : Tree k) (x : k) (r : Tree k) (rl : Tree k) (xr : k) (rr : Tree k) :
--     Avl k l -> Avl k rl -> Avl k rr -> hDiff 

def fixAvl [LT k] (l : Tree k) (x : k) (r : Tree k) :
  Avl k l -> Avl k r -> (hDiff l r <= 2) -> Σ t' : Tree k, Avl k t' := 
  fun lAvl rAvl hH => 
    match diff : Int.ofNat (l.height) - Int.ofNat (r.height) with
    | -2 => match r, rAvl with
      | Tree.leaf, _ => by
          contradiction
      | Tree.branch rl xr rr, Avl.branch _ _ rlAvl rrAvl rhH => 
        match rDiff : Int.ofNat rl.height - Int.ofNat rr.height with
          | -1 => 
            let t' := Tree.branch (Tree.branch l x rl) xr rr;
            Sigma.mk t' $ by
              repeat constructor
              repeat assumption
              unfold hDiff at *
              unfold Tree.height at diff
              simp_all
              sorry
              -- unfold Tree.height at diff
              -- simp at diff
              -- have  := Int.ofNat l.height = max (Int.ofNat rr.height) (Int.ofNat rl.height)
              -- case a =>
                 
              
              
            -- Sigma.mk t' tAvl'
          | 0 => sorry
          | 1 => sorry
          | Int.negSucc (Nat.succ _) => by
              unfold hDiff at *
              rewrite [rDiff] at rhH
              contradiction
          | Int.ofNat (Nat.succ (Nat.succ _)) => by
              unfold hDiff at *
              rewrite [rDiff] at rhH
              contradiction
    | -1 => Sigma.mk (Tree.branch l x r) (Avl.branch l r lAvl rAvl (by
        unfold hDiff at *
        rewrite [diff] at *
        simp  
      ))
    | 0 => Sigma.mk (Tree.branch l x r) (Avl.branch l r lAvl rAvl (by
        unfold hDiff at *
        rewrite [diff] at *
        simp  
      ))
    | 1 => Sigma.mk (Tree.branch l x r) (Avl.branch l r lAvl rAvl (by
        unfold hDiff at *
        rewrite [diff] at *
        simp  
      ))
    | 2 => sorry
    | (Int.negSucc (Nat.succ (Nat.succ _))) => by
      unfold hDiff at *
      rewrite [diff] at hH
      contradiction
    | (Int.ofNat (Nat.succ (Nat.succ (Nat.succ _)))) => by
      unfold hDiff at *
      rewrite [diff] at hH
      contradiction

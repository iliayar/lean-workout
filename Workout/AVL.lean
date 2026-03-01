import Mathlib

inductive BTree (k : Type) [Ord k] : Type
  | leaf : BTree k
  | branch (l : BTree k) (x : k) (r : BTree k) : BTree k

def BTree.height [Ord k] (t : BTree k) : Nat := match t with
  | leaf => 0
  | branch l _ r => max l.height r.height + 1

def hDiff [Ord k] (l : BTree k) (r : BTree k) := Int.natAbs $ Int.ofNat l.height - Int.ofNat r.height
def hDiff' [Ord k] (l : BTree k) (r : BTree k) := Int.ofNat l.height - Int.ofNat r.height

inductive Avl (k : Type) [Ord k] : BTree k -> Prop
  | leaf : Avl k BTree.leaf
  | branch (l : BTree k) (r : BTree k) :
    Avl k l -> Avl k r -> (hDiff l r <= 1) ->
    Avl k (BTree.branch l x r)

def fixAvl [Ord k] (l : BTree k) (x : k) (r : BTree k) :
  Avl k l -> Avl k r -> (hDiff l r <= 2) -> 
  ∃ t' : BTree k, (
    hDiff' l r = -2 ∧ t'.height >= r.height ∧ t'.height <= r.height + 1 ∨ 
    hDiff' l r = 2 ∧ t'.height >= l.height ∧ t'.height <= l.height + 1 ∨ 
    hDiff l r <= 1 ∧ t'.height = max l.height r.height + 1
  ) ∧ Avl k t' :=
  fun lAvl rAvl hH =>
    match diff : hDiff' l r with
    | -2 => match r, rAvl with
      | BTree.leaf, _ => by contradiction
      | BTree.branch rl xr rr, Avl.branch _ _ rlAvl rrAvl rhH =>
        match rDiff : hDiff' rl rr with
          | -1 => by
              exists BTree.branch (BTree.branch l x rl) xr rr

              split_ands
              grind +locals

              repeat constructor
              repeat assumption
              grind +locals
              
              assumption
              grind +locals
          | 0 => by
              exists BTree.branch (BTree.branch l x rl) xr rr

              split_ands
              grind +locals

              repeat constructor
              repeat assumption
              grind +locals
              
              assumption

              grind +locals
          | 1 => 
            match rl, rlAvl with
              | BTree.leaf, _ => by grind +locals
              | BTree.branch rll xrl rlr, Avl.branch _ _ rllAvl rlrAvl rlhH => by
                  exists BTree.branch (BTree.branch l x rll) xrl (BTree.branch rlr xr rr);

                  split_ands
                  grind +locals

                  repeat constructor
                  repeat assumption
                  grind +locals

                  constructor
                  assumption

                  assumption
                  grind +locals
                  grind +locals
          | Int.negSucc (Nat.succ _) => by grind +locals
          | Int.ofNat (Nat.succ (Nat.succ _)) => by grind +locals
    | -1 => by
        exists BTree.branch l x r

        split_ands
        grind +locals

        constructor
        assumption
        assumption

        grind +locals
    | 0 => by
        exists BTree.branch l x r

        split_ands
        grind +locals

        constructor
        assumption
        assumption

        grind +locals
    | 1 => by
        exists BTree.branch l x r

        split_ands
        grind +locals

        constructor
        assumption
        assumption

        grind +locals
    | 2 => match l, lAvl with
      | BTree.leaf, _ => by grind +locals
      | BTree.branch ll lx lr, Avl.branch _ _ llAvl lrAvl lhH =>
        match lDiff : hDiff' ll lr with
          | -1 =>
            match lr, lrAvl with
              | BTree.leaf, _ => by grind +locals
              | BTree.branch lrl lrx lrr, Avl.branch _ _ lrlAvl lrrAvl lrhH => by
                  exists BTree.branch (BTree.branch ll lx lrl) lrx (BTree.branch lrr x r);

                  split_ands
                  grind +locals

                  repeat constructor
                  repeat assumption

                  grind +locals

                  constructor
                  assumption

                  assumption

                  grind +locals

                  grind +locals
          | 0 => by
              exists BTree.branch ll lx (BTree.branch lr x r);

              split_ands
              grind +locals

              constructor
              assumption
              constructor
              assumption
              assumption
              
              grind +locals

              grind +locals
          | 1 => by
              exists BTree.branch ll lx (BTree.branch lr x r);

              split_ands
              grind +locals

              constructor
              assumption
              constructor
              assumption
              assumption
              
              grind +locals

              grind +locals
          | Int.negSucc (Nat.succ _) => by grind +locals
          | Int.ofNat (Nat.succ (Nat.succ _)) => by grind +locals
    | (Int.negSucc (Nat.succ (Nat.succ _))) => by grind +locals
    | (Int.ofNat (Nat.succ (Nat.succ (Nat.succ _)))) => by grind +locals

def insert [Ord k] (t : BTree k) (x : k) :
  Avl k t -> ∃ t' : BTree k, (t'.height >= t.height ∧ t'.height <= t.height + 1) ∧ Avl k t' :=
  fun tAvl => match t'' : t, tAvl with
    | BTree.leaf, _ => by
        exists BTree.branch BTree.leaf x BTree.leaf
        
        split_ands
        grind +locals
        grind +locals
        constructor
        constructor
        constructor
        grind +locals
    | BTree.branch l y r, Avl.branch _ _ lAvl rAvl hH =>
        match compare x y with
          | Ordering.eq => by
              exists t
              split_ands

              rewrite [t'']
              grind +locals
              grind +locals

              assumption
          | Ordering.lt => 
            let ⟨l', ⟨l'diff, l'Avl⟩⟩ := insert l x lAvl; by 
              let ⟨t', ⟨t'diff, t'Avl⟩⟩ := fixAvl l' y r l'Avl rAvl $ by
                unfold hDiff at *
                grind +locals
              exists t'

              split_ands
              grind +locals
              grind +locals
              assumption
          | Ordering.gt =>
            let ⟨r', ⟨r'diff, r'Avl⟩⟩ := insert r x rAvl; by 
              let ⟨t', ⟨t'diff, t'Avl⟩⟩ := fixAvl l y r' lAvl r'Avl $ by
                unfold hDiff at *
                grind +locals
              exists t'

              split_ands
              grind +locals
              grind +locals
              assumption

import Mathlib

inductive BTree : Type
  | leaf : BTree
  | branch (l : BTree) (x : Int) (r : BTree) : BTree

def BTree.height (t : BTree) : Nat := match t with
  | leaf => 0
  | branch l _ r => max l.height r.height + 1

def hDiff (l : BTree) (r : BTree) := Int.natAbs $ Int.ofNat l.height - Int.ofNat r.height
def hDiff' (l : BTree) (r : BTree) := Int.ofNat l.height - Int.ofNat r.height

inductive Member : Int -> BTree -> Prop
  | left : Member x l -> Member x (BTree.branch l y r)
  | right : Member x r -> Member x (BTree.branch l y r)
  | root : Member x (BTree.branch l x r)

inductive Avl : BTree -> Prop
  | leaf : Avl BTree.leaf
  | branch :
    Avl l -> Avl r -> (hDiff l r <= 1) -> Avl (BTree.branch l x r)

def fixAvl (l : BTree) (x : Int) (r : BTree) :
  Avl l -> Avl r -> (hDiff l r <= 2) -> 
  ∃ t' : BTree, (
    hDiff' l r = -2 ∧ t'.height >= r.height ∧ t'.height <= r.height + 1 ∨ 
    hDiff' l r = 2 ∧ t'.height >= l.height ∧ t'.height <= l.height + 1 ∨ 
    hDiff l r <= 1 ∧ t'.height = max l.height r.height + 1
  ) ∧ Avl t' ∧ (∀ (y : Int), Member y (BTree.branch l x r) <-> Member y t') :=
  fun lAvl rAvl hH =>
    match diff : hDiff' l r with
    | -2 => match r, rAvl with
      | BTree.leaf, _ => by contradiction
      | BTree.branch rl xr rr, Avl.branch rlAvl rrAvl rhH =>
        match rDiff : hDiff' rl rr with
          | -1 | 0 => by
              -- Rotated
              exists BTree.branch (BTree.branch l x rl) xr rr

              -- Height and AVL
              split_ands
              grind +locals
              repeat constructor
              repeat assumption
              grind +locals
              assumption
              grind +locals

              -- Preserve elements
              intro x'
              constructor
              . intro tMem
                cases tMem with
                | left => apply Member.left; apply Member.left; assumption
                | right rMem =>
                  cases rMem with
                  | left => apply Member.left; apply Member.right; assumption
                  | right => apply Member.right; assumption
                  | root => apply Member.root
                | root => apply Member.left; apply Member.root
              . intro t'Mem
                cases t'Mem with
                | left lMem =>
                  cases lMem with
                  | left => apply Member.left; assumption
                  | right => apply Member.right; apply Member.left; assumption
                  | root => apply Member.root
                | right => apply Member.right; apply Member.right; assumption
                | root => apply Member.right; apply Member.root
          | 1 => 
            match rl, rlAvl with
              | BTree.leaf, _ => by grind +locals
              | BTree.branch rll xrl rlr, Avl.branch rllAvl rlrAvl rlhH => by
                  -- Rotated
                  exists BTree.branch (BTree.branch l x rll) xrl (BTree.branch rlr xr rr);

                  -- Height and AVL
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

                  -- Preserve elements
                  intro x'
                  constructor
                  . intro tMem
                    cases tMem with
                    | left => apply Member.left; apply Member.left; assumption
                    | right rMem => 
                      cases rMem with
                      | left rlMem =>
                        cases rlMem with
                        | left => apply Member.left; apply Member.right; assumption
                        | right => apply Member.right; apply Member.left; assumption
                        | root => apply Member.root
                      | right => apply Member.right; apply Member.right; assumption
                      | root => apply Member.right; apply Member.root
                    | root => apply Member.left; apply Member.root
                  . intro tMem
                    cases tMem with
                    | left lMem =>
                      cases lMem with
                      | left => apply Member.left; assumption
                      | right => apply Member.right; apply Member.left; apply Member.left; assumption
                      | root => apply Member.root
                    | right rMem =>
                      cases rMem with
                      | left => apply Member.right; apply Member.left; apply Member.right; assumption
                      | right => apply Member.right; apply Member.right; assumption
                      | root => apply Member.right; apply Member.root
                    | root => apply Member.right; apply Member.left; apply Member.root
          | Int.negSucc (Nat.succ _) => by grind +locals
          | Int.ofNat (Nat.succ (Nat.succ _)) => by grind +locals
    | -1 | 0 | 1 => by
        -- Same tree
        exists BTree.branch l x r

        -- Height and AVL
        split_ands
        grind +locals
        constructor
        assumption
        assumption
        grind +locals

        -- Preserve elements
        intro x'
        constructor
        . intro; assumption
        . intro; assumption
    | 2 => match l, lAvl with
      | BTree.leaf, _ => by grind +locals
      | BTree.branch ll lx lr, Avl.branch llAvl lrAvl lhH =>
        match lDiff : hDiff' ll lr with
          | -1 =>
            match lr, lrAvl with
              | BTree.leaf, _ => by grind +locals
              | BTree.branch lrl lrx lrr, Avl.branch lrlAvl lrrAvl lrhH => by
                  -- Rotated
                  exists BTree.branch (BTree.branch ll lx lrl) lrx (BTree.branch lrr x r);

                  -- Height and AVL
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

                  -- Preserve elements
                  intro x'
                  constructor
                  . intro tMem
                    cases tMem with
                    | left lMem =>
                      cases lMem with
                      | left => apply Member.left; apply Member.left; assumption
                      | right lrMem =>
                        cases lrMem with
                        | left => apply Member.left; apply Member.right; assumption
                        | right => apply Member.right; apply Member.left; assumption
                        | root => apply Member.root
                      | root => apply Member.left; apply Member.root
                    | right => apply Member.right; apply Member.right; assumption
                    | root => apply Member.right; apply Member.root
                  . intro tMem
                    cases tMem with
                    | left lMem =>
                      cases lMem with
                      | left => apply Member.left; apply Member.left; assumption
                      | right => apply Member.left; apply Member.right; apply Member.left; assumption
                      | root => apply Member.left; apply Member.root
                    | right rMem =>
                      cases rMem with
                      | left => apply Member.left; apply Member.right; apply Member.right; assumption
                      | right => apply Member.right; assumption
                      | root => apply Member.root
                    | root => apply Member.left; apply Member.right; apply Member.root
          | 0 | 1 => by
              -- Rotated
              exists BTree.branch ll lx (BTree.branch lr x r);

              -- Height and AVL
              split_ands
              grind +locals
              constructor
              assumption
              constructor
              assumption
              assumption
              grind +locals
              grind +locals

              -- Preserve elements
              intro x'
              constructor
              . intro tMem
                cases tMem with
                | left lMem => 
                  cases lMem with
                  | left => apply Member.left; assumption
                  | right => apply Member.right; apply Member.left; assumption
                  | root => apply Member.root
                | right => apply Member.right; apply Member.right; assumption
                | root => apply Member.right; apply Member.root
              . intro t'Mem
                cases t'Mem with
                | left => apply Member.left; apply Member.left; assumption
                | right rMem => 
                  cases rMem with
                  | left => apply Member.left; apply Member.right; assumption
                  | right => apply Member.right; assumption
                  | root => apply Member.root
                | root => apply Member.left; apply Member.root
          | Int.negSucc (Nat.succ _) => by grind +locals
          | Int.ofNat (Nat.succ (Nat.succ _)) => by grind +locals
    | (Int.negSucc (Nat.succ (Nat.succ _))) => by grind +locals
    | (Int.ofNat (Nat.succ (Nat.succ (Nat.succ _)))) => by grind +locals

def insert (t : BTree) (x : Int) :
  Avl t -> ∃ t' : BTree, (t'.height >= t.height ∧ t'.height <= t.height + 1) ∧ Avl t' ∧
  (∀ y, Member y t -> Member y t' ∧ (Member y t' -> y = x ∨ Member y t)) ∧ Member x t' :=
  fun tAvl => match t'' : t, tAvl with
    | BTree.leaf, _ => by
        -- Insertion
        exists BTree.branch BTree.leaf x BTree.leaf
        
        -- Height and AVL
        split_ands
        grind +locals
        grind +locals
        constructor
        constructor
        constructor
        grind +locals

        -- Preserve elements
        . intros; contradiction
        . apply Member.root
    | BTree.branch l y r, Avl.branch lAvl rAvl hH =>
        if x_eq_y : x == y then by
          exists t
          split_ands

          rewrite [t'']
          grind +locals
          grind +locals

          assumption

          . intro x' tMem
            split_ands
            . subst t''; assumption
            . intros; right; assumption
          . subst t''
            have x_eq_y : x = y := by
              aesop
            subst x_eq_y
            apply Member.root
        else if x_lt_y : x < y then
          let ⟨l', ⟨l'diff, l'Avl, l'Mem, xMem⟩⟩ := insert l x lAvl; by 
            let ⟨t', ⟨t'diff, t'Avl, t'Mem⟩⟩ := fixAvl l' y r l'Avl rAvl $ by
              unfold hDiff at *
              grind +locals
            -- Insertion to left
            exists t'

            -- Height and AVL
            split_ands
            grind +locals
            grind +locals
            assumption

            -- Preserve elements
            intro x'
            . intro tMem
              specialize t'Mem x'
              specialize l'Mem x'
              split_ands
              . rw [<-t'Mem]
                cases tMem with
                | left lMem => 
                  apply Member.left
                  specialize l'Mem lMem
                  cases l'Mem
                  assumption
                | right => apply Member.right; assumption
                | root => apply Member.root
              . intros; right; assumption
            . specialize t'Mem x
              rw [<-t'Mem]
              apply Member.left; assumption
        else
          let ⟨r', ⟨r'diff, r'Avl, r'Mem, xMem⟩⟩ := insert r x rAvl; by 
            let ⟨t', ⟨t'diff, t'Avl, t'Mem⟩⟩ := fixAvl l y r' lAvl r'Avl $ by
              unfold hDiff at *
              grind +locals
            -- Insertion to left
            exists t'

            -- Height and AVL
            split_ands
            grind +locals
            grind +locals
            assumption

            -- Preserve elements
            intro x'
            . intro tMem
              specialize t'Mem x'
              specialize r'Mem x'
              split_ands
              . rw [<-t'Mem]
                cases tMem with
                | left => apply Member.left; assumption
                | right rMem =>
                  apply Member.right
                  specialize r'Mem rMem
                  cases r'Mem
                  assumption
                | root => apply Member.root
              . intros; right; assumption
            . specialize t'Mem x
              rw [<-t'Mem]
              apply Member.right; assumption

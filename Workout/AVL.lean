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

inductive Bst : BTree -> Prop
  | leaf : Bst BTree.leaf
  | branch : Bst l -> Bst r -> 
    (∀ xₗ, Member xₗ l -> xₗ < x) -> (∀ xᵣ, Member xᵣ r -> x < xᵣ) -> 
    Bst (BTree.branch l x r)

inductive Avl : BTree -> Prop
  | leaf : Avl BTree.leaf
  | branch :
    Avl l -> Avl r -> (hDiff l r <= 1) -> Avl (BTree.branch l x r)

def fixAvl (l : BTree) (x : Int) (r : BTree) :
  Avl l -> Avl r -> Bst (BTree.branch l x r) -> (hDiff l r <= 2) -> 
  ∃ t' : BTree, (
    hDiff' l r = -2 ∧ t'.height >= r.height ∧ t'.height <= r.height + 1 ∨ 
    hDiff' l r = 2 ∧ t'.height >= l.height ∧ t'.height <= l.height + 1 ∨ 
    hDiff l r <= 1 ∧ t'.height = max l.height r.height + 1
  ) ∧ Avl t' ∧ (∀ (y : Int), Member y (BTree.branch l x r) <-> Member y t')  ∧ Bst t' :=
  fun lAvl rAvl tBst hH =>
    match diff : hDiff' l r with
    | -2 => match r, rAvl with
      | BTree.leaf, _ => by contradiction
      | BTree.branch rl xr rr, Avl.branch rlAvl rrAvl rhH =>
        match rDiff : hDiff' rl rr with
          | -1 | 0 => by
              -- Rotated
              exists BTree.branch (BTree.branch l x rl) xr rr

              split_ands

              -- Height and AVL
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

              -- Bst
              cases tBst with 
              | branch lBst rBst xlH xrH =>
                cases rBst with
                | branch rlBst rrBst xrlH xrrH =>
                  constructor
                  . constructor
                    assumption
                    assumption
                    assumption
                    intro x' x'rlMem
                    have x'rMem : Member x' (BTree.branch rl xr rr) := by apply Member.left; assumption
                    specialize xrH x' x'rMem
                    assumption
                  . assumption
                  . intro x' x'rMem
                    cases x'rMem with
                    | left x'rlMem =>
                      specialize xlH x' x'rlMem
                      have xrMemr : Member xr (BTree.branch rl xr rr) := by apply Member.root
                      specialize xrH xr xrMemr
                      apply lt_trans; exact xlH; assumption
                    | right x'rrMem =>
                      specialize xrlH x' x'rrMem
                      assumption
                    | root => 
                      specialize xrH xr; apply xrH
                      apply Member.root
                  . assumption
          | 1 => 
            match rl, rlAvl with
              | BTree.leaf, _ => by grind +locals
              | BTree.branch rll xrl rlr, Avl.branch rllAvl rlrAvl rlhH => by
                  -- Rotated
                  exists BTree.branch (BTree.branch l x rll) xrl (BTree.branch rlr xr rr);

                  split_ands

                  -- Height and AVL
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

                  -- BST
                  cases tBst with
                  | branch lBst rBst lxH rxH =>
                    cases rBst with
                    | branch rlBst rrBst rlxH rrxH =>
                      cases rlBst with
                      | branch rllBst rlrBst rllxH rlrxH =>
                        constructor
                        . constructor
                          . assumption
                          . assumption
                          . assumption
                          . intros x' x'rllMem
                            apply rxH
                            apply Member.left; apply Member.left; assumption
                        . constructor
                          . assumption
                          . assumption
                          . intros x' x'rlrMem
                            apply rlxH
                            apply Member.right; assumption
                          . assumption
                        . intros x' x'lMem
                          cases x'lMem with
                          | left x'llMem =>
                            apply lt_trans; apply lxH
                            assumption
                            apply rxH
                            apply Member.left; apply Member.root
                          | right x'lrMem =>
                            apply rllxH
                            assumption
                          | root =>
                            apply rxH; apply Member.left; apply Member.root
                        . intros x' x'rMem
                          cases x'rMem with
                          | left x'rlMem =>
                            apply rlrxH; assumption
                          | right x'rrMem => 
                            apply lt_trans; apply rlxH
                            apply Member.root
                            apply rrxH; assumption
                          | root => apply rlxH; apply Member.root

          | Int.negSucc (Nat.succ _) => by grind +locals
          | Int.ofNat (Nat.succ (Nat.succ _)) => by grind +locals
    | -1 | 0 | 1 => by
        -- Same tree
        exists BTree.branch l x r

        split_ands

        -- Height and AVL
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

        -- Bst
        assumption
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

                  split_ands

                  -- Height and AVL
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

                  -- BST
                  cases tBst with
                  | branch lBst rBst xlH xrH =>
                    cases lBst with
                    | branch llBst lrBst xllH xlrH =>
                      cases lrBst with
                      | branch lrlBst lrrBst xlrlH xlrrH =>
                        constructor
                        . constructor
                          . assumption
                          . assumption
                          . assumption
                          . intros x' x'lrlMem
                            apply xlrH; apply Member.left; assumption
                        . constructor
                          . assumption
                          . assumption
                          . intros x' x'lrrMem
                            apply xlH
                            apply Member.right; apply Member.right; assumption
                          . assumption
                        . intros x' x'lMem
                          cases x'lMem with
                          | left x'llMem =>
                            apply lt_trans; apply xllH
                            assumption
                            apply xlrH; apply Member.root
                          | right x'lrMem =>
                            apply xlrlH; assumption
                          | root => apply xlrH; apply Member.root
                        . intros x' x'rMem
                          cases x'rMem with
                          | left x'rlMem =>
                            apply xlrrH; assumption
                          | right x'rrMem =>
                            apply lt_trans; apply xlH
                            apply Member.right; apply Member.root
                            apply xrH; assumption
                          | root => apply xlH; apply Member.right; apply Member.root
          | 0 | 1 => by
              -- Rotated
              exists BTree.branch ll lx (BTree.branch lr x r);

              split_ands

              -- Height and AVL
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

              -- Bst
              cases tBst with
                | branch lBst rBst xlH xrH =>
                  cases lBst with
                  | branch llBst lrBst xllH xlrH =>
                    constructor
                    . assumption
                    . constructor
                      assumption
                      assumption
                      intros x' x'lrMem
                      apply xlH
                      apply Member.right; assumption
                      assumption
                    . assumption
                    . intros x' x'lMem
                      cases x'lMem with
                      | left x'llMem =>
                        apply xlrH
                        assumption
                      | right x'lrMem =>
                        apply lt_trans; apply xlH
                        apply Member.root
                        apply xrH
                        assumption
                      | root => apply xlH; apply Member.root
          | Int.negSucc (Nat.succ _) => by grind +locals
          | Int.ofNat (Nat.succ (Nat.succ _)) => by grind +locals
    | (Int.negSucc (Nat.succ (Nat.succ _))) => by grind +locals
    | (Int.ofNat (Nat.succ (Nat.succ (Nat.succ _)))) => by grind +locals

def insert (t : BTree) (x : Int) :
  Avl t -> Bst t -> ∃ t' : BTree, (t'.height >= t.height ∧ t'.height <= t.height + 1) ∧ Avl t' ∧ Bst t' ∧
  (∀ y, (Member y t -> Member y t') ∧ (Member y t' -> y = x ∨ Member y t)) ∧ Member x t' :=
  fun tAvl tBst => match t'' : t, tAvl, tBst with
    | BTree.leaf, _, _ => by
        -- Insertion
        exists BTree.branch BTree.leaf x BTree.leaf

        split_ands
        
        -- Height and AVL
        grind +locals
        grind +locals
        constructor
        constructor
        constructor
        grind +locals

        -- BST
        constructor
        . constructor
        . constructor
        . intros _ contra
          cases contra
        . intros _ contra
          cases contra

        -- Preserve elements
        intros x'
        split_ands
        . intros; contradiction
        . intros x'Mem
          constructor
          . cases x'Mem with
            | left contra => cases contra
            | right contra => cases contra
            | root => eq_refl
        . apply Member.root
    | BTree.branch l y r, Avl.branch lAvl rAvl hH, Bst.branch lBst rBst xlH xrH =>
        if x_eq_y : x == y then by
          -- Insertion
          exists t
          split_ands

          -- Height and AVL
          rewrite [t'']
          grind +locals
          grind +locals
          assumption

          -- BST
          assumption

          -- Preserve elements
          intro x'
          split_ands
          . subst t''; intros; assumption
          . subst t''; intros; right; assumption
          . subst t''
            have x_eq_y : x = y := by
              aesop
            subst x_eq_y
            apply Member.root
        else if x_lt_y : x < y then
          let ⟨l', ⟨l'diff, l'Avl, l'Bst, l'Mem, xMem⟩⟩ := insert l x lAvl lBst; by 
            have l'rBst : Bst (l'.branch y r) := by
              constructor
              . assumption
              . assumption
              . intros x' x'l'Mem
                specialize l'Mem x'
                let ⟨_, l'Mem⟩ := l'Mem
                specialize l'Mem x'l'Mem
                cases l'Mem with
                | inl l'Mem => 
                  rw [l'Mem]; assumption
                | inr l'Mem => apply xlH; assumption
              . assumption
            let ⟨t', ⟨t'diff, t'Avl, t'Mem, t'Bst⟩⟩ := fixAvl l' y r l'Avl rAvl l'rBst $ by
              unfold hDiff at *
              grind +locals

            -- Insertion to left
            exists t'

            split_ands

            -- Height and AVL
            grind +locals
            grind +locals
            assumption

            -- BST
            assumption

            -- Preserve elements
            intro x'
            split_ands
            . intro tMem
              specialize t'Mem x'
              specialize l'Mem x'
              . rw [<-t'Mem]
                cases tMem with
                | left lMem => 
                  apply Member.left
                  let ⟨l'Mem, _⟩ := l'Mem
                  specialize l'Mem lMem
                  assumption
                | right => apply Member.right; assumption
                | root => apply Member.root
            . intros x't'Mem
              specialize t'Mem x'
              rw [<-t'Mem] at x't'Mem
              cases x't'Mem with
              | left x'l'Mem =>
                specialize l'Mem x'
                let ⟨_, l'Mem⟩ := l'Mem
                specialize l'Mem x'l'Mem
                cases l'Mem with
                | inl x'x => left; assumption
                | inr x'lMem => right; apply Member.left; assumption
              | right x'rMem => right; apply Member.right; assumption
              | root => right; apply Member.root
            . rw [<-t'Mem]
              apply Member.left; assumption
        else
          let ⟨r', ⟨r'diff, r'Avl, r'Bst, r'Mem, xMem⟩⟩ := insert r x rAvl rBst; by 
            have lr'Bst : Bst (l.branch y r') := by
              constructor
              . assumption
              . assumption
              . assumption
              . intros x' x'r'Mem
                specialize r'Mem x'
                let ⟨_, r'Mem⟩ := r'Mem
                specialize r'Mem x'r'Mem
                cases r'Mem with
                | inl r'Mem =>  rw [r'Mem]; grind
                | inr l'Mem => apply xrH; assumption
            let ⟨t', ⟨t'diff, t'Avl, t'Mem, t'Bst⟩⟩ := fixAvl l y r' lAvl r'Avl lr'Bst $ by
              unfold hDiff at *
              grind +locals

            -- Insertion to left
            exists t'

            split_ands

            -- Height and AVL
            grind +locals
            grind +locals
            assumption

            -- BST
            assumption

            -- Preserve elements
            intro x'
            split_ands
            . intro tMem
              specialize t'Mem x'
              specialize r'Mem x'
              . rw [<-t'Mem]
                cases tMem with
                | right rMem => 
                  apply Member.right
                  let ⟨r'Mem, _⟩ := r'Mem
                  specialize r'Mem rMem
                  assumption
                | left => apply Member.left; assumption
                | root => apply Member.root
            . intros x't'Mem
              specialize t'Mem x'
              rw [<-t'Mem] at x't'Mem
              cases x't'Mem with
              | right x'r'Mem =>
                specialize r'Mem x'
                let ⟨_, r'Mem⟩ := r'Mem
                specialize r'Mem x'r'Mem
                cases r'Mem with
                | inl x'x => left; assumption
                | inr x'lMem => right; apply Member.right; assumption
              | left x'lMem => right; apply Member.left; assumption
              | root => right; apply Member.root
            . rw [<-t'Mem]
              apply Member.right; assumption

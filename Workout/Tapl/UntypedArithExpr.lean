import Lean

import Workout.Logic

inductive aexpr : Type
| ATrue
| AFalse
| AZero
| ASucc (e : aexpr)
| APred (e : aexpr)
| AIsZero (e : aexpr)
| AIf (c : aexpr) (t : aexpr) (f : aexpr)
| AWrong

declare_syntax_cat aexpr
syntax "true" : aexpr
syntax "false" : aexpr
syntax "O" : aexpr
syntax "succ" aexpr : aexpr
syntax "pred" aexpr : aexpr
syntax "iszero" aexpr : aexpr
syntax "if" aexpr "then" aexpr "else" aexpr : aexpr
syntax "(" aexpr ")" : aexpr
syntax ident : aexpr

syntax "<{" aexpr "}>" : term

macro_rules
| `(aexpr| true) => `( aexpr.ATrue )
| `(aexpr| false) => `( aexpr.AFalse )
| `(aexpr| O) => `( aexpr.AZero )
| `(aexpr| succ $es:aexpr) => `(aexpr.ASucc <{ $es }> )
| `(aexpr| pred $es:aexpr) => `( aexpr.APred <{ $es }> )
| `(aexpr| iszero $es:aexpr) => `( aexpr.AIsZero <{ $es }> )
| `(aexpr| if $cs:aexpr then $ts:aexpr else $fs:aexpr) => 
  `( aexpr.AIf <{ $cs }> <{ $ts }> <{ $fs }> )
| `(aexpr| ( $es:aexpr ) ) => `( <{ $es }> )
| `(aexpr| $i:ident ) => `( $i )

macro_rules
| `( <{ $e:aexpr }> ) => `(aexpr| $e )

def eval (e : aexpr) : aexpr :=
  match e with
  | .ATrue => .ATrue
  | .AFalse => .AFalse
  | .AZero => .AZero
  | .ASucc e => match eval e with
    | v@ (.AZero) => .ASucc v
    | v@ (.ASucc _) => .ASucc v
    | _ => .AWrong
  | .APred e => match eval e with
    | .AZero => .AZero
    | .ASucc v => v
    | _ => .AWrong
  | .AIsZero e => match eval e with
    | .AZero => .ATrue
    | .ASucc _ => .AFalse
    | _ => .AWrong
  | .AIf c t f => match eval c with
    | .ATrue => eval t
    | .AFalse => eval f
    | _ => .AWrong
  | .AWrong => .AWrong

inductive nvalue : aexpr -> Prop
| NV_Zero : nvalue .AZero
| NV_Succ (nv : aexpr) : 
    nvalue nv ->
    nvalue (.ASucc nv)

inductive bvalue: aexpr -> Prop
| V_True : bvalue .ATrue
| V_False : bvalue .AFalse


def value (t : aexpr) := nvalue t ∨ bvalue t

def wrong (t : aexpr) := eval t = .AWrong

theorem eval_to_value : forall (e : aexpr), value (eval e) ∨ wrong e := by
  intros e
  induction e with
  | ATrue => simp!; left; right; constructor
  | AFalse => simp!; left; right; constructor
  | AZero => simp!; left; left; constructor
  | ASucc e IH => 
    unfold wrong at *
    simp!
    generalize (eval e) = e' at *
    cases e' with
    | AZero => simp; repeat constructor
    | ASucc e' => 
      simp; constructor; constructor
      cases IH with
      | inl H => 
        cases H with
        | inl => assumption
        | inr H => cases H
      | inr H => contradiction
    | _ => simp;
  | APred e IH => 
    unfold wrong at *
    simp!
    generalize (eval e) = e' at *
    cases e' with
    | AZero => simp; repeat constructor
    | ASucc e' => 
      simp
      cases IH with
      | inl IH => 
        cases IH with
        | inl H => left; left; cases H; assumption
        | inr H => cases H
      | inr IH => contradiction
    | _ => simp;
  | AIsZero e ih =>
    unfold wrong at *
    simp!
    generalize (eval e) = e' at *
    cases e' with
    | AZero => simp; right; constructor
    | ASucc => simp; right; constructor
    | _ => simp;
  | AIf ce te fe ihc iht ihf =>
    unfold wrong at *
    simp!
    generalize (eval ce) = e' at *
    cases e' with
    | ATrue => simp; assumption
    | AFalse => simp; assumption
    | _ => simp;
  | AWrong => unfold wrong; right; simp!

#reduce eval ((fun t => <{ if t then O else succ O }>) <{ true }>)

inductive eval_small_step : aepxr -> aexpr -> Prop
| E_IfTrue (t₂ : aexpr) (t₃ : aexpr) : eval_small_step <{ if true then t₂ else t₃ }> t₂
| E_IfFalse (t₂ : aexpr) (t₃ : aexpr) : eval_small_step <{ if false then t₂ else t₃ }> t₃
| E_If (t₁ t₁' : aexpr) (t₂ : aexpr) (t₃ : aexpr) : 
    eval_small_step t₁ t₁' ->
    eval_small_step <{ if t₁ then t₂ else t₃ }> <{ if t₁' then t₂ else t₃ }>
| E_Succ (t₁ t₁' : aexpr) :
    eval_small_step t₁ t₁' ->
    eval_small_step <{ succ t₁ }> <{ succ t₁' }>
| E_PredZero : eval_small_step <{ pred O }> <{ O }>
| E_PredSucc (t : aexpr) : 
    nvalue t ->
    eval_small_step <{ pred succ t }> <{ t }>
| E_Pred (t₁ t₁' : aexpr) :
    eval_small_step t₁ t₁' ->
    eval_small_step <{ pred t₁ }> <{ pred t₁' }>
| E_IsZeroZero : eval_small_step <{ iszero O }> <{ true }>
| E_IsZeroSucc (t : aexpr) :
    nvalue t ->
    eval_small_step <{ iszero (succ t) }> <{ false }>
| E_IsZero (t₁ t₁' : aexpr) :
    eval_small_step t₁ t₁' ->
    eval_small_step <{ iszero t₁ }> <{ iszero t₁' }>

notation t "=>" t' => eval_small_step t t'

theorem nvalue_no_steps : nvalue t -> ¬ t => t' := by
  intros Hnv H
  induction Hnv generalizing t' with
  | NV_Zero => cases H
  | NV_Succ nv _ IH =>
    cases H with
    | E_Succ t₁ t₁' H =>
      apply IH H

theorem value_no_steps : value t -> ¬ t => t' := by
  intros Hv H
  induction Hv generalizing t' with
  | inl Hnv => 
    apply (nvalue_no_steps Hnv H)
  | inr Hbv => cases Hbv with
    | V_True => cases H
    | V_False => cases H

-- NOTE: Excercise 3.5.14
theorem eval_small_step_determinstic : 
    (t => t') -> (t => t'') -> t' = t'' := by
  intros Ht' Ht''
  induction Ht' generalizing t'' with
  | E_IfTrue => 
    cases Ht'' with
    | E_IfTrue => eq_refl
    | E_If _ _ _ _ H => cases H
  | E_IfFalse =>
    cases Ht'' with
    | E_IfFalse => eq_refl
    | E_If _ _ _ _ H => cases H
  | E_If _ _ _ _ Ht₁ IH =>
    cases Ht'' with
    | E_IfTrue => cases Ht₁
    | E_IfFalse => cases Ht₁
    | _ => 
      congr
      apply IH
      assumption
  | E_Succ _ _ _ IH =>
    cases Ht''
    congr
    apply IH
    assumption
  | E_PredZero =>
    cases Ht'' with
    | E_PredZero => rfl
    | E_Pred _ _ H => cases H
  | E_IsZero _ t H IH =>
    cases Ht'' with
    | E_IsZeroZero => cases H
    | E_IsZero =>
      congr
      apply IH
      assumption
    | E_IsZeroSucc t₁ Hv =>
      cases H with
      | E_Succ _ t₁' =>
        have contra : ¬ t₁ => t₁' := nvalue_no_steps Hv
        contradiction
  | E_IsZeroSucc t Hv =>
    cases Ht'' with
    | E_IsZeroSucc => rfl
    | E_IsZero _ _ H =>
      cases H with
      | E_Succ _ t₁' H' =>
        have contra : ¬ t => t₁' := nvalue_no_steps Hv
        contradiction
  | E_IsZeroZero =>
    cases Ht'' with
    | E_IsZeroZero => rfl
    | E_IsZero _ _ H => cases H
  | E_Pred _ _ H IH =>
    cases Ht'' with
    | E_PredZero => cases H
    | E_PredSucc _ Hv =>
      cases H with
      | E_Succ _ t₁' H' =>
        have contra : ¬ t'' => t₁' := nvalue_no_steps Hv
        contradiction
    | E_Pred =>
      congr
      apply IH
      assumption
  | E_PredSucc t Hv =>
    cases Ht'' with
    | E_PredSucc => rfl
    | E_Pred _ _ H' =>
      cases H' with
      | E_Succ _ t₁ H₁ =>
        have contra : ¬ t => t₁ := nvalue_no_steps Hv
        contradiction

def normal_form (t : aexpr) := ¬ exists t', t => t'
def stucks (t : aexpr) := normal_form t ∧ ¬ value t

theorem wrong_succ : wrong t -> wrong (.ASucc t) := by
  intros Hw
  unfold wrong at *
  simp! at *
  generalize (eval t) = t' at *
  cases t' with
  | AZero => contradiction
  | ASucc _ => contradiction
  | _ => simp!

theorem wrong_pred : wrong t -> wrong (.APred t) := by
  intros Hw
  unfold wrong at *
  simp! at *
  generalize (eval t) = t' at *
  cases t' with
  | AZero => contradiction
  | ASucc _ => contradiction
  | _ => simp!

theorem wrong_iszero : wrong t -> wrong (.AIsZero t) := by
  intros Hw
  unfold wrong at *
  simp! at *
  generalize (eval t) = t' at *
  cases t' with
  | AZero => contradiction
  | ASucc _ => contradiction
  | _ => simp!

theorem normal_form_succ : normal_form (.ASucc t) -> normal_form t := by
  intros Hnf nHe
  have ⟨ t', He ⟩ := nHe
  apply Hnf
  exists (.ASucc t')
  constructor
  assumption

theorem normal_form_pred : normal_form (.APred t) -> normal_form t := by
  intros Hnf nHe
  have ⟨ t', He ⟩ := nHe
  apply Hnf
  exists (.APred t')
  constructor
  assumption

theorem normal_form_iszero : normal_form (.AIsZero t) -> normal_form t := by
  intros Hnf nHe
  have ⟨ t', He ⟩ := nHe
  apply Hnf
  exists (.AIsZero t')
  constructor
  assumption

theorem normal_form_if_cond : normal_form (.AIf c t f) -> normal_form c := by
  intros Hnf nHe
  have ⟨ c', He ⟩ := nHe
  apply Hnf
  exists (.AIf c' t f)
  constructor
  assumption

theorem normal_form_eval : normal_form t -> value t ∨ wrong t := by
  intros Hnf
  induction t with
  | ATrue => left; right; constructor
  | AFalse => left; right; constructor
  | AZero => left; left; constructor
  | AWrong => right; unfold wrong; simp!
  | ASucc t IH =>
    have H' := normal_form_succ Hnf
    specialize (IH H')
    cases IH with
    | inl H => cases H with
      | inl H => left; constructor; constructor; assumption
      | inr H => cases H with
        | V_True => right; unfold wrong; simp!
        | V_False => right; unfold wrong; simp!
    | inr H => right; apply wrong_succ; assumption
  | APred t IH =>
    have H' := normal_form_pred Hnf
    specialize (IH H')
    cases IH with
    | inl H => cases H with
      | inl H => cases H with
        | NV_Zero => 
          exfalso; apply Hnf;
          exists (.AZero)
          constructor
        | NV_Succ t₁ => 
          exfalso; apply Hnf;
          exists t₁
          constructor
          assumption
      | inr H => cases H with
        | V_True => right; unfold wrong; simp!
        | V_False => right; unfold wrong; simp!
    | inr H => right; apply wrong_pred; assumption
  | AIsZero t IH =>
    have H' := normal_form_iszero Hnf
    specialize (IH H')
    cases IH with
    | inl H => cases H with
      | inl H => cases H with
        | NV_Zero => 
          exfalso; apply Hnf;
          exists (.ATrue)
          constructor
        | NV_Succ t₁ => 
          exfalso; apply Hnf;
          exists (.AFalse)
          constructor
          assumption
      | inr H => cases H with
        | V_True => right; unfold wrong; simp!
        | V_False => right; unfold wrong; simp!
    | inr H => right; apply wrong_iszero; assumption
  | AIf c t f IHc _ _ =>
    have Hc' := normal_form_if_cond Hnf
    specialize (IHc Hc')
    cases IHc with
    | inl IHc => cases IHc with
      | inl IHc => cases IHc with
        | NV_Zero => right; unfold wrong; simp!
        | NV_Succ c' => 
          right; unfold wrong; simp!
          generalize (eval c') = c₁
          cases c₁ with
          | _ => simp
      | inr IHc => cases IHc with
        | V_True =>
          exfalso
          apply Hnf
          exists t
          constructor
        | V_False =>
          exfalso
          apply Hnf
          exists f
          constructor
    | inr IHc =>
      right; unfold wrong at *
      simp!; rewrite [IHc]
      simp

theorem stucks_is_wrong : stucks t -> wrong t := by
  intros Hnfnv
  have ⟨ Hnf, nHv ⟩ := Hnfnv
  have Hw := normal_form_eval Hnf
  cases Hw with
  | inl => contradiction
  | inr => assumption

theorem eval_nvalue : nvalue t -> eval t = t := by
  intros Hv
  induction Hv with
  | NV_Zero => simp!
  | NV_Succ t H IH => 
    simp! 
    rewrite [IH]
    cases t with
    | AZero => simp
    | ASucc => simp
    | _ => cases H

theorem eval_bvalue : bvalue t -> eval t = t := by
  intros Hv
  induction Hv with
  | V_True => simp!
  | V_False => simp!

theorem eval_value : value t -> eval t = t := by
  intros Hv
  cases Hv with
  | inl => apply eval_nvalue; assumption
  | inr => apply eval_bvalue; assumption

theorem wrong_is_not_value : wrong t -> ¬ value t := by
  intros Hw Hv
  unfold wrong at *
  have Hev := eval_value Hv
  rewrite [Hev] at Hw
  rewrite [Hw] at Hv
  cases Hv with
  | inl Hv => cases Hv
  | inr Hv => cases Hv

inductive eval_to : aexpr -> aexpr -> Prop
| E_Id (t t' : aexpr) :
    eval_small_step t t' ->
    eval_to t t'
| E_Refl (t : aexpr) : eval_to t t
| E_Trans (t t' t'' : aexpr) :
    eval_to t t' ->
    eval_to t' t'' ->
    eval_to t t''

notation t "=>>" t' => eval_to t t'

def stuck (t : aexpr) := ∃ t', (t =>> t') ∧ stucks t'

theorem eval_step : (t => t') -> eval t = eval t' := by
  intros He
  induction t generalizing t' with
  | AIf c t f IHc _ _ =>
    cases He with
    | E_IfTrue => simp!
    | E_IfFalse => simp!
    | E_If _ _ _ _ H =>
      simp!
      specialize (IHc H)
      rewrite [IHc]; rfl
  | AIsZero _ IH =>
    cases He with
    | E_IsZeroSucc t Hv =>
      simp!
      rewrite [eval_value (.inl Hv)] at *
      cases Hv with
      | NV_Zero => simp!
      | NV_Succ => simp!
    | E_IsZeroZero => simp!
    | E_IsZero _ _ H =>
      specialize (IH H)
      simp!
      rewrite [IH]
      rfl
  | APred _ IH =>
    cases He with
    | E_PredZero => simp!
    | E_PredSucc _ Hv =>
      simp!
      rewrite [eval_value (.inl Hv)] at *
      cases Hv with
      | NV_Zero => simp!
      | NV_Succ => simp!
    | E_Pred _ _ H =>
      simp!
      specialize (IH H)
      rewrite [IH]; rfl
  | ASucc _ IH =>
    cases He with
    | E_Succ _ _ H =>
      simp!
      specialize (IH H)
      rewrite [IH]; rfl
  | _ => cases He

theorem eval_steps : (t =>> t') -> eval t = eval t' := by
  intros He
  induction He with
  | E_Id t₁ t₂ H => apply (eval_step H)
  | E_Refl => rfl
  | E_Trans t₁ t₂ t₃ H₁ H₂ IH₁ IH₂ => 
    rewrite [IH₁]
    apply IH₂
     
theorem stuck_is_wrong : stuck t -> wrong t := by
  intros Hs
  unfold wrong
  have ⟨ t', ⟨ He, Hs⟩ ⟩ := Hs
  rewrite [eval_steps He] at *
  have H := stucks_is_wrong Hs
  apply H

-- FIXME: Most of the below is probably well automated

theorem trans_if_cond :
    (c =>> c') -> (<{ if c then t else f }> =>> <{ if c' then t else f }>) := by
    intros Hc
    induction Hc with
    | E_Id c c' H => 
        exact (.E_Id (.AIf c t f) (.AIf c' t f) (.E_If c c' t f H))
    | E_Refl c => exact (.E_Refl (.AIf c t f))
    | E_Trans c c' c'' _ _ IHIf IHIf' =>
      exact (.E_Trans
        <{ if c then t else f }> <{ if c' then t else f }> <{ if c'' then t else f }>
        IHIf IHIf')

theorem trans_iszero :
    (a =>> a') -> (<{ iszero a }> =>> <{ iszero a' }>) := by
    intros Ha
    induction Ha with
    | E_Id a a' H => 
        exact (.E_Id (.AIsZero a) (.AIsZero a') (.E_IsZero a a' H))
    | E_Refl a => exact (.E_Refl (.AIsZero a))
    | E_Trans a a' a'' _ _ IHIsZero IHIsZero' =>
      exact (.E_Trans <{ iszero a }> <{ iszero a' }> <{ iszero a'' }> IHIsZero IHIsZero')

theorem normal_form_exists_if : 
  (∃ t', (c=>>t') ∧ normal_form t') ->
  (∃ t', (t=>>t') ∧ normal_form t') ->
  (∃ t', (f=>>t') ∧ normal_form t') ->
  ∃ t', (c.AIf t f=>>t') ∧ normal_form t' := by
  intros IHc IHt IHf
  have ⟨ c', ⟨ IHce, IHcnf ⟩ ⟩ := IHc
  have HIfE : (.AIf c t f) =>> (.AIf c' t f) := trans_if_cond IHce
  cases c' with
  | ATrue =>
    have ⟨ t', ⟨ IHte, IHtnf ⟩ ⟩ := IHt
    exists t'
    and_intros
    . exact (.E_Trans (.AIf c t f) (.AIf .ATrue t f) t'
              HIfE
              (.E_Trans (.AIf .ATrue t f) t t' 
                (.E_Id (.AIf .ATrue t f) t (.E_IfTrue t f)) 
                IHte))
    . assumption
  | AFalse =>
    have ⟨ f', ⟨ IHfe, IHfnf ⟩ ⟩ := IHf
    exists f'
    and_intros
    . exact (.E_Trans (.AIf c t f) (.AIf .AFalse t f) f'
              HIfE
              (.E_Trans (.AIf .AFalse t f) f f' 
                (.E_Id (.AIf .AFalse t f) f (.E_IfFalse t f)) 
                IHfe))
    . assumption
  | AZero =>
    exists (.AIf .AZero t f)
    and_intros
    . exact (.E_Trans (.AIf c t f) (.AIf .AZero t f) (.AIf .AZero t f)
              HIfE
              (.E_Refl (.AIf .AZero t f)))
    . intros contra; have ⟨ _, contra ⟩ := contra; cases contra with
      | E_If _ _ _ _ contra => cases contra
  | AWrong =>
    exists (.AIf .AWrong t f)
    and_intros
    . exact (.E_Trans (.AIf c t f) (.AIf .AWrong t f) (.AIf .AWrong t f)
              HIfE
              (.E_Refl (.AIf .AWrong t f)))
    . intros contra; have ⟨ _, contra ⟩ := contra; cases contra with
      | E_If _ _ _ _ contra => cases contra
  | AIf c₁ t₁ f₁ =>
    exists (.AIf (.AIf c₁ t₁ f₁) t f)
    and_intros
    . exact (.E_Trans (.AIf c t f) (.AIf (.AIf c₁ t₁ f₁) t f) (.AIf (.AIf c₁ t₁ f₁) t f)
              HIfE
              (.E_Refl (.AIf (.AIf c₁ t₁ f₁) t f)))
    . intros Hnf'
      let ⟨ _, Hnf'⟩ := Hnf'
      cases Hnf' with
      | E_If _ c' _ =>
        apply IHcnf
        exists c'
  | AIsZero a =>
    exists (.AIf (.AIsZero a) t f)
    and_intros
    . exact (.E_Trans (.AIf c t f) (.AIf (.AIsZero a) t f) (.AIf (.AIsZero a) t f)
              HIfE
              (.E_Refl (.AIf (.AIsZero a) t f)))
    . intros Hnf'
      let ⟨ _, Hnf'⟩ := Hnf'
      cases Hnf' with
      | E_If _ c' _ =>
        apply IHcnf
        exists c'
  | APred a =>
    exists (.AIf (.APred a) t f)
    and_intros
    . exact (.E_Trans (.AIf c t f) (.AIf (.APred a) t f) (.AIf (.APred a) t f)
              HIfE
              (.E_Refl (.AIf (.APred a) t f)))
    . intros Hnf'
      let ⟨ _, Hnf'⟩ := Hnf'
      cases Hnf' with
      | E_If _ c' _ =>
        apply IHcnf
        exists c'
  | ASucc a =>
    exists (.AIf (.ASucc a) t f)
    and_intros
    . exact (.E_Trans (.AIf c t f) (.AIf (.ASucc a) t f) (.AIf (.ASucc a) t f)
              HIfE
              (.E_Refl (.AIf (.ASucc a) t f)))
    . intros Hnf'
      let ⟨ _, Hnf'⟩ := Hnf'
      cases Hnf' with
      | E_If _ c' _ =>
        apply IHcnf
        exists c'

theorem nvalue_exm t : ¬ nvalue t ∨ nvalue t := by
  induction t with
  | AZero => right; constructor
  | ASucc t IH =>
    cases IH with
    | inl IH =>
      left
      intros contra
      apply IH
      cases contra; assumption
    | inr IH => right; constructor; assumption
  | _ => left; intros contra; cases contra

theorem normal_form_exists_iszero :
  (∃ t', (a=>>t') ∧ normal_form t') ->
  ∃ t', (a.AIsZero=>>t') ∧ normal_form t' := by
  intros IHa
  have ⟨ a', ⟨ IHa, IHanf ⟩ ⟩ := IHa
  have HIsZeroE : (.AIsZero a) =>> (.AIsZero a') := trans_iszero IHa
  cases a' with
  | AZero =>
    exists .ATrue
    and_intros
    . exact (.E_Trans (.AIsZero a) (.AIsZero .AZero) (.ATrue)
              HIsZeroE
              (.E_Id (.AIsZero .AZero) (.ATrue) .E_IsZeroZero))
    . intros contra; have ⟨ _, contra ⟩ := contra; cases contra
  | ASucc as =>
    have HnvExm := nvalue_exm as
    cases HnvExm with
    | inl Hnv => 
      exists (.AIsZero (.ASucc as))
      and_intros
      . apply HIsZeroE
      . intros Hnf
        have ⟨ t', Hnf ⟩ := Hnf
        cases Hnf with
        | E_IsZeroSucc =>
          apply Hnv
          assumption
        | E_IsZero _ t₁ H =>
          apply IHanf
          exists t₁
    | inr Hnv =>
      exists (.AFalse)
      and_intros
      . exact (.E_Trans (.AIsZero a) (.AIsZero (.ASucc as)) (.AFalse)
                HIsZeroE (.E_Id (.AIsZero (.ASucc as)) .AFalse
                  (.E_IsZeroSucc as Hnv)))
      . intros contra; rcases contra with ⟨ _, contra ⟩; cases contra
  | ATrue =>
    exists <{ iszero true }>
    and_intros
    . assumption
    . intros contra; have ⟨ _, contra ⟩ := contra; cases contra with
      | E_IsZero _ _ contra => cases contra
  | AFalse =>
    exists <{ iszero false }>
    and_intros
    . assumption
    . intros contra; have ⟨ _, contra ⟩ := contra; cases contra with
      | E_IsZero _ _ contra => cases contra
  | AWrong =>
    exists (.AIsZero .AWrong)
    and_intros
    . assumption
    . intros contra; have ⟨ _, contra ⟩ := contra; cases contra with
      | E_IsZero _ _ contra => cases contra
  | AIf c t f =>
    exists (.AIsZero (.AIf c t f))
    and_intros
    . assumption
    . intros contra; have ⟨ _, contra ⟩ := contra; cases contra with
      | E_IsZero _ t₁ contra => apply IHanf; exists t₁
  | AIsZero a =>
    exists (.AIsZero (.AIsZero a))
    and_intros
    . assumption
    . intros contra; have ⟨ _, contra ⟩ := contra; cases contra with
      | E_IsZero _ t₁ contra => apply IHanf; exists t₁
  | APred a =>
    exists (.AIsZero (.APred a))
    and_intros
    . assumption
    . intros contra; have ⟨ _, contra ⟩ := contra; cases contra with
      | E_IsZero _ t₁ contra => apply IHanf; exists t₁

theorem trans_pred :
    (a =>> a') -> (<{ pred a }> =>> <{ pred a' }>) := by
    intros Ha
    induction Ha with
    | E_Id a a' H => 
        exact (.E_Id (.APred a) (.APred a') (.E_Pred a a' H))
    | E_Refl a => exact (.E_Refl (.APred a))
    | E_Trans a a' a'' _ _ IHPred IHPred' =>
      exact (.E_Trans <{ pred a }> <{ pred a' }> <{ pred a'' }> IHPred IHPred')

theorem normal_form_exists_pred :
  (∃ t', (a=>>t') ∧ normal_form t') ->
  ∃ t', (a.APred=>>t') ∧ normal_form t' := by
  intros IHa
  have ⟨ a', ⟨ IHa, IHanf ⟩ ⟩ := IHa
  have HPredE : (.APred a) =>> (.APred a') := trans_pred IHa
  cases a' with
  | AZero =>
    exists <{ O }>
    and_intros
    . exact (.E_Trans (.APred a) (.APred .AZero) (.AZero)
              HPredE (.E_Id (.APred .AZero) .AZero (.E_PredZero)))
    . assumption
  | ASucc as => 
    have HnvExm := nvalue_exm as
    cases HnvExm with
    | inl Hnv =>
      exists (.APred (.ASucc as))
      and_intros
      . apply HPredE
      . intros Hnf
        have ⟨ t', Hnf ⟩ := Hnf
        cases Hnf with
        | E_PredSucc t₁ =>
          apply Hnv; assumption
        | E_Pred _ t₁ H =>
          apply IHanf
          exists t₁
    | inr Hnv =>
      exists as
      and_intros
      . exact (.E_Trans (.APred a) (.APred (.ASucc as)) as
                HPredE (.E_Id (.APred (.ASucc as)) as (.E_PredSucc as Hnv)))
      . intros Hnf; apply IHanf; rcases Hnf with ⟨ t', Hnf ⟩; exists (.ASucc t')
        constructor; assumption
  | ATrue =>
    exists <{ pred true }>
    and_intros
    . assumption
    . intros contra; have ⟨ _, contra ⟩ := contra; cases contra with
      | E_Pred _ _ contra => cases contra
  | AFalse =>
    exists <{ pred false }>
    and_intros
    . assumption
    . intros contra; have ⟨ _, contra ⟩ := contra; cases contra with
      | E_Pred _ _ contra => cases contra
  | AWrong =>
    exists (.APred .AWrong)
    and_intros
    . assumption
    . intros contra; have ⟨ _, contra ⟩ := contra; cases contra with
      | E_Pred _ _ contra => cases contra
  | AIf c t f =>
    exists (.APred (.AIf c t f))
    and_intros
    . assumption
    . intros contra; have ⟨ _, contra ⟩ := contra; cases contra with
      | E_Pred _ t₁ contra => apply IHanf; exists t₁
  | AIsZero a =>
    exists (.APred (.AIsZero a))
    and_intros
    . assumption
    . intros contra; have ⟨ _, contra ⟩ := contra; cases contra with
      | E_Pred _ t₁ contra => apply IHanf; exists t₁
  | APred a =>
    exists (.APred (.APred a))
    and_intros
    . assumption
    . intros contra; have ⟨ _, contra ⟩ := contra; cases contra with
      | E_Pred _ t₁ contra => apply IHanf; exists t₁

theorem trans_succ :
    (a =>> a') -> (<{ succ a }> =>> <{ succ a' }>) := by
    intros Ha
    induction Ha with
    | E_Id a a' H => 
        exact (.E_Id (.ASucc a) (.ASucc a') (.E_Succ a a' H))
    | E_Refl a => exact (.E_Refl (.ASucc a))
    | E_Trans a a' a'' _ _ IHSucc IHSucc' =>
      exact (.E_Trans <{ succ a }> <{ succ a' }> <{ succ a'' }> IHSucc IHSucc')

theorem normal_form_exists_succ :
  (∃ t', (a=>>t') ∧ normal_form t') ->
  ∃ t', (a.ASucc=>>t') ∧ normal_form t' := by
  intros IHa
  have ⟨ a', ⟨ IHa, IHanf ⟩ ⟩ := IHa
  have HSuccE : (.ASucc a) =>> (.ASucc a') := trans_succ IHa
  cases a' with
  | ATrue =>
    exists <{ succ true }>
    and_intros
    . assumption
    . intros contra; have ⟨ _, contra ⟩ := contra; cases contra with
      | E_Succ _ _ contra => cases contra
  | AZero =>
    exists <{ succ O }>
    and_intros
    . assumption
    . intros contra; have ⟨ _, contra ⟩ := contra; cases contra with
      | E_Succ _ _ contra => cases contra
  | AFalse =>
    exists <{ succ false }>
    and_intros
    . assumption
    . intros contra; have ⟨ _, contra ⟩ := contra; cases contra with
      | E_Succ _ _ contra => cases contra
  | AWrong =>
    exists (.ASucc .AWrong)
    and_intros
    . assumption
    . intros contra; have ⟨ _, contra ⟩ := contra; cases contra with
      | E_Succ _ _ contra => cases contra
  | AIf c t f =>
    exists (.ASucc (.AIf c t f))
    and_intros
    . assumption
    . intros contra; have ⟨ _, contra ⟩ := contra; cases contra with
      | E_Succ _ t₁ contra => apply IHanf; exists t₁
  | AIsZero a =>
    exists (.ASucc (.AIsZero a))
    and_intros
    . assumption
    . intros contra; have ⟨ _, contra ⟩ := contra; cases contra with
      | E_Succ _ t₁ contra => apply IHanf; exists t₁
  | APred a =>
    exists (.ASucc (.APred a))
    and_intros
    . assumption
    . intros contra; have ⟨ _, contra ⟩ := contra; cases contra with
      | E_Succ _ t₁ contra => apply IHanf; exists t₁
  | ASucc a =>
    exists (.ASucc (.ASucc a))
    and_intros
    . assumption
    . intros contra; have ⟨ _, contra ⟩ := contra; cases contra with
      | E_Succ _ t₁ contra => apply IHanf; exists t₁

theorem normal_form_exists (t : aexpr) : ∃ t', (t =>> t') ∧ normal_form t' := by
  induction t with
  | ATrue => 
    exists .ATrue
    and_intros
    . exact (.E_Refl .ATrue)
    . intros contra; have ⟨ _, contra ⟩ := contra; cases contra
  | AZero => 
    exists .AZero
    and_intros
    . exact (.E_Refl .AZero)
    . intros contra; have ⟨ _, contra ⟩ := contra; cases contra
  | AFalse => 
    exists .AFalse
    and_intros
    . exact (.E_Refl .AFalse)
    . intros contra; have ⟨ _, contra ⟩ := contra; cases contra
  | AWrong => 
    exists .AWrong
    and_intros
    . exact (.E_Refl .AWrong)
    . intros contra; have ⟨ _, contra ⟩ := contra; cases contra
  | AIsZero a IHa => apply normal_form_exists_iszero IHa
  | APred a IHa => apply normal_form_exists_pred IHa
  | ASucc a IHa => apply normal_form_exists_succ IHa
  | AIf c t f IHc IHt IHf => apply normal_form_exists_if IHc IHt IHf

theorem wrong_is_stuck : wrong t -> stuck t := by
  intros Hw
  have ⟨ t', ⟨ He, Hnf ⟩ ⟩ := normal_form_exists t
  exists t' 
  and_intros
  . assumption
  . assumption
  . unfold wrong at Hw
    rewrite [eval_steps He] at Hw  
    apply wrong_is_not_value
    assumption

-- NOTE: Excercise 3.5.16
theorem wrong_stuck_agree : wrong t <-> stuck t := by
  constructor
  . apply wrong_is_stuck
  . apply stuck_is_wrong

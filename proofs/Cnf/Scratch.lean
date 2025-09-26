/-
Copyright (c) 2025 Johannes Bader. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Johannes Bader
-/

set_option pp.fieldNotation.generalized false

inductive SKIExpr
| S : SKIExpr
| K : SKIExpr
| I : SKIExpr
| app : SKIExpr → SKIExpr → SKIExpr
| var : Nat → SKIExpr
deriving Repr, DecidableEq

inductive isNormalForm : SKIExpr → Prop
| I0 : isNormalForm SKIExpr.I
| K0 : isNormalForm SKIExpr.K
| K1 : ∀ e, isNormalForm e → isNormalForm (SKIExpr.app SKIExpr.K e)
| S0 : isNormalForm SKIExpr.S
| S1 : ∀ e, isNormalForm e → isNormalForm (SKIExpr.app SKIExpr.S e)
| S2 : ∀ e₁ e₂, isNormalForm e₁ → isNormalForm e₂ → isNormalForm (SKIExpr.app (SKIExpr.app SKIExpr.S e₁) e₂)
| var : ∀ n, isNormalForm (SKIExpr.var n)

inductive closedSKI : SKIExpr → Prop
| S : closedSKI SKIExpr.S
| K : closedSKI SKIExpr.K
| I : closedSKI SKIExpr.I
| app : ∀ e₁ e₂, closedSKI e₁ → closedSKI e₂ → closedSKI (SKIExpr.app e₁ e₂)

inductive reduceSKIHelper : SKIExpr → SKIExpr → Prop
| S : ∀ e₁ e₂ e₃,
   reduceSKIHelper (SKIExpr.app (SKIExpr.app (SKIExpr.app SKIExpr.S e₁) e₂) e₃)
                      (SKIExpr.app (SKIExpr.app e₁ e₃) (SKIExpr.app e₂ e₃))
| K : ∀ e₁ e₂, reduceSKIHelper (SKIExpr.app (SKIExpr.app SKIExpr.K e₁) e₂) e₁
| I : ∀ e, reduceSKIHelper (SKIExpr.app SKIExpr.I e) e
| app1 : ∀ e₁ e₁' e₂, reduceSKIHelper e₁ e₁' → reduceSKIHelper (SKIExpr.app e₁ e₂) (SKIExpr.app e₁' e₂)
| app2 : ∀ e₁ e₂ e₂', reduceSKIHelper e₂ e₂' → reduceSKIHelper (SKIExpr.app e₁ e₂) (SKIExpr.app e₁ e₂')

inductive reduceSKI : SKIExpr → SKIExpr → Prop
| closed : closedSKI e₁ → reduceSKIHelper e₁ e₂ → reduceSKI e₁ e₂

inductive reduceSKIMulti : SKIExpr → SKIExpr → Prop
| refl : ∀ e, reduceSKIMulti e e
| step : ∀ e₁ e₂ e₃, reduceSKI e₁ e₂ → reduceSKIMulti e₂ e₃ → reduceSKIMulti e₁ e₃

theorem reduceSKIApp1 : ∀ e₁ e₁' e₂, closedSKI e₂ → reduceSKI e₁ e₁' → reduceSKI (SKIExpr.app e₁ e₂) (SKIExpr.app e₁' e₂) := by
  intros e₁ e₁' e₂ cl h
  cases h
  case closed cl' hlp =>
    apply reduceSKI.closed
    apply closedSKI.app
    exact cl'
    exact cl
    apply reduceSKIHelper.app1
    exact hlp

theorem reduceSKIApp2 : ∀ e₁ e₂ e₂', closedSKI e₁ → reduceSKI e₂ e₂' → reduceSKI (SKIExpr.app e₁ e₂) (SKIExpr.app e₁ e₂') := by
  intros e₁ e₂ e₂' cl h
  cases h
  case closed cl' hlp =>
    apply reduceSKI.closed
    apply closedSKI.app
    exact cl
    exact cl'
    apply reduceSKIHelper.app2
    exact hlp

theorem reduceSKIMultiApp1 : ∀ e₁ e₁' e₂, closedSKI e₂ → reduceSKIMulti e₁ e₁' → reduceSKIMulti (SKIExpr.app e₁ e₂) (SKIExpr.app e₁' e₂) := by
  intros e₁ e₁' e₂ cl h
  induction h
  case refl =>
    apply reduceSKIMulti.refl
  case step e1 e2 e3 h1 h2 ih =>
    apply reduceSKIMulti.step
    apply reduceSKIApp1
    exact cl
    exact h1
    exact ih

theorem reduceSKIMultiApp2 : ∀ e₁ e₂ e₂', closedSKI e₁ → reduceSKIMulti e₂ e₂' → reduceSKIMulti (SKIExpr.app e₁ e₂) (SKIExpr.app e₁ e₂') := by
  intros e₁ e₂ e₂' cl h
  induction h
  case refl =>
    apply reduceSKIMulti.refl
  case step e1 e2 e3 h1 h2 ih =>
    apply reduceSKIMulti.step
    apply reduceSKIApp2
    exact cl
    exact h1
    exact ih

def canReduceSKI (e : SKIExpr) : Prop :=
  ∃ e', reduceSKI e e'

inductive Lambda
| var : Nat → Lambda
| abs : Lambda → Lambda
| app : Lambda → Lambda → Lambda
deriving Repr, DecidableEq

def lift : Nat → Lambda → Lambda
| k, Lambda.var n => Lambda.var (if n < k then n else n + 1)
| k, Lambda.abs e => Lambda.abs (lift (k + 1) e)
| k, Lambda.app e₁ e₂ => Lambda.app (lift k e₁) (lift k e₂)

def lift0 := lift 0

def subst : Nat → Lambda → Lambda → Lambda
| n, Lambda.var m, e => if n = m then e else if n < m then Lambda.var (m - 1) else Lambda.var m
| n, Lambda.abs e, e' => Lambda.abs (subst (n+1) e (lift0 e'))
| n, Lambda.app e₁ e₂, e' => Lambda.app (subst n e₁ e') (subst n e₂ e')

def subst0 := subst 0

example : subst0 (Lambda.var 0) (Lambda.var 3) = (Lambda.var 3) := by
  simp [subst0, subst, lift0, lift]
example : subst0 (Lambda.var 1) (Lambda.var 3) = (Lambda.var 0) := by
  simp [subst0, subst, lift0, lift]
example : subst0 (Lambda.abs (Lambda.var 0)) (Lambda.var 3) = Lambda.abs (Lambda.var 0) := by
  simp [subst0, subst, lift0, lift]
example : subst0 (Lambda.abs (Lambda.var 1)) (Lambda.var 3) = Lambda.abs (Lambda.var 4) := by
  simp [subst0, subst, lift0, lift]

inductive isLambdaNormalForm : Lambda → Prop
| var : ∀ n, isLambdaNormalForm (Lambda.var n)
| abs : ∀ e, isLambdaNormalForm e → isLambdaNormalForm (Lambda.abs e)
| app : ∀ e₁ e₂, isLambdaNormalForm e₁ → isLambdaNormalForm e₂ →
  (¬ ∃ e', e₁ = Lambda.abs e') → -- e₁ is not an abstraction
  isLambdaNormalForm (Lambda.app e₁ e₂)

inductive reduceLambda : Lambda → Lambda → Prop
| beta : ∀ e₁ e₂, reduceLambda (Lambda.app (Lambda.abs e₁) e₂) (subst0 e₁ e₂)
| app1 : ∀ e₁ e₁' e₂, reduceLambda e₁ e₁' → reduceLambda (Lambda.app e₁ e₂) (Lambda.app e₁' e₂)
| app2 : ∀ e₁ e₂ e₂', reduceLambda e₂ e₂' → reduceLambda (Lambda.app e₁ e₂) (Lambda.app e₁ e₂')
| abs : ∀ e e', reduceLambda e e' → reduceLambda (Lambda.abs e) (Lambda.abs e')

def canReduceLambda (e : Lambda) : Prop :=
  ∃ e', reduceLambda e e'

inductive reduceLambdaMulti : Lambda → Lambda → Prop
| refl : ∀ e, reduceLambdaMulti e e
| step : ∀ e₁ e₂ e₃, reduceLambda e₁ e₂ → reduceLambdaMulti e₂ e₃ → reduceLambdaMulti e₁ e₃

theorem reduceLambdaMultiApp1 : ∀ e₁ e₁' e₂, reduceLambdaMulti e₁ e₁' → reduceLambdaMulti (Lambda.app e₁ e₂) (Lambda.app e₁' e₂) := by
  intros e₁ e₁' e₂ h
  induction h
  case refl =>
    apply reduceLambdaMulti.refl
  case step e₁ e₂ e₃ h1 h2 ih =>
    apply reduceLambdaMulti.step
    apply reduceLambda.app1
    exact h1
    exact ih

theorem reduceLambdaMultiApp2 : ∀ e₁ e₂ e₂', reduceLambdaMulti e₂ e₂' → reduceLambdaMulti (Lambda.app e₁ e₂) (Lambda.app e₁ e₂') := by
  intros e₁ e₂ e₂' h
  induction h
  case refl =>
    apply reduceLambdaMulti.refl
  case step e₁ e₂ e₃ h1 h2 ih =>
    apply reduceLambdaMulti.step
    apply reduceLambda.app2
    exact h1
    exact ih

inductive isClosedHelper : Nat → Lambda → Prop
| var : ∀ n k, n < k → isClosedHelper k (Lambda.var n)
| abs : ∀ e k, isClosedHelper (k + 1) e → isClosedHelper k (Lambda.abs e)
| app : ∀ e₁ e₂ k, isClosedHelper k e₁ → isClosedHelper k e₂ → isClosedHelper k (Lambda.app e₁ e₂)

def isClosed (e : Lambda) : Prop := isClosedHelper 0 e

inductive isClosedNormalForm : Lambda → Prop
| var : ∀ n, isClosedNormalForm (Lambda.var n)
| abs : ∀ e, isClosedNormalForm e → isClosedNormalForm (Lambda.abs e)
| app : ∀ e₁ e₂, isClosedNormalForm e₁ → isClosedNormalForm e₂ →
  ((¬ ∃ e', e₁ = Lambda.abs e') ∨ ¬ isClosed (Lambda.app e₁ e₂)) →
  isClosedNormalForm (Lambda.app e₁ e₂)

inductive reduceClosedLambda : Lambda → Lambda → Prop
| beta : ∀ e₁ e₂, isClosed (Lambda.app (Lambda.abs e₁) e₂) → reduceClosedLambda (Lambda.app (Lambda.abs e₁) e₂) (subst0 e₁ e₂)
| app1 : ∀ e₁ e₁' e₂, reduceClosedLambda e₁ e₁' → reduceClosedLambda (Lambda.app e₁ e₂) (Lambda.app e₁' e₂)
| app2 : ∀ e₁ e₂ e₂', reduceClosedLambda e₂ e₂' → reduceClosedLambda (Lambda.app e₁ e₂) (Lambda.app e₁ e₂')
| abs : ∀ e e', reduceClosedLambda e e' → reduceClosedLambda (Lambda.abs e) (Lambda.abs e')

def canReduceClosedLambda (e : Lambda) : Prop :=
  ∃ e', reduceClosedLambda e e'

def skiToLambda : SKIExpr → Lambda
| SKIExpr.var n => Lambda.var n
| SKIExpr.I =>
  Lambda.abs (Lambda.var 0)
| SKIExpr.K =>
  Lambda.abs (Lambda.abs (Lambda.var 1))
| SKIExpr.app SKIExpr.K e₁ =>
  Lambda.abs (skiToLambda e₁)
| SKIExpr.S =>
  Lambda.abs (Lambda.abs (Lambda.abs (
    Lambda.app
    (Lambda.app (Lambda.var 2) (Lambda.var 0))
    (Lambda.app (Lambda.var 1) (Lambda.var 0))
  )))
| SKIExpr.app SKIExpr.S e₁ =>
  Lambda.abs (Lambda.abs (
    Lambda.app
    (Lambda.app (lift0 (lift0 (skiToLambda e₁))) (Lambda.var 0))
    (Lambda.app (Lambda.var 1) (Lambda.var 0))
  ))
| SKIExpr.app (SKIExpr.app SKIExpr.S e₁) e₂ =>
  Lambda.abs (
    Lambda.app
    (Lambda.app (lift0 (skiToLambda e₁)) (Lambda.var 0))
    (Lambda.app (lift0 (skiToLambda e₂)) (Lambda.var 0))
  )
| SKIExpr.app e₁ e₂ =>
  Lambda.app (skiToLambda e₁) (skiToLambda e₂)

def skiToLambda2 : SKIExpr → Lambda
| SKIExpr.var n => Lambda.var n
| SKIExpr.I =>
  Lambda.abs (Lambda.var 0)
| SKIExpr.K =>
  Lambda.abs (Lambda.abs (Lambda.var 1))
| SKIExpr.S =>
  Lambda.abs (Lambda.abs (Lambda.abs (
    Lambda.app
    (Lambda.app (Lambda.var 2) (Lambda.var 0))
    (Lambda.app (Lambda.var 1) (Lambda.var 0))
  )))
| SKIExpr.app e₁ e₂ =>
  Lambda.app (skiToLambda2 e₁) (skiToLambda2 e₂)

def containsVar : Nat → Lambda → Bool
| n, Lambda.var m => n = m
| n, Lambda.abs e => containsVar (n + 1) e
| n, Lambda.app e₁ e₂ => containsVar n e₁ || containsVar n e₂

def skiContainsVar : SKIExpr → Bool
| SKIExpr.var m => 0 = m
| SKIExpr.app e₁ e₂ => skiContainsVar e₁ || skiContainsVar e₂
| _ => false

theorem closedSkiNoVar : ∀ e, closedSKI e → skiContainsVar e = false := by
  intros e h
  induction h
  case S => simp [skiContainsVar]
  case K => simp [skiContainsVar]
  case I => simp [skiContainsVar]
  case app e₁ e₂ h1 h2 ih1 ih2 =>
    simp [skiContainsVar]
    constructor
    case left =>
      exact ih1
    case right =>
      exact ih2

def abstract : SKIExpr -> SKIExpr
| SKIExpr.var 0 => SKIExpr.I
| SKIExpr.var (n+1) => SKIExpr.app SKIExpr.K (SKIExpr.var n)
| SKIExpr.app e₁ e₂ => if skiContainsVar e₁ || skiContainsVar e₂ then
  SKIExpr.app (SKIExpr.app SKIExpr.S (abstract e₁)) (abstract e₂) else
  SKIExpr.app SKIExpr.K (SKIExpr.app e₁ e₂)
| SKIExpr.S => SKIExpr.app SKIExpr.K SKIExpr.S
| SKIExpr.K => SKIExpr.app SKIExpr.K SKIExpr.K
| SKIExpr.I => SKIExpr.app SKIExpr.K SKIExpr.I

theorem closedSkiAbstract : ∀ e, closedSKI e → abstract e = SKIExpr.app SKIExpr.K e := by
  intros e h
  induction e
  case S => simp [abstract]
  case K => simp [abstract]
  case I => simp [abstract]
  case app e₁ e₂ ih1 ih2 =>
    simp [abstract]
    cases h
    case app h1 h2 =>
      constructor
      case left =>
        apply closedSkiNoVar
        exact h1
      case right =>
        apply closedSkiNoVar
        exact h2
  case var n =>
    cases h

-- theorem reduceSKIMultiAbstract : ∀ e₁ e₂, reduceSKIMulti e₁ e₂ → reduceSKIMulti (abstract e₁) (abstract e₂) := by
--   intros e₁ e₂ h
--   induction h
--   case refl =>
--     apply reduceSKIMulti.refl
--   case step e₁ e₂ e₃ h1 h2 ih =>
--     apply reduceSKIMulti.step
--     apply reduceSKI.app1
--     apply reduceSKI.app1
--     exact h1
--     exact ih

def starAbstraction : Lambda → SKIExpr
| Lambda.var n => SKIExpr.var n
| Lambda.app e₁ e₂ => SKIExpr.app (starAbstraction e₁) (starAbstraction e₂)
| Lambda.abs e => abstract (starAbstraction e)

theorem reduceLambdaEqual : ∀ e₁ e₂ e3, reduceLambda e₁ e₂ → e₂ = e3 → reduceLambda e₁ e3 := by
  intros e₁ e₂ e3 h1 h2
  subst h2
  apply h1

theorem subst_lift : subst n (lift n e₁) e = e₁ := by
  induction e₁ generalizing n e
  case var m =>
    rw [lift, subst]
    by_cases h1 : m < n
    case pos =>
      simp [h1]
      simp [Nat.ne_of_lt' h1]
      intro h2
      exfalso
      exact Nat.not_lt_of_lt h1 h2
    case neg =>
      simp [h1]
      by_cases h2 : n = m + 1
      case pos =>
        exfalso
        rw [h2] at h1
        exact h1 (Nat.lt_succ_self m)
      case neg =>
        simp [h2]
        have h2 : n ≤ m := Nat.not_lt.mp h1
        exact Nat.lt_succ_of_le h2
  case abs iht =>
    rw [lift, subst, iht]
  case app iht1 iht2 =>
    rw [lift, subst, iht1, iht2]

theorem lift_swap : m <= n → lift (n + 1) (lift m f) = lift m (lift n f) := by
  induction f generalizing n m
  case var v =>
    simp [lift]
    by_cases h : v < n
    case pos =>
      intro rel
      simp [h]
      by_cases h1 : v < m
      case pos =>
        simp [h1]
        exact Nat.lt_succ_of_lt h
      case neg =>
        simp [h1]
        exact h
    case neg =>
      intro rel
      simp [h]
      by_cases h1 : v < m
      case pos =>
        exfalso
        have h2 : v < n := Nat.lt_of_lt_of_le h1 rel
        exact h h2
      case neg =>
        simp [h1, h]
        by_cases h2 : v + 1 < m
        case pos =>
          exfalso
          have h3 : v < m := Nat.lt_of_succ_lt h2
          exact h1 h3
        case neg =>
          exact Nat.le_of_not_gt h2
  case abs iht =>
    intro rel
    simp [lift]
    apply iht
    exact Nat.succ_le_succ rel
  case app iht1 iht2 =>
    intro rel
    simp [lift]
    constructor
    exact iht1 rel
    exact iht2 rel

theorem lift_swap0 : lift (n + 1) (lift 0 f) = lift 0 (lift n f) := by
  apply lift_swap
  exact Nat.zero_le n

theorem subst_lift2 : m <= n → subst (n+1) (lift m e) (lift m f) = lift m (subst n e f) := by
  induction e generalizing n m f
  case var v =>
    intro rel
    simp [lift, subst]
    by_cases h : n = v
    case pos =>
      rw [h] at rel
      have rel' : ¬ (v < m) := Nat.not_lt_of_le rel
      simp [rel', h]
    case neg =>
      simp [h]
      by_cases h1 : v < m
      case pos =>
        simp [h1]
        have rel' : (v < n) := Nat.lt_of_lt_of_le h1 rel
        by_cases h2 : n + 1 = v
        case pos =>
          exfalso
          sorry
        case neg =>
          simp [h2]
          by_cases h3 : n + 1 < v
          case pos =>
            simp [h3]
            have h4 : n < v := Nat.lt_of_le_of_lt (Nat.le_succ n) h3
            simp [h4]
            sorry
          case neg =>
            simp [h3]
            have hnv : ¬ (n < v) := Nat.not_lt_of_gt rel'
            simp [hnv]
            sorry
      case neg =>
        simp [h1, h]
        by_cases h2 : n < v
        case pos =>
          simp [h2]
          sorry
        case neg =>
          simp [h2]
          sorry
  case app e₁ e₂ iht1 iht2 =>
    intro rel
    simp [lift, subst, iht1 rel, iht2 rel]
  case abs e iht =>
    intro rel
    simp [lift, lift0, subst]
    have rel' : m + 1 ≤ n + 1 := Nat.succ_le_succ rel
    -- simp [iht rel']
    have iht := @iht (m + 1) (n + 1) (lift 0 f) rel'
    have foo := @lift_swap0 m f
    rw [foo] at iht
    exact iht

theorem subst_lift20 : subst (n+1) (lift 0 e) (lift 0 f) = lift 0 (subst n e f) := by
  apply subst_lift2
  exact Nat.zero_le n

theorem ifSkiReducesThenLambdaReduces :
  ∀ e₁ e₂, reduceSKI e₁ e₂ → reduceLambdaMulti (skiToLambda2 e₁) (skiToLambda2 e₂) := by
  intro e₁ e₂ h
  cases h
  case closed cl h =>
    induction h
    case S =>
      simp [skiToLambda2]
      apply reduceLambdaMulti.step
      apply reduceLambda.app1
      apply reduceLambda.app1
      apply reduceLambda.beta
      simp [subst0, subst, lift0]
      apply reduceLambdaMulti.step
      apply reduceLambda.app1
      apply reduceLambda.beta
      simp [subst0, subst, lift0]
      apply reduceLambdaMulti.step
      apply reduceLambda.beta
      simp [subst0, subst]
      rw [subst_lift]
      rw [subst_lift20]
      rw [subst_lift]
      rw [subst_lift]
      apply reduceLambdaMulti.refl
    case K =>
      simp [skiToLambda2]
      apply reduceLambdaMulti.step
      apply reduceLambda.app1
      apply reduceLambda.beta
      simp [subst0, subst, lift0]
      apply reduceLambdaMulti.step
      apply reduceLambda.beta
      simp [subst0]
      rw [subst_lift]
      apply reduceLambdaMulti.refl
    case I =>
      simp [skiToLambda2]
      apply reduceLambdaMulti.step
      apply reduceLambda.beta
      simp [subst0, subst]
      apply reduceLambdaMulti.refl
    case app1 e₁ e₁' e₂ h ih =>
      simp [skiToLambda2]
      cases cl
      case app cl1 cl2 =>
        apply reduceLambdaMultiApp1
        exact ih cl1
    case app2 e₁ e₂ e₂' h ih =>
      simp [skiToLambda2]
      cases cl
      case app cl1 cl2 =>
        apply reduceLambdaMultiApp2
        exact ih cl2

theorem helper :
  reduceSKIMulti (starAbstraction (Lambda.app (Lambda.abs e₁) e₂)) (starAbstraction (subst0 e₁ e₂)) := by
  simp [starAbstraction]
  sorry

theorem reducedSkiIsClosed : ∀ e₁ e₂, reduceSKI e₁ e₂ → closedSKI e₂ := by
  intros e₁ e₂ h
  cases h
  case closed cl hlp =>
    induction hlp
    case S e1 e2 e3 =>
      cases cl
      case app cl1 cl2 =>
        cases cl1
        case app cl11 cl12 =>
          cases cl11
          case app cl111 cl112 =>
            apply closedSKI.app
            apply closedSKI.app
            exact cl112
            exact cl2
            apply closedSKI.app
            exact cl12
            exact cl2
    case K e1 e2 =>
      cases cl
      case app cl1 cl2 =>
        cases cl1
        case app cl11 cl12 =>
          exact cl12
    case I e =>
      cases cl
      case app cl1 cl2 =>
        exact cl2
    case app1 e1 e1' e2 h ih =>
      cases cl
      case app cl1 cl2 =>
        apply closedSKI.app
        exact ih cl1
        exact cl2
    case app2 e1 e2 e2' h ih =>
      cases cl
      case app cl1 cl2 =>
        apply closedSKI.app
        exact cl1
        exact ih cl2

theorem reduceSKIAbstract : ∀ e₁ e₂, reduceSKI e₁ e₂ → reduceSKI (abstract e₁) (abstract e₂) := by
  intros e₁ e₂ h
  cases h
  case closed cl h =>
    have cl' := closedSkiAbstract e₁ cl
    have cl'' := closedSkiAbstract e₂ (reducedSkiIsClosed e₁ e₂ (reduceSKI.closed cl h))
    rw [cl', cl'']
    apply reduceSKIApp2
    constructor
    constructor
    exact cl
    exact h

theorem reduceSKIMultiAbstract : ∀ e₁ e₂, reduceSKIMulti e₁ e₂ → reduceSKIMulti (abstract e₁) (abstract e₂) := by
  intros e₁ e₂ h
  induction h
  case refl =>
    apply reduceSKIMulti.refl
  case step e₁' e₂' e red h1 ih =>

    -- apply reduceSKI.app1
    -- apply reduceSKI.app1
    sorry

theorem ifLambdaReducesThenSkiReduces :
  ∀ e₁ e₂, reduceClosedLambda e₁ e₂ → reduceSKIMulti (starAbstraction e₁) (starAbstraction e₂) := by
  intro e₁
  induction e₁
  case var v =>
    intro e₂ h
    cases h
  case app e₁ e₂ h₁ h₂ =>
    intro e₂ h
    cases h
    case beta e clo =>
      apply helper
    case app1 e red =>
      simp [starAbstraction]
      apply reduceSKIMultiApp1
      exact h₁ e red
    case app2 e red =>
      simp [starAbstraction]
      apply reduceSKIMultiApp2
      exact h₂ e red
  case abs e₁ h₁ =>
    intro e₂ red
    cases red
    case abs e red =>
      have ih := h₁ e red
      simp [starAbstraction]
      apply reduceSKIMultiAbstract
      exact ih

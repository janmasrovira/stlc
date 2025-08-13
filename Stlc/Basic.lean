import Init.Prelude
import Stlc.Prelude

inductive Ty : Type where
  | Fn : Ty → Ty → Ty
  | Nat : Ty

variable {ty : Ty}

infixr:0 " ⟶ " => Ty.Fn

abbrev interp : Ty → Type := fun
 | .Nat => Nat
 | .Fn l r => interp l → interp r

notation "⟦" t "⟧" => interp t

abbrev Context : Type := List Ty

namespace Context

@[simp]
def cons (ty : Ty) (ctx : Context) : Context := List.cons ty ctx

infixr:67 " ▹ " => cons

@[simp]
def get (ctx : Context) (ix : Fin ctx.length) : Ty :=
  let ⟨m, p⟩ := ix
  match m, ctx with
  | .zero, .cons x _ => x
  | .succ k, .cons _ xs => get xs ⟨k, by simp at p; omega⟩

def get_congr {ctx ctx' : Context} (ectx : ctx = ctx') (ix : Fin ctx.length) :
  ctx.get ix = ctx'.get ⟨ix.val, by cases ectx; exact ix.isLt⟩ := by
  cases ectx; rfl

def get_succ {ty : Ty} (ctx : Context) (ix : Nat) (prf : ix < ctx.length) :
  (ty ▹ ctx).get ⟨ix.succ, by simp; omega⟩ = ctx.get ⟨ix, prf⟩ := by rfl

def get_concat_l
  (Δ Γ : Context)
  {ix : Nat}
  (p : ix < Δ.length)
  : (Δ ++ Γ).get ⟨ix, by simp; omega⟩ = Δ.get ⟨ix, p⟩ :=
  by
  induction Δ generalizing ix
  case nil => contradiction
  case cons ih =>
   simp
   cases ix
   case zero => simp
   case succ i => apply ih

def get_concat_r
  (ix : Nat)
  (Δ Γ : Context)
  (ty : Ty)
  (p : Δ.length <= ix)
  (u : ix < Δ.length + Γ.length)
  : (Δ ++ (ty ▹ Γ)).get ⟨ix.succ, by simp; omega⟩ = (Δ ++ Γ).get ⟨ix, by simp; omega⟩ :=
  by
  induction Δ generalizing ix
  case nil => rfl
  case cons n' t Δ' ih =>
    let .succ ix' := ix
    simp at u
    simp at p
    apply ih ix' (by assumption) (by omega)

theorem Fin.fun_eq_of_val {n : Nat} {Res : Type} (f : Fin n → Res) (i j : Fin n) (e : i.val = j.val) : f i = f j := by
  have Eq.rfl := Fin.eq_of_val_eq e
  subst_eqs
  exact rfl

def get_concat_r2
  (ix : Nat)
  (Δ Ε Γ : Context)
  (p : Δ.length <= ix)
  (u : ix < Γ.length + Δ.length)
  : (Δ ++ Ε ++ Γ).get ⟨ix + Ε.length, by simp; omega⟩ = (Δ ++ Γ).get ⟨ix, by simp; omega⟩ :=
  by
  induction Δ generalizing ix
  case nil =>
    induction Ε
    case nil => simp
    case cons eh el ih => simp at ih; simpa
  case cons t Δ' ih =>
    let .succ ix' := ix
    simp at u; simp at p; simp
    replace ih := ih ix' (by assumption) (by omega)
    have lem : get (t :: (Δ' ++ Ε ++ Γ)) ⟨ix' + 1 + List.length Ε, by simp; omega⟩ =
               get (t :: (Δ' ++ Ε ++ Γ)) ⟨ix' + (List.length Ε).succ, by simp; omega⟩
        := by apply Fin.fun_eq_of_val; simp; omega
    simpa [lem]

def get_concat_m
  (Δ Γ : Context)
  (ty : Ty)
  : (Δ ++ (ty ▹ Γ)).get ⟨Δ.length, by simp⟩ = ty :=
  by
  induction Δ
  case nil => rfl
  case cons Δ' ih => apply ih

end Context

structure Var (Γ : Context) (ty : Ty) : Type where
  ix : Fin Γ.length
  tyProof : Γ.get ix = ty := by rfl

inductive Expr : (Γ : Context) → Ty → Type where
  | lam
    {Γ : Context}
    {varTy : Ty}
    {bodyTy : Ty}
    (body : Expr (varTy ▹ Γ) bodyTy)
    : Expr Γ (varTy ⟶ bodyTy)
  | var
    {Γ : Context}
    {ty : Ty}
    (var : Var Γ ty)
    : Expr Γ ty
  | app
    {Γ : Context}
    {l r : Ty}
    (fn : Expr Γ (l ⟶ r))
    (arg : Expr Γ l)
    : Expr Γ r
  | zero
    {Γ : Context}
    : Expr Γ (.Nat)
  | suc
    {Γ : Context}
    (num : Expr Γ .Nat)
    : Expr Γ .Nat
  -- | prec
  --   {Γ : Context n}
  --   {ty : Ty}
  --   (z : Expr Γ ty)
  --   (s : Expr Γ (.Nat ⟶ ty ⟶ ty))
  --   (m : Expr Γ .Nat)
  --   : Expr Γ ty

mutual

inductive Val : Ty → Type where
  | nat : Nat → Val .Nat
  | closure
    {Γ : Context}
    (env : Env Γ)
    {varTy retTy : Ty}
    (body : Expr (varTy ▹ Γ) retTy)
    : Val (varTy ⟶ retTy)

inductive Env : (Γ : Context) → Type where
  | nil : Env .nil
  | cons
    {Γ : Context}
    {ty : Ty}
    (val : Val ty)
    (env : Env Γ)
    : Env (ty ▹ Γ)

end

def Val.interpNat : Val .Nat → Nat := fun
  | .nat n => n

def Env.get
  {ty : Ty}
  (env : Env Γ)
  (var : Var Γ ty)
  : Val ty :=
  let ⟨⟨ix, l⟩, p⟩ := var
  match ix, env with
  | 0, (.cons v _) => p ▸ v
  | .succ m, (.cons _ env) => env.get ⟨⟨m, Nat.succ_lt_succ_iff.mp l⟩, by simpa using p⟩

@[reducible]
def Expr.size (expr :  Expr Γ t) : Nat := match expr with
  | .zero => 1
  | .suc e => e.size.succ
  | .app l r => l.size + r.size |>.succ
  | .var _ => 1
  | .lam l => l.size.succ

mutual
def Val.size (val : Val t) : Nat := match val with
  | .nat _ => 1
  | .closure cenv cbody => cenv.size + cbody.size

def Env.size (env : Env Γ) : Nat := match env with
  | .nil => 0
  | .cons v e => v.size + e.size
end

def Expr.weaken
  {ty : Ty}
  {Δ Ε Γ : Context}
  (e : Expr (Δ ++ Γ) ty)
  : Expr (Δ ++ Ε ++ Γ) ty := match e with
  | .zero => .zero
  | .suc n => .suc n.weaken
  | .app l r => .app l.weaken r.weaken
  | .lam (varTy := vt) (bodyTy := bodyTy) b => .lam (b.weaken (Δ := vt ▹ Δ) (Γ := Γ))
  | .var ⟨⟨k, u⟩, p⟩ => by
        apply Expr.var
        by_cases cmp : k < Δ.length
        case pos =>
          refine ⟨⟨k, by simp; omega⟩, ?_⟩
          rw [Context.get_congr (List.append_assoc Δ Ε Γ) ⟨k, by simp; omega⟩]
          rw [Context.get_concat_l Δ (Ε ++ Γ) (by simp; omega)]
          rw [Context.get_concat_l (p := cmp )] at p
          assumption
        case neg =>
          have cmp : Δ.length <= k := by omega
          simp at u
          refine ⟨⟨k + Ε.length, by simp; omega⟩, ?_⟩
          rw [Context.get_concat_r2 k Δ Ε Γ]
          assumption
          assumption
          omega

def Expr.substH
  {l r : Ty}
  {Δ Γ : Context}
  (fn : Expr (Δ ++ (l ▹ Γ)) r)
  (arg : Expr Γ l)
  : Expr (Δ ++ Γ) r := match fn with
  | .zero => .zero
  | .suc n => n.substH arg
  | .app f x => .app (f.substH arg) (x.substH arg)
  | .lam (varTy := varTy) (bodyTy := bodyTy) body => .lam (body.substH (Δ := varTy ▹ Δ) arg)
  | .var var@⟨⟨k, u⟩, p⟩ => by
    by_cases h : k < Δ.length
    case pos =>
      have h1 := Context.get_concat_l Δ Γ h
      have h2 := Context.get_concat_l Δ (l ▹ Γ) h
      refine (.var ⟨⟨k , by simp; omega⟩ , ?_⟩)
      rw [h1, ←h2, p]
    case neg =>
      by_cases h2 : k = Δ.length
      case pos =>
        subst h2
        have h1 := Context.get_concat_m Δ Γ l
        rw [p] at h1
        rw [h1]
        exact (arg.weaken (Δ := .nil))
      case neg =>
        have h1 : k > Δ.length := by omega
        let .succ ks := k
        simp at u
        refine (.var ⟨⟨ks, by simp; omega⟩, ?_⟩)
        rw [← Context.get_concat_r ks Δ Γ l (by omega) (by omega)]
        assumption

def Expr.subst
  {l r : Ty}
  {Γ : Context}
  (fn : Expr (l ▹ Γ) r)
  (arg : Expr Γ l)
  : Expr Γ r := Expr.substH (Δ := .nil) fn arg

inductive IsValue : {Γ : Context} → {ty : Ty} → (e : Expr Γ ty) → Prop where
  | zero : IsValue .zero
  | suc {n : Expr Γ .Nat} : IsValue n → IsValue (.suc n)
  | lam {l r : Ty} {body : Expr (l ▹ Γ) r} : IsValue body → IsValue (.lam body)

def Expr.isValue {Γ : Context} {ty : Ty} (e : Expr Γ ty) : Decidable (IsValue e) :=
  match e with
  | .var .. => isFalse (by intro x; cases x)
  | .app .. => isFalse (by intro x; cases x)
  | .zero => isTrue .zero
  | .suc n => match n.isValue with
              | isFalse p => isFalse (by intro x; cases x; contradiction)
              | isTrue p => isTrue (.suc p)
  | .lam b => match b.isValue with
              | isFalse p => isFalse (by intro x; cases x; contradiction)
              | isTrue p => isTrue (.lam p)

-- exactly 1 β-reduction step
inductive βstep : {Γ : Context} → {ty : Ty} → (e1 e2 : Expr Γ ty) → Prop where
  | βreduction {Γ : Context} {l r : Ty} (body : Expr (l ▹ Γ) r) (arg : Expr Γ l) : βstep (.app (.lam body) arg) (body.subst arg)
  | suc {Γ : Context} (n n' : Expr Γ .Nat) : βstep n n' → βstep n.suc n'.suc
  | appl {Γ : Context} {l r : Ty} (fn fn' : Expr Γ (l ⟶ r)) (arg : Expr Γ l) : βstep fn fn' → βstep (.app fn arg) (.app fn' arg)
  | appr {Γ : Context} {l r : Ty} (fn : Expr Γ (l ⟶ r)) {arg arg' : Expr Γ l} : βstep arg arg' → βstep (.app fn arg) (.app fn arg')
  | lam {Γ : Context} {l : Ty} {body body' : Expr (l ▹ Γ) r} : βstep body body' → βstep (.lam body) (.lam body')

-- zero or more β-reduction steps
inductive βsteps {Γ : Context} : {ty : Ty} → (e1 e2 : Expr Γ ty) → Prop where
  | rfl {ty : Ty} {a : Expr Γ ty} : βsteps a a
  | cons {ty : Ty} {a b c : Expr Γ ty} : βstep a b → βsteps b c → βsteps a c

theorem βsteps.trans : βsteps a b → βsteps b c → βsteps a c := by
  intro l r; induction l; assumption
  case cons ab bc ih => exact cons ab (ih r)

theorem βsteps.singleton {ty : Ty} {a b : Expr Γ ty} : βstep a b → βsteps a b := by
  intro x; constructor; apply x; constructor

theorem βsteps.lam {l r : Ty} {a b : Expr (l ▹ Γ) r} : βsteps a b → βsteps a.lam b.lam := by
  intro f; induction f; constructor
  case cons t1 t2 t3 => constructor; apply βstep.lam; assumption; assumption

theorem βsteps.appr {l r : Ty} {fn : Expr Γ (l ⟶ r)} {arg arg' : Expr Γ l}
  : βsteps arg arg' → βsteps (.app fn arg) (.app fn arg') := by
  intro f; induction f; constructor
  case cons t1 t2 t3 => constructor; apply βstep.appr; assumption; assumption

theorem βsteps.suc {n n' : Expr Γ .Nat} : βsteps n n' → βsteps n.suc n'.suc := by
  intro f; induction f; constructor
  case cons t1 t2 t3 => constructor; apply βstep.suc; assumption; assumption

-- strong normalization
@[simp]
def Expr.normalize {Γ : Context} {ty : Ty} (e : Expr Γ ty) : Expr Γ ty :=
  match e with
  | .zero => .zero
  | .suc n => .suc n.normalize
  | .lam b => .lam b.normalize
  | .var v => .var v
  | .app l r => match l.normalize with
                | .lam b => b.subst r.normalize
                | _ => .app l r.normalize

theorem βsteps_normalize
  {Γ : Context}
  {ty : Ty}
  (e : Expr Γ ty)
  : βsteps e e.normalize := by
  induction e
  case lam body ih => simp; exact βsteps.lam ih
  case var => constructor
  case zero => constructor
  case suc p => exact βsteps.suc p
  case app fn arg bfn barg =>
    simp
    cases fn.normalize <;> simp
    case var v => apply (βsteps.appr barg)
    case app wut => exact βsteps.appr barg
    case lam body => sorry

theorem progress (e : Expr Γ ty) : IsValue e ∨ ∃ e' : Expr Γ ty, βsteps e e' := sorry

def eval
  {ty : Ty}
  (env : Env Γ)
  (expr : Expr Γ ty)
  : Val ty :=
  match expr with
  | .zero => .nat 0
  | .suc e => let .nat m := eval env e
              .nat (m + 1)
  | .lam body => .closure env body
  | .var v => env.get v
  | .app (l := l) (r := r) (fn : Expr Γ (l ⟶ r)) arg =>
      let arg' := eval env arg
      let .closure clEnv body := eval env fn
      eval (.cons arg' clEnv) body
  termination_by 0
  decreasing_by repeat sorry

def evalTop
  {ty : Ty}
  (expr : Expr .nil ty)
  : Val ty := eval .nil expr

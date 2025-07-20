/- TODO: Define 𝕍 as a lifted version of base 𝕍 with additional effects -/
class Semantics (𝔼 : Type) (𝕊 𝕍 : outParam Type) where
  sem : 𝔼 → 𝕊 → 𝕍

namespace LangT
  inductive 𝔼
    | add (n : Nat)
    | mul (n : Nat)

  declare_syntax_cat exp_t
  syntax ("ADD " <|> "MUL ") term : exp_t
  syntax "T⟪ " exp_t " ⟫" : term
  macro_rules
    | `(T⟪ ADD $n ⟫) => `(𝔼.add $n)
    | `(T⟪ MUL $n ⟫) => `(𝔼.mul $n)

  /- Metaprogramming from the object language T's perspective -/
  #eval T⟪ ADD (42 + 5) ⟫

  inductive 𝕍
    | nat (n : Nat)

  instance : OfNat 𝕍 n where
    ofNat := .nat n

  instance : Coe Nat 𝕍 where
    coe := .nat

  instance : Coe 𝕍 Nat where
    coe := λ (.nat n) => n

  #eval (42 : 𝕍)

  def sem : 𝔼 → 𝕍 → 𝕍
    | .add n, .nat m => n + m
    | .mul n, .nat m => n * m

  instance : Semantics 𝔼 𝕍 𝕍 where
    sem := sem
end LangT

namespace LangS
  inductive 𝔼
    | var
    | nat (n : Nat)
    | add (e₁ e₂ : 𝔼)
    | mul (e₁ e₂ : 𝔼)
    | equal (e₁ e₂ : 𝔼)
    | pair (e₁ e₂ : 𝔼)
    | proj₁ (e : 𝔼)
    | proj₂ (e : 𝔼)
    | ite (eᵢ eₜ eₑ : 𝔼)

  instance : OfNat 𝔼 n where
    ofNat := .nat n

  instance : Coe Nat 𝔼 where
    coe := .nat

  declare_syntax_cat exp_s
  syntax num : exp_s
  syntax ident : exp_s
  syntax:40 exp_s:40 " = " exp_s:41 : exp_s
  syntax:50 exp_s:50 " + " exp_s:51 : exp_s
  syntax:60 exp_s:60 " * " exp_s:61 : exp_s
  syntax "( " exp_s ", " exp_s " )" : exp_s
  syntax "( " exp_s " )" : exp_s
  syntax exp_s (".1" <|> ".2") : exp_s
  syntax "if " "( " exp_s " ) " "then" " { " exp_s " } " "else" " { " exp_s " }" : exp_s
  syntax "S⟪ " exp_s " ⟫" : term
  macro_rules
    | `(S⟪ x ⟫) => `(𝔼.var)
    | `(S⟪ $n:num ⟫) => `(𝔼.nat $n)
    | `(S⟪ $e₁:exp_s + $e₂:exp_s ⟫) => `(𝔼.add S⟪ $e₁ ⟫ S⟪ $e₂ ⟫)
    | `(S⟪ $e₁:exp_s * $e₂:exp_s ⟫) => `(𝔼.mul S⟪ $e₁ ⟫ S⟪ $e₂ ⟫)
    | `(S⟪ $e₁:exp_s = $e₂:exp_s ⟫) => `(𝔼.equal S⟪ $e₁ ⟫ S⟪ $e₂ ⟫)
    | `(S⟪ ($e₁:exp_s, $e₂:exp_s) ⟫) => `(𝔼.pair S⟪ $e₁ ⟫ S⟪ $e₂ ⟫)
    | `(S⟪ ($e:exp_s) ⟫) => `(𝔼.pair S⟪ $e ⟫ S⟪ $e ⟫)
    | `(S⟪ $e:exp_s.1 ⟫) => `(𝔼.proj₁ S⟪ $e ⟫)
    | `(S⟪ $e:exp_s.2 ⟫) => `(𝔼.proj₂ S⟪ $e ⟫)
    | `(S⟪ if ($eᵢ:exp_s) then { $eₜ:exp_s } else { $eₑ:exp_s } ⟫) =>
        `(𝔼.ite S⟪ $eᵢ ⟫ S⟪ $eₜ ⟫ S⟪ $eₑ ⟫)

  inductive 𝕍
    | nat (n : Nat)
    | pair (v₁ v₂ : 𝕍)

  instance : OfNat 𝕍 n where
    ofNat := .nat n

  instance : Coe Nat 𝕍 where
    coe := .nat

  instance : Coe 𝕍 𝕍 where
    coe n := n

  instance [Coe A 𝕍] [Coe B 𝕍] : Coe (A × B) 𝕍 where
    coe := λ (a, b) => .pair a b

  #eval (((1, 2), 3) : 𝕍)


  def sem : 𝔼 → 𝕍 → Option 𝕍
    | .var, v => v
    | .nat n, _ => n
    | .add e₁ e₂, v => do
      let v1 ← sem e₁ v
      let v2 ← sem e₂ v
      match (v1, v2) with
        | (.nat n1, .nat n2) => n1 + n2
        | _ => none
    | .mul e₁ e₂, v => do
      let v1 ← sem e₁ v
      let v2 ← sem e₂ v
      match (v1, v2) with
        | (.nat n1, .nat n2) => n1 * n2
        | _ => none
    | .equal e₁ e₂, v => do
      let v1 ← sem e₁ v
      let v2 ← sem e₂ v
      match (v1, v2) with
        | (.nat n1, .nat n2) => 𝕍.nat (if n1 = n2 then 1 else 0)
        | _ => none
    | .pair e₁ e₂, v => do
      let v1 ← sem e₁ v
      let v2 ← sem e₂ v
      (v1, v2)
    | .proj₁ e, v => do
      let v' ← sem e v
      match v' with
        | .pair v1 _ => v1
        | _ => none
    | .proj₂ e, v => do
      let v' ← sem e v
      match v' with
        | .pair _ v2 => v2
        | _ => none
    | .ite eᵢ eₜ eₑ, v => do
      let p ← sem eᵢ v
      match p with
        | 0 => sem eₑ v
        | _ => sem eₜ v

  instance : Semantics 𝔼 𝕍 (Option 𝕍) where
    sem := sem
end LangS



notation "⟦ " e " ⟧" => Semantics.sem e
macro "⟦ " e:exp_t " ⟧" : term => `(Semantics.sem T⟪ $e ⟫)
macro "⟦ " e:exp_s " ⟧" : term => `(Semantics.sem S⟪ $e ⟫)

def term42 := T⟪ ADD 42 ⟫

#eval ⟦ T⟪ ADD 42 ⟫ ⟧ 10
#eval ⟦ term42 ⟧ 0
#eval ⟦ MUL 2 ⟧ 3

#eval S⟪
  if (x.1.1 = 0) then {
    x.1.2 + x.2
  } else {
    x.1.2 * x.2
  }
⟫
#eval S⟪ x ⟫


def encodeEₜₛ : LangT.𝔼 → LangS.𝕍
  | T⟪ ADD n ⟫ => (0, n)
  | T⟪ MUL n ⟫ => (1, n)

macro "⌈ " e:exp_t " ⌉" : term => `(encodeEₜₛ T⟪ $e ⟫)
macro "⌈ " e:term " ⌉" : term => `(encodeEₜₛ $e)

#eval ⌈ T⟪ ADD 42 ⟫ ⌉
#eval ⌈ MUL 42 ⌉

def encodeVₜₛ : LangT.𝕍 → LangS.𝕍
  | .nat n => n

macro "⌈ " e:term " ⌉" : term => `(encodeVₜₛ $e)

#eval ⌈ 42 ⌉


def Iₛₜ : LangS.𝔼 := S⟪
  if (x.1.1 = 0) then {
    x.1.2 + x.2
  } else {
    x.1.2 * x.2
  }
⟫

#eval if let some v := ⟦ Iₛₜ ⟧ (⌈ T⟪ ADD 3 ⟫ ⌉, ⌈ 4 ⌉)
  then v else 99

#eval if let some v := ⟦ Iₛₜ ⟧ (⌈ T⟪ MUL 3 ⟫ ⌉, ⌈ 4 ⌉)
  then v else 99

theorem Iₛₜ_correctness : ∀ (e : LangT.𝔼) (i : LangT.𝕍), ⟦ Iₛₜ ⟧ (⌈ e ⌉, ⌈ i ⌉) = ⌈⟦ e ⟧ i⌉ := by
  intros e i
  cases e <;> rfl

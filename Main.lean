inductive ExpT where
  | add (n : Nat) : ExpT
  | mul (n : Nat) : ExpT

inductive ExpS where
  | var : ExpS
  | nat (n : Nat) : ExpS
  | add (e1 e2 : ExpS) : ExpS
  | mul (e1 e2 : ExpS) : ExpS
  | equal (e1 e2 : ExpS) : ExpS
  | pair (e1 e2 : ExpS) : ExpS
  | proj1 (e : ExpS) : ExpS
  | proj2 (e : ExpS) : ExpS
  | ite (pred con alt : ExpS) : ExpS

inductive ValT where
  | nat (n : Nat) : ValT

inductive ValS where
  | nat (n : Nat) : ValS
  | pair (v1 v2 : ValS) : ValS

def encodeTS : ExpT → ValS
  | ExpT.add n => ValS.pair (ValS.nat 0) (ValS.nat n)
  | ExpT.mul n => ValS.pair (ValS.nat 1) (ValS.nat n)

Require Export ZArith.
Require Export Znumtheory.
Require Export Zpow_facts.

(* Theorem 70 *)
Theorem theorem_70 : forall p : Z, prime p -> forall a : Z, a^p mod p = a mod p.
Proof.
Abort.

(* Theorem 71 *)
Theorem fermats_theorem : forall a p : Z, prime p /\ ~(p|a) -> a^(p-1) mod p = 1.
Proof.
Abort.

(* Theorem 72 : a^phi(m) mod m = 1 *)



  

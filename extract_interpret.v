Require Export little.
Require Export denot.
Require Export axiom.
Require Export abstract_i.

Extract Constant Tarski_fix => "let rec fix f = f (fun y -> fix f y) in fix".

Extract Constant excluded_middle_informative => "Left".

Extract Constant constructive_indefinite_description =>
   "fun a -> failwith ""constructive_indefinite_description not provided""".

(* Zopp is used in the parser. *)

Extraction "interp.ml" Z.opp denot.denot ax ab.
